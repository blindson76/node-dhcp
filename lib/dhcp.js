/**
 * @license DHCP.js v0.2.20 28/06/2017
 * http://www.xarg.org/2017/06/a-pure-javascript-dhcp-implementation/
 *
 * Copyright (c) 2017, Robert Eisele (robert@xarg.org)
 * Dual licensed under the MIT or GPL Version 2 licenses.
 **/

const util = require('util');
const dgram = require('dgram');
const os = require('os');
const EventEmitter = require('events').EventEmitter;
const pcap = require('pcap');
const raw = require('./checksum.js');
const SeqBuffer = require('./seqbuffer.js');
const Options = require('./options.js');
const Protocol = require('./protocol.js');
const Tools = require('./tools.js');
const { nextTick } = require('process');

const DHCPDISCOVER = 1;
const DHCPOFFER = 2;
const DHCPREQUEST = 3;
const DHCPDECLINE = 4;
const DHCPACK = 5;
const DHCPNAK = 6;
const DHCPRELEASE = 7;
const DHCPINFORM = 8;

const SERVER_PORT = 67;
const CLIENT_PORT = 68;

const INADDR_ANY = '0.0.0.0';
const INADDR_BROADCAST = '255.255.255.255';

const BOOTREQUEST = 1;
const BOOTREPLY = 2;



function Lease() {

}

Lease.prototype = {
  bindTime: null, // Time when we got an ACK
  leasePeriod: 86400, // Seconds the lease is allowed to live, next lease in "leasePeriod - (now - bindTime)"
  renewPeriod: 1440, // Seconds till a renew is due, next renew in "renewPeriod - (now - bindTime)"
  rebindPeriod: 14400, // Seconds till a rebind is due, next rebind in "rebindPeriod - (now - bindTime)"
  state: null, // Current State, like BOUND, INIT, REBOOTING, ...
  server: null, // The server we got our config from
  address: null, // actual IP address we got
  options: null, // object of all other options we got
  tries: 0, // number of tries in order to complete a state
  xid: 1 // unique id, incremented with every request
};


function Server(config, listenOnly) {

  EventEmitter.call(this);

  const self = this;
  const capSession = pcap.createSession(config.if, { promiscuous: true, filter: "udp and ( port 67)" });

  this._conf = config;
  this._state = {};
  this._capSession = capSession;
  this.listenOnly = listenOnly
}

Server.prototype = {


  // Config (cache) object
  _conf: null,

  // All mac -> IP mappings, we currently have assigned or blacklisted
  _state: null,

  // Incoming request
  _req: null,

  config: function (key) {

    let val;
    const optId = Options.conf[key];

    // If config setting is set by user
    if (undefined !== this._conf[key]) {
      val = this._conf[key];
    } else if (undefined !== Options.opts[optId]) {
      val = Options.opts[optId].default;
      if (val === undefined)
        return 0; // Better idea?
    } else {
      return null
      throw new Error('Invalid option ' + key);
    }

    // If a function was provided
    if (val instanceof Function) {
      var reqOpt = {};
      for (var i in this._req.options) {
        var opt = Options.opts[i];
        if (opt.enum) {
          reqOpt[opt.attr || i] = opt.enum[this._req.options[i]];
        } else {
          reqOpt[opt.attr || i] = this._req.options[i];
        }
      }
      val = val.call(this, reqOpt);
    }

    // If the option has an "enum" attribute:
    if (key !== 'range' && key !== 'static' && key !== 'randomIP' && Options.opts[optId].enum) {
      const values = Options.opts[optId].enum;

      // Check if value is an actual enum string
      for (let i in values) {
        if (values[i] === val) {
          return parseInt(i, 10);
        }
      }

      // Okay, check  if it is the numeral value of the enum
      if (values[val] === undefined) {
        throw new Error('Provided enum value for ' + key + ' is not valid');
      } else {
        val = parseInt(val, 10);
      }
    }
    return val;
  },
  _getOptions: function (pre, required, requested) {

    for (let req of required) {

      // Check if option id actually exists
      if (Options.opts[req] !== undefined) {

        // Take the first config value always
        if (pre[req] === undefined) {
          pre[req] = this.config(Options.opts[req].config);
        }

        if (!pre[req]) {
          throw new Error('Required option ' + Options.opts[req].config + ' does not have a value set');
        }

      } else {
        this.emit('error', 'Unknown option ' + req);
      }
    }

    // Add all values, the user wants, which are not already provided:
    if (requested) {

      for (let req of requested) {

        // Check if option id actually exists
        if (Options.opts[req] !== undefined) {

          // Take the first config value always
          if (pre[req] === undefined) {
            const val = this.config(Options.opts[req].config);
            // Add value only, if it's meaningful
            if (val) {
              pre[req] = val;
            }
          }

        } else {
          this.emit('error', 'Unknown option ' + req);
        }
      }
    }

    // Finally Add all missing and forced options
    const forceOptions = this._conf.forceOptions;
    if (forceOptions instanceof Array) {
      for (let option of forceOptions) {

        // Add numeric options right away and look up alias names
        let id;
        if (isNaN(option)) {
          id = Options.conf[option];
        } else {
          id = option;
        }

        // Add option if it is valid and not present yet
        if (id !== undefined && pre[id] === undefined) {
          pre[id] = this.config(option);
        }
      }
    }
    return pre;
  },

  _selectAddress: function (clientMAC, req) {

    /*
     * IP Selection algorithm:
     *
     * 0. Is Mac already known, send same IP of known lease
     *
     * 1. Is there a wish for static binding?
     *
     * 2. Are all available IP's occupied?
     *    - Send release to oldest lease and reuse
     *
     * 3. is config randomIP?
     *    - Select random IP of range, until no occupied slot is found
     *
     * 4. Take first unmapped IP of range
     *
     * TODO:
     * - Incorporate user preference, sent to us
     * - Check APR if IP exists on net
     */


    // If existing lease for a mac address is present, re-use the IP
    if (this._state[clientMAC] && this._state[clientMAC].address) {
      return this._state[clientMAC].address;
    }



    // Is there a static binding?
    const _static = this.config('static');
    if (typeof _static === "function") {
      const staticResult = _static(clientMAC, req);
      if (staticResult)
        return staticResult;
    } else if (_static[clientMAC]) {
      return _static[clientMAC];
    }


    const randIP = this.config('randomIP');
    const _tmp = this.config('range');
    const firstIP = Tools.parseIp(_tmp[0]);
    const lastIP = Tools.parseIp(_tmp[1]);



    // Add all known addresses and save the oldest lease
    const ips = [this.config('server')]; // Exclude our own server IP from pool
    let oldestMac = null;
    let oldestTime = Infinity;
    let leases = 0;
    for (let mac in this._state) {
      if (this._state[mac].address)
        ips.push(this._state[mac].address);

      if (this._state[mac].leaseTime < oldestTime) {
        oldestTime = this._state[mac].leaseTime;
        oldestMac = mac;
      }
      leases++;
    }




    // Check if all IP's are used and delete the oldest
    if (oldestMac !== null && lastIP - firstIP === leases) {
      const ip = this._state[oldestMac].address;

      // TODO: Notify deleted client
      delete this._state[oldestMac];

      return ip;
    }




    // Select a random IP, maybe not the best algorithm for quick selection if lots of ip's are given: TODO
    if (randIP) {

      while (1) {

        const ip = Tools.formatIp(firstIP + Math.random() * (lastIP - firstIP) | 0);

        if (ips.indexOf(ip) === -1) {
          return ip;
        }
      }
    }



    // Choose first free IP in subnet
    for (let i = firstIP; i <= lastIP; i++) {

      const ip = Tools.formatIp(i);

      if (ips.indexOf(ip) === -1) {
        return ip;
      }
    }
  },

  handleDiscover: function (req) {
    //console.log('Handle Discover', req);

    const lease = this._state[req.chaddr] = this._state[req.chaddr] || new Lease;
    lease.address = this._selectAddress(req.chaddr, req);
    lease.leasePeriod = this.config('leaseTime');
    lease.server = this.config('server');
    lease.state = 'OFFERED';

    this.sendOffer(req);
  },
  sendOffer: function (req) {

    //console.log('Send Offer');

    // Formulate the response object
    const ans = {
      op: BOOTREPLY,
      htype: 1, // RFC1700, hardware types: 1=Ethernet, 2=Experimental, 3=AX25, 4=ProNET Token Ring, 5=Chaos, 6=Tokenring, 7=Arcnet, 8=FDDI, 9=Lanstar (keep it constant)
      hlen: 6, // Mac addresses are 6 byte
      hops: 0,
      xid: req.xid, // 'xid' from client DHCPDISCOVER message
      secs: 0,
      flags: req.flags,
      ciaddr: INADDR_ANY,
      yiaddr: this._selectAddress(req.chaddr), // My offer
      siaddr: this.config('server'), // next server in bootstrap. That's us
      giaddr: req.giaddr,
      chaddr: req.chaddr, // Client mac address
      sname: '',
      file: '',
      options: this._getOptions({
        53: DHCPOFFER
      }, [
        1, 3, 51, 54, 6
      ], req.options[55])
    };

    // Send the actual data
    // INADDR_BROADCAST : 68 <- SERVER_IP : 67
    this._send(this.config('broadcast'), ans);

  },

  handleRequest: function (req) {
    //console.log('Handle Request', req);

    const lease = this._state[req.chaddr] = this._state[req.chaddr] || new Lease;
    lease.address = this._selectAddress(req.chaddr);
    lease.leasePeriod = this.config('leaseTime');
    lease.server = this.config('server');
    lease.state = 'BOUND';
    lease.bindTime = new Date;

    this.sendAck(req);
  },
  sendAck: function (req) {
    //console.log('Send ACK');
    // Formulate the response object
    const ans = {
      op: BOOTREPLY,
      htype: 1, // RFC1700, hardware types: 1=Ethernet, 2=Experimental, 3=AX25, 4=ProNET Token Ring, 5=Chaos, 6=Tokenring, 7=Arcnet, 8=FDDI, 9=Lanstar (keep it constant)
      hlen: 6, // Mac addresses are 6 byte
      hops: 0,
      xid: req.xid, // 'xid' from client DHCPREQUEST message
      secs: 0,
      flags: req.flags, // 'flags' from client DHCPREQUEST message
      ciaddr: req.ciaddr,
      yiaddr: this._selectAddress(req.chaddr), // my offer
      siaddr: this.config('server'), // server ip, that's us
      giaddr: req.giaddr, // 'giaddr' from client DHCPREQUEST message
      chaddr: req.chaddr, // 'chaddr' from client DHCPREQUEST message
      sname: '',
      file: '',
      options: this._getOptions({
        53: DHCPACK
      }, [
        1, 3, 51, 54, 6
      ], req.options[55])
    };

    this.emit('bound', this._state);

    // Send the actual data
    // INADDR_BROADCAST : 68 <- SERVER_IP : 67
    this._send(this.config('broadcast'), ans);
  },
  sendNak: function (req) {
    //console.log('Send NAK');
    // Formulate the response object
    const ans = {
      op: BOOTREPLY,
      htype: 1, // RFC1700, hardware types: 1=Ethernet, 2=Experimental, 3=AX25, 4=ProNET Token Ring, 5=Chaos, 6=Tokenring, 7=Arcnet, 8=FDDI, 9=Lanstar (keep it constant)
      hlen: 6, // Mac addresses are 6 byte
      hops: 0,
      xid: req.xid, // 'xid' from client DHCPREQUEST message
      secs: 0,
      flags: req.flags, // 'flags' from client DHCPREQUEST message
      ciaddr: INADDR_ANY,
      yiaddr: INADDR_ANY,
      siaddr: INADDR_ANY,
      giaddr: req.giaddr, // 'giaddr' from client DHCPREQUEST message
      chaddr: req.chaddr, // 'chaddr' from client DHCPREQUEST message
      sname: '', // unused
      file: '', // unused
      options: this._getOptions({
        53: DHCPNAK
      }, [
        54
      ])
    };

    // Send the actual data
    this._send(this.config('broadcast'), ans);
  },

  handleRelease: function () {

  },

  handleRenew: function () {
    // Send ack
  },

  listen: function (port, host, fn) {

    const self = this;
    this._capSession.on('packet', function (rawPacket) {

      const buf = pcap.decode(rawPacket).payload.payload.payload.data
      let req;

      try {
        req = Protocol.parse(buf);
      } catch (e) {
        self.emit('error', e);
        return;
      }

      self._req = req;

      if (req.op !== BOOTREQUEST) {
        self.emit('error', new Error('Malformed packet'), req);
        return;
      }

      if (!req.options[53]) {
        self.emit('error', new Error('Got message, without valid message type'), req);
        return;
      }

      self.emit('message', req);

      if (!self.listenOnly) {
        // Handle request
        switch (req.options[53]) {
          case DHCPDISCOVER: // 1.
            self.handleDiscover(req);
            break;
          case DHCPREQUEST: // 3.
            self.handleRequest(req);
            break;
          default:
            console.error("Not implemented method", req.options[53]);
        }
      }
    });

    if (fn instanceof Function) {
      nextTick(fn)
    }
    this.emit('listening')
  },

  close: function (callback) {
    this._capSession.close(callback)
  },

  _send: function (host, data) {

    const sb = Protocol.format(data);
    const buff = sb._data.slice(0, sb._w)
    const eth = Buffer.from([
      //eth
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, //dst
      0x52, 0x66, 0x00, 0x41, 0x55, 0x01,  //src
      0x08, 0x00, //type

      //ipv4
      0x45, 0x00, //hdr
      0x00, 0x00, //length udp+8+20,
      0x00, 0x00, //ident
      0x00, //flags
      0x00, 0x40, //ttl = 64,
      0x11, //proto=udp,
      0x00, 0x00, //header checksum,
      10, 10, 11, 1, //src addr
      255, 255, 255, 255, //dst addr

      //udp
      0x00, 67, //src port,
      0x00, 68, //dst port
      0x00, 0x00, //data length = udp+8
      0x00, 0x00, //checksum
      ...buff
    ])
    const checksum = raw.udp4(
      eth.slice(26, 30),
      eth.slice(30, 34),
      eth.slice(34, 36),
      eth.slice(36, 38),
      buff
    )
    eth.writeUInt16BE(buff.length + 8 + 20, 16)
    eth.writeUInt16BE(buff.length + 8, 38)
    eth.writeUInt16BE(checksum, 40)

    eth.writeUInt16BE(raw.raw(eth.slice(14, 34)), 24)
    try {
      this._capSession.inject(eth)
    } catch (e) {
      this.emit('error', e)
    }
  }

};









util.inherits(Server, EventEmitter);

exports.DHCP = exports.default = module.exports = {
  createServer: function (opt) {
    return new Server(opt);
  },
  createBroadcastHandler: function () {
    return new Server(null, true);
  },
  addOption: Options.addOption,
  DHCPDISCOVER: DHCPDISCOVER,
  DHCPOFFER: DHCPOFFER,
  DHCPREQUEST: DHCPREQUEST,
  DHCPDECLINE: DHCPDECLINE,
  DHCPACK: DHCPACK,
  DHCPNAK: DHCPNAK,
  DHCPRELEASE: DHCPRELEASE,
  DHCPINFORM: DHCPINFORM
};
