/*@flow*/
'use strict';

const raw = module.exports.raw = (buf /*:Buffer*/) => {
    // Checksum pairs.
    let state = 0;
    let hbit = 0;
    const add = (num) => {
        state += num;
        if (state > 0x7fffffff) {
            hbit ^= 1;
            state &= 0x7fffffff;
        }
    };

    for (let i = 0; i < buf.length - 1; i += 2) {
        add(buf.readUInt16LE(i));
    }

    // Do the odd byte if there is one.
    if (buf.length % 2) {
        add(buf[buf.length - 1]);
    }

    state |= hbit << 31;

    while (state < 0 || state > 0xFFFF) {
        state = (state >>> 16) + (state & 0xFFFF);
    }

    // Unconditional flip because node only runs on little endian machines
    state = ((state << 8) & 0xffff) | (state >>> 8);

    return state ^ 0xffff;
};

const udp4 = module.exports.udp4 = (
    srcIp /*:Buffer*/,
    dstIp /*:Buffer*/,
    srcPort /*:Buffer|number*/,
    dstPort /*:Buffer|number*/,
    content /*:Buffer*/) =>
{
    if (!Buffer.isBuffer(srcIp) || srcIp.length !== 4) {
        throw new Error("srcIp must be a 4 byte buffer");
    }
    if (!Buffer.isBuffer(dstIp) || dstIp.length !== 4) {
        throw new Error("dstIp must be a 4 byte buffer");
    }
    if (typeof(srcPort) === 'number') {
        if (srcPort < 0 || srcPort > 65535) { throw new Error("srcPort out of range"); }
        const _srcPort = new Buffer(2);
        _srcPort.writeUInt16BE(srcPort, 0);
        srcPort = _srcPort;
    }
    if (typeof(dstPort) === 'number') {
        if (dstPort < 0 || dstPort > 65535) { throw new Error("dstPort out of range"); }
        const _dstPort = new Buffer(2);
        _dstPort.writeUInt16BE(dstPort, 0);
        dstPort = _dstPort;
    }
    if (!Buffer.isBuffer(srcPort) || srcPort.length !== 2) {
        throw new Error("srcPort must be a 2 byte buffer or a number between 0 and 65535");
    }
    if (!Buffer.isBuffer(dstPort) || dstPort.length !== 2) {
        throw new Error("dstPort must be a 2 byte buffer or a number between 0 and 65535");
    }
    // length includes the length of the udp header...
    if ((8 + content.length) > 65535) {
        throw new Error("it is impossible to make a UDP packet of length > 65535");
    }
    const length = new Buffer(2);
    length.writeUInt16BE(8 + content.length, 0);
    const pseudo = Buffer.concat([
        srcIp, dstIp, new Buffer([0, 17]), length,
        srcPort, dstPort, length, new Buffer([0, 0]),
        content
    ]);
    return raw(pseudo);
};