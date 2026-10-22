#ifndef __EMP_BITIO_H__
#define __EMP_BITIO_H__
#include "emp-tool/emp-tool.h"

namespace emp {
using namespace std;
// Bit-level IOChannel adapter for emp-zk-bool. Wraps an inner IOChannel and
// buffers single bits (send_bit / recv_bit), flushing them packed 8-per-byte
// through the inner channel's send_bool / recv_bool. The Fiat-Shamir
// transcript lives on the INNER channel (enabled here), so it absorbs every
// byte that actually crosses the wire — packed gate bits, byte sends, Ferret
// OT — in true wire order. Callers read it via `io->get_digest()` on the inner
// channel; there is no separate hash here to keep in sync.
//
// The bits go in blocks: the number of bits of the block (4 bytes, little
// endian), then the bits, packed. A block is full (NETWORK_STAGING_BUFFER_SIZE
// bits) or is what a flush finds waiting, so a flush sends no padding. The
// number is public (the bits that the protocol sends since the last block),
// and a receiver refuses a number of 0 or above the size of its buffer.
class BoolIO : public IOChannel {
public:
  IOChannel *io;
  // Staging buffer of unpacked bools, flushed via the inner channel's
  // send_bool / recv_bool (which pack 8 bools per wire byte). Raw bool[]
  // (not vector<bool>, which is bit-packed) so we hand send_bool a real bool*.
  std::unique_ptr<bool[]> buf;
  int ptr = 0;  // the sender: the bits that wait; the receiver: the bits of the block that it has read
  int len = 0;  // the receiver: the bits of the block
  bool sender;
  BoolIO(IOChannel *io, int sender) : io(io), sender(sender) {
    // FS transcript on the inner channel; exactly one party passes true and
    // sender (= party == ALICE) satisfies that. Guard so re-wrapping a channel
    // that already has FS on is a no-op rather than an assert / reset.
    if (!io->fs_enabled())
      io->enable_fs(sender);
    buf.reset(new bool[NETWORK_STAGING_BUFFER_SIZE]);
  }
  ~BoolIO() { this->flush(); }
  // The sender sends the bits that wait; the receiver drops the rest of its
  // block.
  void flush() override {
    if (sender) {
      if (ptr != 0)
        send_block();
    } else {
      ptr = len;
    }
    io->flush();
  }

  void send_bit(bool data) {
    buf[ptr] = data;
    ptr++;
    if (ptr == NETWORK_STAGING_BUFFER_SIZE)
      send_block();
  }

  bool recv_bit() {
    if (ptr == len)
      recv_block();
    bool res = buf[ptr];
    ptr++;
    return res;
  }

  // Pending bits must reach the wire before any byte op so the bit and byte
  // streams stay ordered on the shared connection.
  void send_data_internal(const void *data, int64_t nbyte) override {
    if (!sender || ptr != 0)
      flush();
    io->send_data(data, nbyte);
  }

  void recv_data_internal(void *data, int64_t nbyte) override {
    if (sender || ptr != len)
      flush();
    io->recv_data(data, nbyte);
  }

private:
  void send_block() {
    const uint32_t n = static_cast<uint32_t>(ptr);
    const uint8_t size[4] = {uint8_t(n), uint8_t(n >> 8), uint8_t(n >> 16), uint8_t(n >> 24)};
    io->send_data(size, 4);
    io->send_bool(buf.get(), ptr);
    ptr = 0;
  }

  void recv_block() {
    uint8_t size[4];
    io->recv_data(size, 4);
    const uint32_t n = uint32_t(size[0]) | uint32_t(size[1]) << 8 | uint32_t(size[2]) << 16 | uint32_t(size[3]) << 24;
    expecting(n >= 1 && n <= uint32_t(NETWORK_STAGING_BUFFER_SIZE), "BoolIO: a block of bits of a wrong size");
    io->recv_bool(buf.get(), n);
    len = static_cast<int>(n);
    ptr = 0;
  }
};
} // namespace emp
#endif // __UNIDIRIO_H__
