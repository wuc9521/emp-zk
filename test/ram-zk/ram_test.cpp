#include "emp-tool/emp-tool.h"
#include "emp-zk/emp-zk.h"
#include <iostream>
using namespace emp;
using namespace std;

int party;
// val_sz is wide on purpose: index_sz + val_sz + time_sz > 128 forces each
// record to span two f2k wires, exercising ZKPermProof's multi-block compress
// path. Values themselves stay < 2^16. Single-block records are covered by
// rom_test/set_test.
int index_sz = 5, val_sz = 130;

// Read/write RAM: init, an
// interleaved load/store stream that mutates cells, read-back checks, then
// check(). `bad` makes a malicious prover forge a stored value so the verifier
// must abort.
void test(BoolIO *io, int party, const string &mode) {
  ZKBoolSession sess(io, party);
  if (mode.rfind("invalid-", 0) == 0) {
    const int index_bits = mode == "invalid-record" ? 0 : 1;
    const int value_bits = mode == "invalid-value" ? 0 : val_sz;
    ZKRam memory(sess, index_bits, value_bits, mode == "invalid-capacity" ? -1 : 1);
    vector<ZKUInt> initial(mode == "invalid-cells" ? 3 : 1,
                          sess.input<ZKUInt>(PUBLIC, 19, mode == "invalid-init" ? val_sz - 1 : val_sz));
    memory.init(initial);
    memory.read(sess.input<ZKUInt>(PUBLIC, 0, mode == "invalid-index" ? 2 : 1));
    memory.check();
    sess.finalize();
    cout << "Invalid configuration accepted" << endl;
    return;
  }
  if (mode == "overflow") {
    vector<ZKUInt> initial{sess.input<ZKUInt>(PUBLIC, 19, val_sz)};
    ZKRam memory(sess, 1, val_sz, 1);
    memory.init(initial);
    const auto index = sess.input<ZKUInt>(PUBLIC, 0, 1);
    memory.read(index);
    sess.flush();  // Finish valid traffic before testing the public capacity guard.
    memory.read(index);
    error("ZKRam: capacity overflow accepted");
  }
  if (mode == "bounds") {
    ZKBit correct = ZKBit::constant(sess.ctx(), true);
    for (const int64_t limit : {0, 1, 2, 3, 4, 7, 8, 15, 16}) {
      vector<ZKUInt> initial{sess.input<ZKUInt>(PUBLIC, 19, val_sz)};
      ZKRam memory(sess, 1, val_sz, limit);
      memory.init(initial);
      uint64_t expected = 19;
      for (int64_t step = 0; step < limit; ++step) {
        const auto index = sess.input<ZKUInt>(PUBLIC, 0, 1);
        if ((step & 1) == 0) {
          expected += 3;
          memory.write(index, sess.input<ZKUInt>(PUBLIC, expected, val_sz));
        } else {
          const auto got = memory.read(index);
          correct = correct & (got == sess.input<ZKUInt>(PUBLIC, expected, val_sz));
        }
      }
      memory.check();
    }
    if (!sess.reveal(correct, PUBLIC).value_or(false)) error("ZKRam: wrong boundary value");
    sess.finalize();
    cout << "ZKRam boundary cases ok" << endl;
    return;
  }
  if (mode == "cycle" || mode == "self") {
    vector<ZKUInt> initial{sess.input<ZKUInt>(PUBLIC, 0, val_sz)};
    ZKRam memory(sess, 1, val_sz, mode == "self" ? 1 : 3);
    memory.init(initial);
    const auto index = sess.input<ZKUInt>(PUBLIC, 0, 1);
    // A disconnected future/past cycle balances the old record permutation.
    if (party == ALICE) { memory.mem[0] = 7; memory.last_t[0] = mode == "self" ? 1 : 2; }
    memory.read(index);
    if (mode == "cycle") memory.read(index);
    // Keep a separate honest path from setup to teardown.
    if (party == ALICE) { memory.mem[0] = 0; memory.last_t[0] = 0; }
    if (mode == "cycle") memory.read(index);
    memory.check();
    sess.finalize();
    cout << "ZKRam cycle accepted" << endl;
    return;
  }
  int cells = (1 << index_sz);

  int rounds = 4;
  int64_t T = (int64_t)rounds * cells * 2;   // each sweep: 1 write + 1 read / cell

  vector<ZKUInt> data;
  for (int i = 0; i < cells; ++i)
    data.push_back(sess.input<ZKUInt>(ALICE, i, val_sz));

  ZKRam *ram = new ZKRam(sess, index_sz, val_sz, T);
  ram->init(data);

  if (mode == "bad" && party == ALICE)
    ram->mem[0] += 1;   // forge cell 0: future reads carry a wrong value

  auto start = clock_start();
  int wrong = 0;
  vector<uint64_t> expect(cells);
  for (int i = 0; i < cells; ++i)
    expect[i] = i;

  for (int r = 0; r < rounds; ++r)
    for (int i = 0; i < cells; ++i) {
      expect[i] += cells;
      ram->write(sess.input<ZKUInt>(PUBLIC, i, index_sz),
                 sess.input<ZKUInt>(ALICE, expect[i], val_sz));
      ZKUInt got = ram->read(sess.input<ZKUInt>(PUBLIC, i, index_sz));
      ZKBit eq = got == sess.input<ZKUInt>(ALICE, expect[i], val_sz);
      if (!sess.reveal(eq, PUBLIC).value_or(false))
        wrong++;
    }
  ram->check();   // time order and record matching reject a forged value
  double t = time_from(start);

  delete ram;
  sess.finalize();
  int accesses = rounds * cells * 2;
  cout << "RAM ok (cells=" << cells << ", accesses=" << accesses
       << ", wrong=" << wrong << ")  " << t / accesses << " us/access  party "
       << party << endl;
}

int main(int argc, char **argv) {
  party = parse_party(argv);
  auto netio = (party == ALICE) ? NetIO::listen(peer_port()) : NetIO::connect(peer_ip(), peer_port());
  BoolIO io(netio.get(), party == ALICE);

  const string mode = argc >= 3 ? argv[2] : "honest";
  test(&io, party, mode);

  return 0;
}
