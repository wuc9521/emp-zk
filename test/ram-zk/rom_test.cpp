#include "emp-tool/emp-tool.h"
#include "emp-zk/emp-zk.h"
#include <iostream>
using namespace emp;
using namespace std;

int party;
int index_sz = 5, val_sz = 32;

void test(BoolIO *io, int party, const string &mode) {
  ZKBoolSession sess(io, party);
  if (mode.rfind("invalid-", 0) == 0) {
    const int index_bits = mode == "invalid-record" ? 0 : 1;
    const int value_bits = mode == "invalid-value" ? 0 : val_sz;
    ZKROM memory(sess, index_bits, value_bits, mode == "invalid-capacity" ? -1 : 1);
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
    ZKROM memory(sess, 1, val_sz, 1);
    memory.init(initial);
    const auto index = sess.input<ZKUInt>(PUBLIC, 0, 1);
    memory.read(index);
    sess.flush();  // Finish valid traffic before testing the public capacity guard.
    memory.read(index);
    error("ZKROM: capacity overflow accepted");
  }
  if (mode == "bounds") {
    ZKBit correct = ZKBit::constant(sess.ctx(), true);
    for (const int64_t limit : {0, 1, 2, 3, 4, 7, 8, 15, 16}) {
      vector<ZKUInt> initial{sess.input<ZKUInt>(PUBLIC, 19, val_sz)};
      ZKROM memory(sess, 1, val_sz, limit);
      memory.init(initial);
      const uint64_t expected = 19;
      for (int64_t step = 0; step < limit; ++step) {
        const auto index = sess.input<ZKUInt>(PUBLIC, 0, 1);
        const auto got = memory.read(index);
        correct = correct & (got == sess.input<ZKUInt>(PUBLIC, expected, val_sz));
      }
      memory.check();
    }
    if (!sess.reveal(correct, PUBLIC).value_or(false)) error("ZKROM: wrong boundary value");
    sess.finalize();
    cout << "ZKROM boundary cases ok" << endl;
    return;
  }
  if (mode == "cycle" || mode == "self") {
    vector<ZKUInt> initial{sess.input<ZKUInt>(PUBLIC, 0, val_sz)};
    ZKROM memory(sess, 1, val_sz, mode == "self" ? 1 : 3);
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
    cout << "ZKROM cycle accepted" << endl;
    return;
  }
  int test_n = (1 << index_sz);   // number of cells

  // Memory content x[i] = 2*i.
  vector<ZKUInt> data;
  for (int i = 0; i < test_n; ++i)
    data.push_back(sess.input<ZKUInt>(ALICE, 2 * i, val_sz));

  int rounds = 8;
  int64_t T = (int64_t)rounds * test_n;   // number of lookups

  ZKROM *rom = new ZKROM(sess, index_sz, val_sz, T);
  rom->init(data);

  // Soundness check: a malicious prover forges cell 0's value. The reads of
  // cell 0 then carry the wrong value and won't match any write → check()
  // must abort on the verifier.
  if (mode == "bad" && party == ALICE) rom->mem[0] ^= 1;

  auto start = clock_start();
  // Read every cell several times.
  int wrong = 0;
  for (int r = 0; r < rounds; ++r)
    for (int i = 0; i < test_n; ++i) {
      ZKUInt res = rom->read(sess.input<ZKUInt>(PUBLIC, i, index_sz));
      ZKBit eq = res == sess.input<ZKUInt>(ALICE, i * 2, val_sz);
      if (!sess.reveal(eq, PUBLIC).value_or(false)) wrong++;
    }
  rom->check();   // proves reads ∼ writes; aborts on a forged read
  double t = time_from(start);

  sess.finalize();
  int accesses = rounds * test_n;
  cout << "ROM ok (cells=" << test_n << ", accesses=" << accesses
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
