#include "emp-tool/emp-tool.h"
#include <emp-zk/emp-zk.h>
#include <iostream>
#include <string>
using namespace emp;
using namespace std;

int party;
const int W = 64;   // bit width of each fed value

// Build a valid authenticated f2k wire from a fresh ALICE-input value: feed W
// authenticated bits and pack them into one F(2^128) element via the local
// Σ·Xⁱ map (mac from the bit wires, val from the cleartext LSBs).
static F2kAuthValue make_wire(ZKBoolSession &sess, uint64_t v) {
  ZKInt x = sess.input<ZKInt>(ALICE, v, W);
  vector<F2kAuthValue> out;
  ramzk_pack_record(&sess.engine(), {&x}, out);
  return out[0];
}

// n elements, each `m` wires (payload = m*128 bits). A is the natural order;
// B is the same elements in reversed order (a permutation). `bad` corrupts
// one wire of B so the multiset no longer matches.
void test_perm(BoolIO *io, int party, int n, int bits,
               const string &mode) {
  ZKBoolSession sess(io, party);
  const int m = (bits + 127) / 128;
  const bool bad = (mode == "bad");
  // "periodic" exercises explicit per-batch compress(): each fold draws its
  // own coefficient, so matched elements must stay in the same batch — use
  // identity order. Otherwise B is the reversed permutation, folded once.
  const bool periodic = (mode == "periodic");

  vector<F2kAuthValue> elems((size_t)n * m);
  for (int i = 0; i < n; ++i)
    for (int j = 0; j < m; ++j)
      elems[(size_t)i * m + j] =
          make_wire(sess, ((uint64_t)i * 2654435761ull + 7) ^ ((uint64_t)j << 40));

  auto start = clock_start();
  ZKPermProof perm(sess, bits);
  const int chunk = (n >= 4) ? n / 4 : n;
  for (int i = 0; i < n; ++i) {
    perm.add_A(&elems[(size_t)i * m]);
    int src = periodic ? i : (n - 1 - i);
    if (bad && i == 0) {
      F2kAuthValue e[8];                  // corrupt one element's first wire
      for (int j = 0; j < m; ++j) e[j] = elems[(size_t)src * m + j];
      e[0] = make_wire(sess, 0xDEADBEEFull);
      perm.add_B(e);
    } else {
      perm.add_B(&elems[(size_t)src * m]);
    }
    if (periodic && (i + 1) % chunk == 0) perm.compress();   // fold this batch
  }
  perm.check_eq();   // passes iff B is a permutation of A
  double t = time_from(start);

  sess.finalize();
  cout << "perm check (n=" << n << ", bits=" << bits << " [" << m << " blk]"
       << (mode.empty() ? "" : ", " + mode) << ") PASSED\t" << t
       << " us\tparty " << party << endl;
}

// The key check consumes the first authentication mask without producing a
// multiplication. A small logical window exercises that partial first batch
// and later full refills; the real backing buffers and correlations stay intact.
static void test_rollover(BoolIO *io, int party, bool bad) {
  ZKBoolSession sess(io, party);
  auto &engine = sess.engine();
  engine.f2k_init();
  expecting(engine.f2k_authval_cnt == 1 && engine.f2k_check_cnt == 0 && engine.f2k_buffer_sz >= 4,
            "rollover test did not start after the real key check");
  engine.f2k_buffer_sz = 4;
  const auto zero = engine.f2k_wire(zero_block, zero_block);
  F2kAuthValue value, factor;
  engine.f2k_add_const(value, zero, makeBlock(0, 2));
  engine.f2k_add_const(factor, zero, makeBlock(0, 3));
  block expected = makeBlock(0, 2);
  for (int i = 0; i < 12; ++i) {
    F2kAuthValue next;
    engine.f2k_mul(next, value, factor);
    gfmul(expected, makeBlock(0, 3), &expected);
    if (party == ALICE) {
      expecting(cmpBlock(&next.val, &expected, 1), "rollover changed the returned product");
      if (bad && i == 0) engine.f2k_left_mac[0] ^= makeBlock(0, 1);
    }
    value = next;
  }
  if (!bad) {
    F2kAuthValue want;
    engine.f2k_add_const(want, zero, expected);
    ZKPermProof equal(sess, 128);
    equal.add_A(&value); equal.add_B(&want); equal.check_eq();
  }
  sess.finalize();
  cout << "f2k rollover " << (bad ? "BAD ACCEPTED" : "PASSED") << " party " << party << endl;
}

int main(int argc, char **argv) {
  party = parse_party(argv);
  auto netio = (party == ALICE) ? NetIO::listen(peer_port()) : NetIO::connect(peer_ip(), peer_port());
  BoolIO io(netio.get(), party == ALICE);

  int n = (argc >= 3) ? atoi(argv[2]) : 100000;
  int bits = (argc >= 4) ? atoi(argv[3]) : 128;
  string mode = (argc >= 5) ? string(argv[4]) : "";   // "", "periodic", "bad"
  if (mode == "rollover" || mode == "rollover-bad")
    test_rollover(&io, party, mode == "rollover-bad");
  else {
    test_rollover(&io, party, false);
    test_perm(&io, party, n, bits, mode);
  }

  return 0;
}
