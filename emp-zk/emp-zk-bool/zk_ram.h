#ifndef EMP_ZK_RAM_H__
#define EMP_ZK_RAM_H__

#include <limits>
#include "emp-zk/emp-zk-bool/zk_perm_proof.h"

namespace emp {
using namespace std;

// Zero-knowledge memory: a permutation matches every read to a write with the
// same address, value and timestamp. Setup writes have time 0; each access
// writes at its distinct public clock, and must read a strictly earlier time.
// For each address the matching records form an init-to-teardown path and
// possibly cycles. Strict time order excludes cycles, so that path includes
// every access in chronological order: each reads the most recent value.
// Read-only accesses rewrite that same value and therefore retain setup data.
//
// T bounds the number of accesses, keeping their public timestamps distinct
// in time_sz bits. init() and check() each run once; operations are public.
// The local prover keeps uint64_t values: wider records require zero high bits.
class ZKRam {
public:
  int party;
  bool read_only;
  int64_t index_sz, val_sz, T;
  int64_t time_sz;                 // holds timestamps 0 … T
  int64_t n = 0;                   // number of cells
  uint64_t clock = 1;               // public; setup writes are time 0
  vector<uint64_t> mem;            // ALICE: current value per cell
  vector<uint64_t> last_t;         // ALICE: time of last write per cell
  ZKBoolSession &zk;               // owns the engine; source of runtime input/reveal
  ZKBoolBase *bb;
  ZKPermProof perm;                // reads ∼ writes
  ZKBit time_ok;                   // every access reads a strictly earlier write
  vector<F2kAuthValue> elem_;

  ZKRam(ZKBoolSession &sess, int64_t index_sz, int64_t val_sz, int64_t T,
        bool read_only = false)
      : party(sess.party()), read_only(read_only), index_sz(index_sz),
        val_sz(val_sz), T(T), time_sz(ramzk_bits_for(T)), zk(sess),
        bb(&sess.engine()), perm(sess, record_width(index_sz, val_sz, time_sz)),
        time_ok(ZKBit::constant(sess.ctx(), true)) {}

  // Setup: commit the initial contents and emit a write (i, x[i], 0) per cell.
  void init(vector<ZKUInt> &content) {
    if (index_sz < 64 && content.size() > (uint64_t(1) << index_sz))
      error("ZKRam: cell count exceeds index width");
    n = (int64_t)content.size();
    if (party == ALICE) {
      mem.resize(n);
      last_t.assign(n, 0);
    }
    ZKUInt time0 = zk.input<ZKUInt>(PUBLIC, 0, time_sz);
    for (int64_t i = 0; i < n; ++i) {
      if (content[i].width() != val_sz) error("ZKRam: initial value width differs");
      if (party == ALICE)
        mem[i] = zk.reveal(content[i], ALICE).value_or(0);
      else
        zk.reveal(content[i], ALICE);
      emit_(/*toA=*/false, content[i],
            zk.input<ZKUInt>(PUBLIC, (uint64_t)i, index_sz), time0);
    }
  }

  ZKUInt read(const ZKUInt &index) { return access_(index, index, false); }

  void write(const ZKUInt &index, const ZKUInt &value) {
    if (read_only)
      error("ZKRam: write() on read-only memory");
    access_(index, value, true);
  }

  // Teardown: check time order and read every cell's final state, then match records.
  // As with every session reveal, acceptance also requires zk.finalize().
  void check() {
    const bool ordered = zk.reveal(time_ok, PUBLIC).value_or(false);
    zk.flush();  // Publish the verdict bit before either party stops.
    if (!ordered) error("ZKRam: read does not precede its write");
    for (int64_t i = 0; i < n; ++i) {
      uint64_t v = (party == ALICE) ? mem[i] : 0;
      uint64_t t = (party == ALICE) ? last_t[i] : 0;
      emit_(/*toA=*/true, zk.input<ZKUInt>(ALICE, v, val_sz),
            zk.input<ZKUInt>(PUBLIC, (uint64_t)i, index_sz),
            zk.input<ZKUInt>(ALICE, t, time_sz));
    }
    perm.check_eq();
  }

private:
  static int64_t record_width(int64_t index_sz, int64_t val_sz, int64_t time_sz) {
    if (index_sz < 1 || index_sz > 64 || val_sz < 1 ||
        val_sz > std::numeric_limits<int>::max() - index_sz - time_sz)
      error("ZKRam: invalid record widths");
    return index_sz + val_sz + time_sz;
  }

  // One access. `value` is the new contents on a store; ignored on a load
  // (where we pass `index` as a harmless placeholder). Returns the old value.
  ZKUInt access_(const ZKUInt &index, const ZKUInt &value, bool is_write) {
    if (clock > static_cast<uint64_t>(T)) error("ZKRam: access capacity exceeded");
    if (index.width() != index_sz || (is_write && value.width() != val_sz))
      error("ZKRam: access widths differ");
    uint64_t ci = zk.reveal(index, ALICE).value_or(0);
    // An index_sz-bit witness can exceed the cell count. Avoid a local OOB by
    // reading defaults for an out-of-range index and letting the closing
    // permutation check reject (the bogus read matches no write) — a
    // verifier-observed failure rather than a prover-side abort.
    const bool in_range = (ci < (uint64_t)n);
    uint64_t v_old = 0, t_old = 0;
    if (party == ALICE && in_range) {
      v_old = mem[ci];
      t_old = last_t[ci];
    }
    ZKUInt old = zk.input<ZKUInt>(ALICE, v_old, val_sz);
    ZKUInt time_old = zk.input<ZKUInt>(ALICE, t_old, time_sz);

    const ZKUInt now = zk.input<ZKUInt>(PUBLIC, clock, time_sz);
    time_ok = time_ok & (time_old < now);

    // Read the old (addr, value, time), and write back the new state.
    emit_(/*toA=*/true, old, index, time_old);
    ZKUInt newv = is_write ? value : old;
    emit_(/*toA=*/false, newv, index, now);

    if (party == ALICE) {
      uint64_t nv = is_write ? zk.reveal(value, ALICE).value_or(0) : v_old;
      if (in_range) { mem[ci] = nv; last_t[ci] = clock; }
    } else if (is_write) {
      zk.reveal(value, ALICE);   // keep the two parties' reveals in lockstep
    }
    ++clock;
    return old;
  }

  void emit_(bool toA, const ZKUInt &value, const ZKUInt &index,
             const ZKUInt &time) {
    elem_.clear();
    ramzk_pack_record(bb, {&value, &index, &time}, elem_);
    if (toA)
      perm.add_A(elem_.data());
    else
      perm.add_B(elem_.data());
  }
};

// Read-only memory: the same time-ordered value chain, with writes disabled.
// T is the maximum number of read() lookups.
class ZKROM : public ZKRam {
public:
  ZKROM(ZKBoolSession &sess, int64_t index_sz, int64_t val_sz, int64_t T)
      : ZKRam(sess, index_sz, val_sz, T, /*read_only=*/true) {}
};

} // namespace emp
#endif // EMP_ZK_RAM_H__
