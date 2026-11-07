// Circuits expressed over the emp-tool BooleanContext, executed in zero knowledge
// on emp-zk-bool through ZKBoolContext / ZKBoolSession. Proves (1) a Ctx-templated
// typed kernel (UInt32 add) run in ZK via the session's generic input/reveal, and
// (2) an IR-replay builtin (sha256_256) run over the ZK context, validated
// bit-for-bit against a ClearCtx replay of the same circuit. C++20.

#include "emp-tool/emp-tool.h"
#include "emp-tool/ir/context/clear.h"   // ClearCtx
#include "emp-tool/ir/builtins.h"        // circuit::builtin_circuit
#include "emp-tool/ir/execute.h"         // execute_program
#include <emp-zk/emp-zk.h>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <limits>
#include <string>
#include <sys/wait.h>
#include <unistd.h>
#include <span>
#include <vector>

using namespace emp;

int party;
static int fails = 0;

// Feed cleartext bits as authenticated ZK wires owned by `owner` (ALICE witness
// or PUBLIC); the raw Ctx::Wire form execute_program consumes. Routes through the
// session's raw-bit boundary (no reaching into the engine).
static std::vector<ZKWire> feed_wires(ZKBoolSession &sess, int owner,
                                      const std::vector<uint8_t> &bits) {
  const int n = (int)bits.size();
  auto b = std::make_unique<bool[]>((size_t)n);
  for (int i = 0; i < n; ++i) b[(size_t)i] = bits[(size_t)i] != 0;
  return sess.input_bits(owner, b.get(), (size_t)n);
}
static std::vector<uint8_t> reveal_wires(ZKBoolSession &sess, int recipient,
                                         const std::vector<ZKWire> &w) {
  const int n = (int)w.size();
  auto b = std::make_unique<bool[]>((size_t)n);
  sess.reveal_bits(b.get(), recipient, w.data(), (size_t)n);
  std::vector<uint8_t> out((size_t)n);
  for (int i = 0; i < n; ++i) out[(size_t)i] = b[(size_t)i] ? 1 : 0;
  return out;
}

// Invalid configurations must fail at the shared Base guard before live OT.
// Run before any session/pool exists; a signal or timeout is a test failure.
template <class Make>
static void rejects_ot_threads(const char *api, int threads, Make make) {
  int diagnostic[2];
  expecting(pipe(diagnostic) == 0, "OT-thread test: pipe failed");
  std::fflush(nullptr);
  const pid_t child = fork();
  expecting(child >= 0, "OT-thread test: fork failed");
  if (child == 0) {
    close(diagnostic[0]);
    if (dup2(diagnostic[1], STDERR_FILENO) < 0) std::_Exit(3);
    close(diagnostic[1]);
    alarm(3);
    make();
    std::_Exit(0);
  }
  close(diagnostic[1]);
  std::string text;
  char buffer[512];
  ssize_t got;
  while ((got = read(diagnostic[0], buffer, sizeof buffer)) > 0)
    text.append(buffer, static_cast<size_t>(got));
  close(diagnostic[0]);
  int status = 0;
  const bool waited = waitpid(child, &status, 0) == child;
  const bool rejected = waited && WIFEXITED(status) && WEXITSTATUS(status) == 1 &&
      text.find("ZKBoolBase: OT thread count must be positive and at most INT_MAX/8") != std::string::npos;
  if (!rejected) ++fails;
  std::printf("OT threads %s %d: %s\n", api, threads, rejected ? "rejected at Base" : "FAIL");
  if (!rejected || !text.empty()) std::fprintf(stderr, "%s", text.c_str());
}

static void invalid_ot_threads(BoolIO *io, int party) {
  for (const int threads : {0, -1, std::numeric_limits<int>::max() / 8 + 1, std::numeric_limits<int>::max()}) {
    rejects_ot_threads("Session", threads, [&] { ZKBoolSession session(io, party, 0, threads); });
    rejects_ot_threads("Prover", threads, [&] { ZKBoolProver prover(io, 0, threads); });
    rejects_ot_threads("Verifier", threads, [&] { ZKBoolVerifier verifier(io, 0, threads); });
  }
}

void run(ZKBoolSession &sess, int party, const char *configuration) {
  ZKBoolSession::ctx_t &ctx = sess.ctx();

  // (1) Typed UInt32 add over the ZK context, via the session's generic
  // WireValue input/reveal (UInt_T<ZKBoolSession::ctx_t,32>).
  using U32 = UInt_T<ZKBoolSession::ctx_t, 32>;
  const uint32_t x = 0x12345678u, y = 0x9abcdef0u;
  U32 a = sess.input<U32>(ALICE, x);
  U32 b = sess.input<U32>(ALICE, y);
  uint32_t got = (uint32_t)sess.reveal(a + b, PUBLIC).value_or(0);
  if (got != (uint32_t)(x + y)) {
    ++fails;
    printf("UInt32 add over ZK: got %u want %u\n", got, (uint32_t)(x + y));
  }

  // (2) IR replay of the sha256_256 builtin over the ZK context, validated
  // against a ClearCtx replay of the SAME .empbc on the same (test) witness.
  const circuit::BooleanProgram &prog = circuit::builtin_circuit("sha256_256");
  const int nin = (int)prog.num_inputs;
  std::vector<uint8_t> wit((size_t)nin);
  for (int i = 0; i < nin; ++i)                // deterministic test witness
    wit[(size_t)i] = (uint8_t)(((uint32_t)i * 2654435761u) >> 17) & 1u;

  auto zin = feed_wires(sess, ALICE, wit);
  auto zout = execute_program(ctx, prog,
                              std::span<const ZKWire>(zin.data(), zin.size()));
  auto zdig = reveal_wires(sess, PUBLIC, zout);

  ClearCtx cctx;
  auto cout = execute_program(cctx, prog,
                              std::span<const uint8_t>(wit.data(), (size_t)nin));
  for (size_t i = 0; i < cout.size(); ++i)
    if ((zdig[i] & 1) != (cout[i] & 1)) {
      ++fails;
      printf("sha256_256 ZK-vs-ClearCtx replay mismatch at bit %zu\n", i);
      break;
    }

  sess.finalize();
  if (party == ALICE)
    printf("test_context_zk (%s): %s\n", configuration,
           fails ? "FAILED"
                 : "BooleanContext over ZK (UInt32 add + sha256_256 replay) — PASS");
}

int main(int argc, char **argv) {
  party = parse_party(argv);
  auto netio = (party == ALICE) ? NetIO::listen(peer_port()) : NetIO::connect(peer_ip(), peer_port());
  BoolIO io(netio.get(), party == ALICE);
  invalid_ot_threads(&io, party);
  if (fails) return 1;
  {
    ZKBoolSession session(&io, party);
    run(session, party, "omitted: default 1");
  }
  for (const int threads : {1, 2, 3, 4}) {
    ZKBoolSession session(&io, party, 0, threads);
    const std::string label = "explicit " + std::to_string(threads);
    run(session, party, label.c_str());
  }
  {
    // The existing third argument remains the COT prepay count, not workers.
    ZKBoolSession session(&io, party, int64_t{1024});
    run(session, party, "third expected_cots argument");
  }
  return fails ? 1 : 0;
}
