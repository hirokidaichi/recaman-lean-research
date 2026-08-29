#include "balanced_trace_source.hpp"

#include <cstdlib>
#include <iostream>
#include <optional>
#include <string_view>
#include <vector>

namespace {

using recaman::balanced_trace_source::Nat;

[[noreturn]] void fail(std::string_view message) {
  std::cerr << "FAIL: " << message << '\n';
  std::exit(1);
}

void require(bool condition, std::string_view message) {
  if (!condition) fail(message);
}

}  // namespace

int main() {
  using namespace recaman::balanced_trace_source;

  const auto first_fifteen_trace = recaman::lean_trace_witness::replay(15);
  const auto first_fifteen_codes = encode_trace(first_fifteen_trace);
  const std::vector<Nat> expected_codes{
      1, 1, 1, 0, 1, 3, 5, 0, 4, 0, 1, 0, 1, 0, 1};
  require(first_fifteen_codes == expected_codes,
          "compact branch-code regression");
  for (std::size_t index = 0; index < first_fifteen_codes.size(); ++index) {
    require(decode_code(first_fifteen_codes[index]) ==
                first_fifteen_trace.reasons[index],
            "compact branch code must decode to the exact-history reason");
  }

  const auto trace1024 = generate(1024, 64);
  require(trace1024.block_count == 16,
          "1024 steps must produce sixteen leaves");
  require(trace1024.final_leaf_length == 64,
          "1024 final leaf must have 64 codes");
  require(trace1024.expected_value == 3698,
          "1024 endpoint regression");
  require(trace1024.source.find("namespace GeneratedBalancedTrace1024") !=
              std::string::npos,
          "1024 generated namespace is absent");
  require(trace1024.source.find("EMPIRICAL INPUT ONLY") != std::string::npos,
          "generated source must mark the empirical trust boundary");
  require(trace1024.source.find("BalancedTrace.verifiesBitsValue") !=
              std::string::npos,
          "generated source must name the Lean final verifier");

  const auto trace4825 = generate(4825, 64);
  require(trace4825.block_count == 76,
          "4825 steps must produce 76 leaves");
  require(trace4825.final_leaf_length == 25,
          "4825 final leaf must have 25 codes");
  require(trace4825.expected_value == 371,
          "4825 endpoint regression");
  require(trace4825.source.find("theorem generated_value : a 4825 = 371") !=
              std::string::npos,
          "4825 generated endpoint theorem is absent");

  // Filled with the deterministic FNV-1a fingerprint of the complete Lean
  // source.  A byte-level source change must be reviewed explicitly.
  constexpr std::uint64_t expected_4825_fingerprint =
      0x7e016593e1de83ebULL;
  if (trace4825.fingerprint() != expected_4825_fingerprint) {
    std::cerr << "observed 4825 fingerprint: "
              << hexadecimal_u64(trace4825.fingerprint()) << '\n';
    fail("4825 generated source fingerprint regression");
  }

  const auto trace99734 = generate(99734, 64);
  require(trace99734.block_count == 1559,
          "99734 steps must produce 1559 leaves");
  require(trace99734.final_leaf_length == 22,
          "99734 final leaf must have 22 codes");
  require(trace99734.expected_value == 19,
          "99734 endpoint regression");
  require(!trace99734.source.empty(),
          "99734 source-size measurement requires generated source");

  std::cout << "balanced trace source generator regressions: PASS\n";
}
