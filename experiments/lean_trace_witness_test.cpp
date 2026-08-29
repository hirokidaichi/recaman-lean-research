#include "lean_trace_witness.hpp"

#include <cstdlib>
#include <iostream>
#include <sstream>
#include <string_view>
#include <vector>

namespace {

using recaman::lean_trace_witness::ExactTrace;
using recaman::lean_trace_witness::Nat;
using recaman::lean_trace_witness::StepReason;
using recaman::lean_trace_witness::StepReasonKind;

[[noreturn]] void fail(std::string_view message) {
  std::cerr << "FAIL: " << message << '\n';
  std::exit(1);
}

void require(bool condition, std::string_view message) {
  if (!condition) fail(message);
}

void validate_reasons(const ExactTrace& trace) {
  require(trace.orbit.size() == trace.steps + 1,
          "orbit size must match trace horizon");
  require(trace.reasons.size() == trace.steps,
          "one reason is required per transition");

  for (Nat clock = 1; clock <= trace.steps; ++clock) {
    const Nat previous = trace.orbit[clock - 1];
    const Nat next = trace.orbit[clock];
    const StepReason& reason = trace.reasons[clock - 1];
    switch (reason.kind) {
      case StepReasonKind::fresh: {
        require(clock < previous, "fresh subtraction must be positive");
        const Nat candidate = previous - clock;
        require(next == candidate, "fresh next-value mismatch");
        require(trace.first(candidate) == clock,
                "fresh result must first occur at this clock");
        require(!reason.witness_time,
                "fresh reason must not carry a witness");
        break;
      }
      case StepReasonKind::nonpositive:
        require(!(clock < previous),
                "nonpositive reason used for a positive candidate");
        require(next == previous + clock,
                "nonpositive next-value mismatch");
        require(!reason.witness_time,
                "nonpositive reason must not carry a witness");
        break;
      case StepReasonKind::blocked: {
        require(clock < previous, "blocked subtraction must be positive");
        require(reason.witness_time.has_value(),
                "blocked reason must carry a witness");
        const Nat witness_time = *reason.witness_time;
        const Nat candidate = previous - clock;
        require(witness_time < clock,
                "blocked witness must precede the transition");
        require(trace.orbit[witness_time] == candidate,
                "blocked witness value mismatch");
        require(trace.first(candidate) == witness_time,
                "blocked witness must be the deterministic first occurrence");
        require(next == previous + clock, "blocked next-value mismatch");
        break;
      }
    }
  }
}

}  // namespace

int main() {
  using namespace recaman::lean_trace_witness;

  const auto first_fifteen = replay(15);
  const std::vector<StepReason> expected_first_fifteen{
      {StepReasonKind::nonpositive, std::nullopt},
      {StepReasonKind::nonpositive, std::nullopt},
      {StepReasonKind::nonpositive, std::nullopt},
      {StepReasonKind::fresh, std::nullopt},
      {StepReasonKind::nonpositive, std::nullopt},
      {StepReasonKind::blocked, 1},
      {StepReasonKind::blocked, 3},
      {StepReasonKind::fresh, std::nullopt},
      {StepReasonKind::blocked, 2},
      {StepReasonKind::fresh, std::nullopt},
      {StepReasonKind::nonpositive, std::nullopt},
      {StepReasonKind::fresh, std::nullopt},
      {StepReasonKind::nonpositive, std::nullopt},
      {StepReasonKind::fresh, std::nullopt},
      {StepReasonKind::nonpositive, std::nullopt},
  };
  require(first_fifteen.reasons == expected_first_fifteen,
          "first-fifteen reason regression");
  require(first_fifteen.orbit.back() == 24,
          "first-fifteen endpoint regression");
  validate_reasons(first_fifteen);

  const auto clock112_trace = replay(2622);
  validate_reasons(clock112_trace);
  const auto witnesses =
      occurrence_witness_table(clock112_trace, 153, 261, 223);
  require(witnesses.size() == 108,
          "clock-112 target band must have 108 included values");
  for (std::size_t index = 0; index < witnesses.size(); ++index) {
    const auto& witness = witnesses[index];
    const Nat expected_value = index < 70 ? 153 + index : 154 + index;
    require(witness.value == expected_value,
            "target witness values must be ordered and omit only 223");
    require(witness.witness_time <= 2622,
            "included target witness exceeds trace horizon");
    require(clock112_trace.orbit[witness.witness_time] == witness.value,
            "target witness does not point to its value");
    require(clock112_trace.first(witness.value) == witness.witness_time,
            "target witness must be a first occurrence");
  }
  require(!clock112_trace.first(223),
          "excluded target 223 must be absent through clock 2622");

  const auto deep_trace = replay(181545);
  require(deep_trace.first(223) == 181545,
          "excluded target 223 first-occurrence regression");

  std::ostringstream source;
  write_clock112_lean_source(source, clock112_trace, 64);
  const std::string lean = source.str();
  require(lean.find("EMPIRICAL INPUT ONLY") != std::string::npos,
          "generated source must state its empirical status");
  require(lean.find("theorem trace_checked") != std::string::npos,
          "generated source must invoke the Lean trace checker");
  require(lean.find("theorem witness_entries_checked") != std::string::npos,
          "generated source must invoke the Lean witness checker");
  require(lean.find("(223,") == std::string::npos,
          "generated witness table must exclude target 223");

  std::cout << "Lean trace witness generator regressions: PASS\n";
}
