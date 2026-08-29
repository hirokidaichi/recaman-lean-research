#pragma once

// Deterministic empirical inputs for Recaman.ChunkedTraceCertificate.
//
// Nothing computed here is trusted by Lean.  The generated source asks the
// kernel-checked trace checker to validate every branch reason and then checks
// the occurrence table against the authenticated chronological value array.

#include <algorithm>
#include <cstdint>
#include <limits>
#include <optional>
#include <ostream>
#include <stdexcept>
#include <string_view>
#include <utility>
#include <vector>

namespace recaman::lean_trace_witness {

using Nat = std::uint64_t;

inline constexpr Nat unset = std::numeric_limits<Nat>::max();

class BitSet {
 public:
  [[nodiscard]] bool contains(Nat value) const {
    const Nat word = value >> 6;
    return word < words_.size() &&
           ((words_[word] >> (value & 63)) & 1ULL) != 0;
  }

  void insert(Nat value) {
    const Nat word = value >> 6;
    if (word >= words_.size()) words_.resize(word + 1, 0);
    words_[word] |= 1ULL << (value & 63);
  }

 private:
  std::vector<Nat> words_;
};

enum class StepReasonKind { fresh, nonpositive, blocked };

struct StepReason {
  StepReasonKind kind;
  std::optional<Nat> witness_time;

  friend bool operator==(const StepReason&, const StepReason&) = default;
};

struct ExactTrace {
  Nat steps;
  Nat max_value;
  std::vector<Nat> orbit;
  std::vector<Nat> first_occurrence;
  std::vector<StepReason> reasons;

  [[nodiscard]] std::optional<Nat> first(Nat value) const {
    if (value >= first_occurrence.size() ||
        first_occurrence[value] == unset) {
      return std::nullopt;
    }
    return first_occurrence[value];
  }
};

// Replay from time zero with exact visited-value membership.  For a blocked
// subtraction, use the candidate's first occurrence as the canonical witness.
inline ExactTrace replay(Nat steps) {
  if (steps == unset) throw std::invalid_argument("steps is too large");

  std::vector<Nat> orbit(steps + 1, 0);
  std::vector<Nat> first_occurrence(1, 0);
  std::vector<StepReason> reasons;
  reasons.reserve(steps);

  BitSet seen;
  seen.insert(0);
  Nat value = 0;
  Nat max_value = 0;

  for (Nat clock = 1; clock <= steps; ++clock) {
    Nat next = 0;
    if (clock < value) {
      const Nat candidate = value - clock;
      if (!seen.contains(candidate)) {
        reasons.push_back({StepReasonKind::fresh, std::nullopt});
        next = candidate;
      } else {
        if (candidate >= first_occurrence.size() ||
            first_occurrence[candidate] == unset ||
            first_occurrence[candidate] >= clock) {
          throw std::logic_error("invalid exact-history blocked witness");
        }
        reasons.push_back(
            {StepReasonKind::blocked, first_occurrence[candidate]});
        if (value > unset - clock) {
          throw std::overflow_error("Recaman orbit value overflow");
        }
        next = value + clock;
      }
    } else {
      reasons.push_back({StepReasonKind::nonpositive, std::nullopt});
      if (value > unset - clock) {
        throw std::overflow_error("Recaman orbit value overflow");
      }
      next = value + clock;
    }

    value = next;
    orbit[clock] = value;
    max_value = std::max(max_value, value);
    if (value >= first_occurrence.size()) {
      first_occurrence.resize(value + 1, unset);
    }
    if (!seen.contains(value)) {
      first_occurrence[value] = clock;
      seen.insert(value);
    }
  }

  return {steps, max_value, std::move(orbit), std::move(first_occurrence),
          std::move(reasons)};
}

struct OccurrenceWitness {
  Nat value;
  Nat witness_time;

  friend bool operator==(const OccurrenceWitness&,
                         const OccurrenceWitness&) = default;
};

// Return one first-occurrence witness for every value in the inclusive band,
// except for the explicitly excluded value.  Missing values are an error so a
// partial empirical table can never be emitted silently.
inline std::vector<OccurrenceWitness> occurrence_witness_table(
    const ExactTrace& trace, Nat lower, Nat upper,
    std::optional<Nat> excluded = std::nullopt) {
  if (lower > upper) {
    throw std::invalid_argument("witness lower bound exceeds upper bound");
  }

  std::vector<OccurrenceWitness> witnesses;
  for (Nat value = lower;; ++value) {
    if (!excluded || value != *excluded) {
      const auto first = trace.first(value);
      if (!first) {
        throw std::runtime_error("requested witness value is absent");
      }
      witnesses.push_back({value, *first});
    }
    if (value == upper) break;
  }
  return witnesses;
}

inline std::string_view lean_reason_name(StepReasonKind kind) {
  switch (kind) {
    case StepReasonKind::fresh:
      return ".fresh";
    case StepReasonKind::nonpositive:
      return ".nonpositive";
    case StepReasonKind::blocked:
      return ".blocked";
  }
  throw std::logic_error("unknown trace reason");
}

inline void write_lean_reason(std::ostream& out, const StepReason& reason) {
  out << lean_reason_name(reason.kind);
  if (reason.kind == StepReasonKind::blocked) {
    if (!reason.witness_time) {
      throw std::logic_error("blocked reason has no witness time");
    }
    out << ' ' << *reason.witness_time;
  } else if (reason.witness_time) {
    throw std::logic_error("non-blocked reason has a witness time");
  }
}

// Emit a complete Lean module fragment.  Its theorem declarations are the
// trust boundary: the C++ replay merely proposes data, while Lean validates
// both the transition reasons and every target-band occurrence lookup.
inline void write_clock112_lean_source(std::ostream& out,
                                       const ExactTrace& trace,
                                       Nat chunk_size) {
  if (chunk_size == 0) {
    throw std::invalid_argument("chunk size must be positive");
  }
  if (trace.max_value == unset) {
    throw std::overflow_error("trace capacity overflow");
  }
  const auto witnesses = occurrence_witness_table(trace, 153, 261, 223);

  out << "/-\n"
         "Generated deterministic EMPIRICAL INPUT ONLY.\n"
         "The C++ generator is not a proof or part of the trusted base.\n"
         "The Lean declarations below make checkTraceChunks the final branch\n"
         "verifier and separately check every occurrence witness against its\n"
         "authenticated chronological trace array.\n"
         "-/\n"
         "import Recaman.ChunkedTraceCertificate\n\n"
         "namespace Recaman\n"
         "namespace Clock112EmpiricalInput\n\n"
         "set_option maxHeartbeats 2000000\n"
         "set_option maxRecDepth 1000000\n\n";
  out << "def traceSteps : Nat := " << trace.steps << "\n";
  out << "def traceCapacity : Nat := " << trace.max_value + 1 << "\n";
  out << "def traceChunkSize : Nat := " << chunk_size << "\n\n";

  out << "def traceChunks : List (List TraceStepReason) := [\n";
  for (std::size_t begin = 0; begin < trace.reasons.size();) {
    const std::size_t end = std::min<std::size_t>(
        trace.reasons.size(), begin + static_cast<std::size_t>(chunk_size));
    out << "  [";
    for (std::size_t index = begin; index < end; ++index) {
      if (index != begin) out << ", ";
      write_lean_reason(out, trace.reasons[index]);
    }
    out << ']';
    begin = end;
    if (begin != trace.reasons.size()) out << ',';
    out << '\n';
  }
  out << "]\n\n";

  out << "def targetOccurrenceWitnessTimes : List (Nat × Nat) := [\n";
  for (std::size_t index = 0; index < witnesses.size(); ++index) {
    const auto& witness = witnesses[index];
    out << "  (" << witness.value << ", " << witness.witness_time << ')';
    if (index + 1 != witnesses.size()) out << ',';
    out << '\n';
  }
  out << "]\n\n";

  out << "theorem trace_length_checked :\n"
         "    traceChunksLength traceChunks = traceSteps := by\n"
         "  decide\n\n"
         "theorem trace_checked :\n"
         "    checkTraceChunks 0 (initialTraceMachine traceCapacity)\n"
         "      traceChunks = true := by\n"
         "  decide\n\n"
         "def traceMachine : TraceMachine :=\n"
         "  replayTraceChunks 0 (initialTraceMachine traceCapacity) "
         "traceChunks\n\n"
         "def witnessEntryValid (entry : Nat × Nat) : Bool :=\n"
         "  traceMachine.values[entry.2]? == some entry.1\n\n"
         "def witnessEntriesValid : Bool :=\n"
         "  targetOccurrenceWitnessTimes.all witnessEntryValid\n\n"
         "theorem witness_entries_checked : witnessEntriesValid = true := by\n"
         "  decide\n\n"
         "end Clock112EmpiricalInput\n"
         "end Recaman\n";
}

}  // namespace recaman::lean_trace_witness
