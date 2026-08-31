#pragma once

// Deterministic source generation for Recaman.BalancedTraceCertificate.
//
// This tooling depends on the exact-history replay shared with Issue #67.
// Its output is untrusted empirical input: only the generated Lean theorem,
// checked through ValidBitTraceStep and BitTraceMachine.Represents, turns the
// proposed branch codes into a theorem about the Recaman sequence.

#include "lean_trace_witness.hpp"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <iomanip>
#include <limits>
#include <optional>
#include <ostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

namespace recaman::balanced_trace_source {

using Nat = lean_trace_witness::Nat;
using ExactTrace = lean_trace_witness::ExactTrace;
using StepReason = lean_trace_witness::StepReason;
using StepReasonKind = lean_trace_witness::StepReasonKind;

inline Nat encode_reason(const StepReason& reason) {
  switch (reason.kind) {
    case StepReasonKind::fresh:
      if (reason.witness_time) {
        throw std::logic_error("fresh reason unexpectedly carries a witness");
      }
      return 0;
    case StepReasonKind::nonpositive:
      if (reason.witness_time) {
        throw std::logic_error(
            "nonpositive reason unexpectedly carries a witness");
      }
      return 1;
    case StepReasonKind::blocked:
      if (!reason.witness_time) {
        throw std::logic_error("blocked reason has no witness");
      }
      if (*reason.witness_time > std::numeric_limits<Nat>::max() - 2) {
        throw std::overflow_error("blocked branch code overflow");
      }
      return *reason.witness_time + 2;
  }
  throw std::logic_error("unknown trace reason");
}

inline StepReason decode_code(Nat code) {
  if (code == 0) return {StepReasonKind::fresh, std::nullopt};
  if (code == 1) return {StepReasonKind::nonpositive, std::nullopt};
  return {StepReasonKind::blocked, code - 2};
}

inline std::vector<Nat> encode_trace(const ExactTrace& trace) {
  std::vector<Nat> codes;
  codes.reserve(trace.reasons.size());
  for (const auto& reason : trace.reasons) {
    codes.push_back(encode_reason(reason));
  }
  return codes;
}

inline Nat leaf_count(Nat steps, Nat leaf_size) {
  if (steps == 0) throw std::invalid_argument("steps must be positive");
  if (leaf_size == 0) {
    throw std::invalid_argument("leaf size must be positive");
  }
  return steps / leaf_size + (steps % leaf_size == 0 ? 0 : 1);
}

inline std::size_t decimal_width(Nat value) {
  std::size_t width = 1;
  while (value >= 10) {
    value /= 10;
    ++width;
  }
  return width;
}

inline std::string block_name(Nat index, std::size_t width) {
  const std::string digits = std::to_string(index);
  return "traceBlock" + std::string(width - digits.size(), '0') + digits;
}

inline void write_tree_expression(std::ostream& out, Nat begin, Nat end,
                                  std::size_t name_width) {
  if (begin >= end) throw std::logic_error("empty balanced tree range");
  if (end - begin == 1) {
    out << ".leaf " << block_name(begin, name_width);
    return;
  }
  const Nat middle = begin + (end - begin) / 2;
  out << ".node (";
  write_tree_expression(out, begin, middle, name_width);
  out << ") (";
  write_tree_expression(out, middle, end, name_width);
  out << ')';
}

// A small stable, explicitly specified regression fingerprint.  This is not
// a security primitive; it detects accidental byte changes in generated Lean
// source without relying on implementation-defined std::hash behavior.
inline std::uint64_t fnv1a64(std::string_view input) {
  std::uint64_t hash = 14695981039346656037ULL;
  for (const char character : input) {
    const auto byte = static_cast<unsigned char>(character);
    hash ^= byte;
    hash *= 1099511628211ULL;
  }
  return hash;
}

inline std::string hexadecimal_u64(std::uint64_t value) {
  std::ostringstream out;
  out << std::hex << std::nouppercase << std::setfill('0') << std::setw(16)
      << value;
  return out.str();
}

struct GeneratedSource {
  Nat steps;
  Nat leaf_size;
  Nat block_count;
  Nat capacity;
  Nat expected_value;
  Nat final_leaf_length;
  std::string source;

  [[nodiscard]] std::uint64_t fingerprint() const {
    return fnv1a64(source);
  }
};

inline GeneratedSource generate(const ExactTrace& trace, Nat leaf_size) {
  const Nat blocks = leaf_count(trace.steps, leaf_size);
  if (trace.max_value == std::numeric_limits<Nat>::max()) {
    throw std::overflow_error("trace capacity overflow");
  }
  const Nat capacity = trace.max_value + 1;
  const auto codes = encode_trace(trace);
  if (codes.size() != trace.steps) {
    throw std::logic_error("trace code count does not match horizon");
  }

  const std::size_t name_width =
      std::max<std::size_t>(2, decimal_width(blocks - 1));
  std::ostringstream out;
  out << "/-\n"
         "Generated deterministic EMPIRICAL INPUT ONLY.\n"
         "The C++ exact-history replay and its compact Nat codes are not part\n"
         "of the trusted base.  Code 0 proposes fresh, code 1 proposes\n"
         "nonpositive, and code (witnessTime + 2) proposes blocked.\n"
         "BalancedTrace.verifiesBitsValue is the final verifier in Lean.\n"
         "-/\n"
         "import Recaman.BalancedTraceCertificate\n\n"
         "namespace Recaman\n"
      << "namespace GeneratedBalancedTrace" << trace.steps << "\n\n"
      << "def traceSteps : Nat := " << trace.steps << "\n"
      << "def traceLeafSize : Nat := " << leaf_size << "\n"
      << "def traceBlockCount : Nat := " << blocks << "\n"
      << "def traceCapacity : Nat := " << capacity << "\n"
      << "def traceExpectedValue : Nat := " << trace.orbit.back() << "\n\n";

  for (Nat block = 0; block < blocks; ++block) {
    const Nat begin = block * leaf_size;
    const Nat end = std::min(trace.steps, begin + leaf_size);
    out << "def " << block_name(block, name_width) << " : List Nat :=\n  [";
    for (Nat index = begin; index < end; ++index) {
      if (index != begin) out << ", ";
      out << codes[static_cast<std::size_t>(index)];
    }
    out << "]\n\n";
  }

  out << "set_option maxRecDepth 100000 in\n"
         "def traceTree : BalancedTrace :=\n  ";
  write_tree_expression(out, 0, blocks, name_width);
  out << "\n\n"
         "set_option maxRecDepth 100000 in\n"
         "set_option maxHeartbeats 20000000 in\n"
         "theorem traceTree_length : traceTree.length = traceSteps := by\n"
         "  decide\n\n"
         "set_option maxRecDepth 100000 in\n"
         "set_option maxHeartbeats 20000000 in\n"
         "theorem traceBits_checked :\n"
         "    traceTree.verifiesBitsValue traceCapacity 0\n"
         "      initialBitTraceMachine traceExpectedValue = true := by\n"
         "  decide\n\n"
      << "theorem generated_value : a " << trace.steps << " = "
      << trace.orbit.back() << " := by\n"
         "  have hvalue := BalancedTrace.verified_bits_value\n"
         "    initialBitTraceMachine_represents traceBits_checked\n"
         "  rw [traceTree_length] at hvalue\n"
         "  simpa [traceSteps, traceExpectedValue] using hvalue\n\n"
      << "end GeneratedBalancedTrace" << trace.steps << "\n"
         "end Recaman\n";

  const Nat final_leaf_length =
      trace.steps - (blocks - 1) * leaf_size;
  return {trace.steps, leaf_size, blocks, capacity, trace.orbit.back(),
          final_leaf_length, out.str()};
}

inline GeneratedSource generate(Nat steps, Nat leaf_size = 64) {
  return generate(lean_trace_witness::replay(steps), leaf_size);
}

}  // namespace recaman::balanced_trace_source
