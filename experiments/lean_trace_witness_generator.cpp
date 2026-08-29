// Generate Lean-checkable empirical trace input for Issue #67.

#include "lean_trace_witness.hpp"

#include <charconv>
#include <iostream>
#include <stdexcept>
#include <string>

namespace {

using recaman::lean_trace_witness::Nat;

Nat parse_nat(const char* text, const char* name) {
  Nat value = 0;
  const std::string input(text);
  const auto result =
      std::from_chars(input.data(), input.data() + input.size(), value);
  if (result.ec != std::errc{} || result.ptr != input.data() + input.size()) {
    throw std::invalid_argument(std::string("invalid ") + name + ": " +
                                input);
  }
  return value;
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Nat trace_steps = argc > 1 ? parse_nat(argv[1], "traceSteps") : 2622;
    const Nat chunk_size = argc > 2 ? parse_nat(argv[2], "chunkSize") : 64;
    if (argc > 3) {
      throw std::invalid_argument(
          "usage: lean_trace_witness_generator "
          "[traceSteps=2622] [chunkSize=64]");
    }

    const auto trace = recaman::lean_trace_witness::replay(trace_steps);
    recaman::lean_trace_witness::write_clock112_lean_source(
        std::cout, trace, chunk_size);
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "Lean trace witness generator error: " << error.what()
              << '\n';
    return 2;
  }
}
