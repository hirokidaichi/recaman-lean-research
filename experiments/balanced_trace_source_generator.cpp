// Emit a deterministic balanced Lean trace certificate source module.

#include "balanced_trace_source.hpp"

#include <charconv>
#include <iostream>
#include <stdexcept>
#include <string>

namespace {

using recaman::balanced_trace_source::Nat;

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
    const Nat steps = argc > 1 ? parse_nat(argv[1], "steps") : 4825;
    const Nat leaf_size = argc > 2 ? parse_nat(argv[2], "leafSize") : 64;
    if (argc > 3) {
      throw std::invalid_argument(
          "usage: balanced_trace_source_generator "
          "[steps=4825] [leafSize=64]");
    }

    const auto generated =
        recaman::balanced_trace_source::generate(steps, leaf_size);
    std::cout << generated.source;
    std::cerr << "empirical_metrics"
              << " steps=" << generated.steps
              << " leaf_size=" << generated.leaf_size
              << " block_count=" << generated.block_count
              << " final_leaf_length=" << generated.final_leaf_length
              << " capacity=" << generated.capacity
              << " expected_value=" << generated.expected_value
              << " source_bytes=" << generated.source.size()
              << " source_fnv1a64="
              << recaman::balanced_trace_source::hexadecimal_u64(
                     generated.fingerprint())
              << '\n';
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "balanced trace source generator error: " << error.what()
              << '\n';
    return 2;
  }
}
