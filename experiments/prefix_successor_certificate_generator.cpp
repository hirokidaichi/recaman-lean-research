// Emit deterministic, Lean-connectable TSV candidates for
// ReplayPrefixSuccessorCoverage.  These rows are empirical audit output, not
// kernel proofs.

#include "prefix_successor_certificate.hpp"

#include <charconv>
#include <iostream>
#include <stdexcept>
#include <string>

namespace {

using recaman::prefix_successor::CertificateRow;
using recaman::prefix_successor::Nat;

Nat parse_nat(const char* text, const char* name) {
  Nat value = 0;
  const std::string input(text);
  const auto result =
      std::from_chars(input.data(), input.data() + input.size(), value);
  if (result.ec != std::errc{} || result.ptr != input.data() + input.size()) {
    throw std::invalid_argument(std::string("invalid ") + name + ": " + input);
  }
  return value;
}

void write_optional(std::ostream& out, const std::optional<Nat>& value) {
  if (value) {
    out << *value;
  } else {
    out << "none";
  }
}

void write_row(std::ostream& out, const CertificateRow& row) {
  out << "empirical\t" << row.orbit_steps << '\t' << row.clock << '\t'
      << row.anchor << '\t';
  if (row.frontier) {
    out << row.frontier->prefix_time << '\t'
        << row.frontier->predecessor_value << '\t'
        << row.frontier->successor_value << '\t';
    write_optional(out, row.frontier->successor_first);
  } else {
    out << "none\tnone\tnone\tnone";
  }
  out << '\t' << row.low_witness_time << '\t' << row.low_witness_value << '\t'
      << (row.low_witness_at_or_below_anchor ? "yes" : "no") << '\t'
      << row.uncovered_successor_count << '\t'
      << recaman::prefix_successor::status_name(row.status) << '\n';
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Nat steps = argc > 1 ? parse_nat(argv[1], "steps") : 400000;
    const Nat clock_max = argc > 2 ? parse_nat(argv[2], "clockMax") : 1000;
    const Nat cutoff = argc > 3 ? parse_nat(argv[3], "cutoff") : 99734;
    const Nat clock_min = argc > 4 ? parse_nat(argv[4], "clockMin") : 112;
    if (argc > 5) {
      throw std::invalid_argument(
          "usage: prefix_successor_certificate_generator "
          "[steps=400000] [clockMax=1000] [cutoff=99734] [clockMin=112]");
    }

    const auto history = recaman::prefix_successor::replay(steps);
    const auto rows = recaman::prefix_successor::analyze_range(
        history, clock_min, clock_max, cutoff);

    std::cout
        << "evidence_kind\torbit_steps\tclock\tanchor\tprefix_time\t"
           "predecessor_value\tsuccessor_value\tsuccessor_first\t"
           "low_witness_time\tlow_witness_value\t"
           "low_witness_at_or_below_anchor\tuncovered_successor_count\t"
           "coverage_status\n";
    for (const auto& row : rows) write_row(std::cout, row);
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "prefix-successor certificate error: " << error.what()
              << '\n';
    return 2;
  }
}
