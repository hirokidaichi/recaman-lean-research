#include "prefix_successor_certificate.hpp"

#include <cstdlib>
#include <iostream>
#include <string_view>

namespace {

using recaman::prefix_successor::CertificateRow;
using recaman::prefix_successor::CoverageStatus;

[[noreturn]] void fail(std::string_view message) {
  std::cerr << "FAIL: " << message << '\n';
  std::exit(1);
}

void require(bool condition, std::string_view message) {
  if (!condition) fail(message);
}

const CertificateRow& require_clock(const std::vector<CertificateRow>& rows,
                                    std::uint64_t clock) {
  for (const auto& row : rows) {
    if (row.clock == clock) return row;
  }
  fail("expected eligible clock is absent");
}

}  // namespace

int main() {
  using namespace recaman::prefix_successor;

  const auto history = replay(400000);

  const auto clock112 = analyze(history, 112, 371);
  require(clock112.has_value(), "clock 112 must be eligible");
  require(clock112->anchor == 152, "clock 112 anchor regression");
  require(clock112->frontier.has_value(), "clock 112 frontier must exist");
  require(clock112->frontier->prefix_time == 108,
          "clock 112 predecessor time regression");
  require(clock112->frontier->predecessor_value == 370,
          "clock 112 predecessor value regression");
  require(clock112->frontier->successor_value == 371,
          "clock 112 successor regression");
  require(clock112->frontier->successor_first == 4825,
          "clock 112 successor first-occurrence regression");
  require(clock112->low_witness_time == 371 &&
              clock112->low_witness_value == 108,
          "clock 112 low-witness regression");
  require(clock112->low_witness_at_or_below_anchor,
          "clock 112 low witness must be below its anchor");
  require(clock112->uncovered_successor_count == 1,
          "clock 112 must have the unique successor exception 371");
  require(clock112->status == CoverageStatus::uncovered_late_first,
          "clock 112 cutoff 371 must expose the 371 exception");

  const auto through776 = analyze_range(history, 112, 776, 99734);
  require(!through776.empty(), "eligible clocks through 776 must exist");
  for (const auto& row : through776) {
    require(row.status == CoverageStatus::covered,
            "cutoff 99734 must cover every eligible clock through 776");
  }

  const auto through1000 = analyze_range(history, 112, 1000, 99734);
  const CertificateRow* first_uncovered = nullptr;
  for (const auto& row : through1000) {
    if (row.status != CoverageStatus::covered) {
      first_uncovered = &row;
      break;
    }
  }
  require(first_uncovered != nullptr, "an uncovered frontier must exist");
  require(first_uncovered->clock == 777,
          "first uncovered eligible clock regression");

  const auto& clock777 = require_clock(through1000, 777);
  require(clock777.anchor == 877, "clock 777 anchor regression");
  require(clock777.frontier.has_value(), "clock 777 frontier must exist");
  require(clock777.frontier->predecessor_value == 878,
          "clock 777 predecessor value regression");
  require(clock777.frontier->successor_value == 879,
          "clock 777 successor regression");
  require(clock777.frontier->successor_first == 328002,
          "clock 777 successor first-occurrence regression");
  require(clock777.low_witness_time == 99734 &&
              clock777.low_witness_value == 19,
          "clock 777 low-witness regression");
  require(clock777.low_witness_at_or_below_anchor,
          "clock 777 low witness must be below its anchor");
  require(clock777.uncovered_successor_count == 1,
          "clock 777 wall must have the unique successor exception 879");
  require(clock777.status == CoverageStatus::uncovered_late_first,
          "clock 777 must be beyond the cutoff frontier");

  std::cout << "prefix-successor certificate regressions: PASS\n";
}
