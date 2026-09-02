// Diagnostic census for H-20260902-04: where does a strict-high excursion
// after a burst use end, and how long can any cone-exterior excursion last?
//
// For generalized orbits (single initial value v0, exact greedy rule) the
// probe records, for every internal-demand burst use at clock m with
// candidate c >= 2, the first clock t > m whose candidate a t - (t+1) is at
// most t (the link breaker), classified by the ratio t / m and by the sign of
// the step into t.  Independently it records the maximal runs of clocks t
// with a t > 2t + 1 (cone-exterior runs) and the largest ratio
// (last clock + 1) / first clock over runs starting at clock >= 16.
//
// Frozen diagnostic questions:
//   Q1  is every breaker at t < 2m + 2 (before the doubling lattice clock)?
//   Q2  does every cone-exterior run starting at s >= max(16, 4 v0) end
//       before 2s + 1?

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using Nat = std::uint64_t;
using Clock = std::uint32_t;

constexpr Clock kNoClock = std::numeric_limits<Clock>::max();
constexpr Nat kValueCap = 400000000ULL;

class DenseHistory {
 public:
  bool Contains(Nat value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < seen_.size() &&
           ((seen_[word] >> (value & 63U)) & 1ULL) != 0U;
  }
  Clock First(Nat value) const {
    const std::size_t index = static_cast<std::size_t>(value);
    return index < first_.size() ? first_[index] : kNoClock;
  }
  void Record(Nat value, Clock clock) {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    if (word >= seen_.size()) seen_.resize(word + 1U, 0U);
    const std::uint64_t mask = 1ULL << (value & 63U);
    if ((seen_[word] & mask) != 0U) return;
    seen_[word] |= mask;
    const std::size_t index = static_cast<std::size_t>(value);
    if (index >= first_.size()) first_.resize(index + 1U, kNoClock);
    first_[index] = clock;
  }

 private:
  std::vector<std::uint64_t> seen_;
  std::vector<Clock> first_;
};

struct Census {
  Nat uses = 0U;
  Nat breaker_bins[4] = {0U, 0U, 0U, 0U};  // [1,1.25) [1.25,1.5) [1.5,2) [2,inf)
  Nat breaker_subtraction = 0U;
  Nat breaker_addition = 0U;
  Nat breakers_at_or_after_doubling = 0U;
  Nat no_breaker = 0U;
  double max_breaker_ratio = 0.0;
  Nat max_breaker_start = 0U, max_breaker_m = 0U, max_breaker_t = 0U,
      max_breaker_c = 0U;
  Nat runs = 0U;
  double max_run_ratio = 0.0;
  Nat max_run_start = 0U, max_run_first = 0U, max_run_last = 0U;
  Nat runs_reaching_doubling = 0U;
  Nat overflow = 0U;
};

Nat ParseNat(const char* text, Nat lower, Nat upper, const char* name) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed < lower || parsed > upper)
    throw std::invalid_argument(std::string(name) + " out of range");
  return static_cast<Nat>(parsed);
}

void ScanOrbit(Nat start, Clock horizon, Nat run_floor, Census& census) {
  const Clock simulation_end = horizon + 3U;
  DenseHistory history;
  history.Record(start, 0U);
  std::vector<Nat> values(static_cast<std::size_t>(simulation_end) + 1U, 0U);
  std::vector<unsigned char> signs(
      static_cast<std::size_t>(simulation_end) + 1U, 0U);
  values[0] = start;
  Nat value = start;
  for (Clock clock = 1U; clock <= simulation_end; ++clock) {
    const Nat candidate = value > clock ? value - clock : 0U;
    const bool subtract = value > clock && !history.Contains(candidate);
    signs[clock] = subtract ? static_cast<unsigned char>('S')
                            : static_cast<unsigned char>('A');
    value = subtract ? candidate : value + clock;
    if (value > kValueCap) {
      ++census.overflow;
      return;
    }
    values[clock] = value;
    history.Record(value, clock);
  }
  const auto candidate_at = [&values](Clock t) -> Nat {
    return values[t] > static_cast<Nat>(t) + 1U
               ? values[t] - static_cast<Nat>(t) - 1U
               : 0U;
  };
  const auto high_at = [&values](Clock t) -> bool {
    return values[t] > 2ULL * t + 1U;
  };

  // Breakers after burst uses.
  for (Clock m = 1U; m <= horizon; ++m) {
    const Nat c = candidate_at(m);
    if (c < 2U || c > m || signs[m] != static_cast<unsigned char>('S')) continue;
    if (signs[m + 1U] != 'A' || signs[m + 2U] != 'A' || signs[m + 3U] != 'A')
      continue;
    const Clock birth = history.First(c + m);
    if (birth == kNoClock || birth == 0U || birth > m + 1U) continue;
    ++census.uses;
    Clock t = m + 1U;
    while (t <= horizon && candidate_at(t) > static_cast<Nat>(t)) ++t;
    if (t > horizon) {
      ++census.no_breaker;
      continue;
    }
    const double ratio = static_cast<double>(t) / static_cast<double>(m);
    const int bin = ratio < 1.25 ? 0 : ratio < 1.5 ? 1 : ratio < 2.0 ? 2 : 3;
    ++census.breaker_bins[bin];
    if (signs[t] == 'S') ++census.breaker_subtraction; else ++census.breaker_addition;
    if (static_cast<Nat>(t) >= 2ULL * m + 2U) ++census.breakers_at_or_after_doubling;
    if (ratio > census.max_breaker_ratio) {
      census.max_breaker_ratio = ratio;
      census.max_breaker_start = start;
      census.max_breaker_m = m;
      census.max_breaker_t = t;
      census.max_breaker_c = c;
    }
  }

  // Cone-exterior runs, counted only from clock max(16, floor * v0) so that
  // the trivially high prefix of a large initial value is excluded.
  Clock t = static_cast<Clock>(std::max<Nat>(16U, run_floor * start));
  while (t <= horizon) {
    if (!high_at(t)) { ++t; continue; }
    const Clock first = t;
    while (t <= horizon && high_at(t)) ++t;
    const Clock last = t - 1U;
    ++census.runs;
    const double ratio = static_cast<double>(last + 1U) / static_cast<double>(first);
    if (static_cast<Nat>(last) + 1U >= 2ULL * first + 1U) ++census.runs_reaching_doubling;
    if (ratio > census.max_run_ratio) {
      census.max_run_ratio = ratio;
      census.max_run_start = start;
      census.max_run_first = first;
      census.max_run_last = last;
    }
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Nat lo = argc >= 2 ? ParseNat(argv[1], 0U, 100000000ULL, "lo") : 0U;
    const Nat hi = argc >= 3 ? ParseNat(argv[2], lo, 100000000ULL, "hi") : 1000U;
    const Clock horizon = static_cast<Clock>(
        argc >= 4 ? ParseNat(argv[3], 32U, 2000000000ULL, "horizon") : 100000U);
    const Nat run_floor =
        argc >= 5 ? ParseNat(argv[4], 0U, 1000U, "run_floor") : 4U;
    Census census;
    for (Nat start = lo; start <= hi; ++start)
      ScanOrbit(start, horizon, run_floor, census);
    std::cout << "cone-excursion starts=[" << lo << ',' << hi << "] horizon="
              << horizon << " overflow=" << census.overflow
              << " burstUses=" << census.uses
              << " noBreakerInHorizon=" << census.no_breaker << '\n';
    std::cout << "breaker t/m bins [1,1.25)=" << census.breaker_bins[0]
              << " [1.25,1.5)=" << census.breaker_bins[1]
              << " [1.5,2)=" << census.breaker_bins[2]
              << " [2,inf)=" << census.breaker_bins[3]
              << " intoSubtraction=" << census.breaker_subtraction
              << " intoAddition=" << census.breaker_addition << '\n';
    std::cout << "Q1 breakersAtOrAfterDoubling=" << census.breakers_at_or_after_doubling
              << " maxRatio=" << census.max_breaker_ratio
              << " (start=" << census.max_breaker_start << ",c=" << census.max_breaker_c
              << ",m=" << census.max_breaker_m << ",t=" << census.max_breaker_t << ")\n";
    std::cout << "Q2 runFloor=" << run_floor << " coneExteriorRuns=" << census.runs
              << " runsReachingDoubling=" << census.runs_reaching_doubling
              << " maxRatio=" << census.max_run_ratio
              << " (start=" << census.max_run_start << ",first=" << census.max_run_first
              << ",last=" << census.max_run_last << ")\n";
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
