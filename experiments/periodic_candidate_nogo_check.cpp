// Exact finite checker for the periodic candidate-drift identity.
//
// Write a periodic step word as signs epsilon_r in {-1,+1}, with +1 for
// addition and -1 for subtraction.  In the non-truncated candidate regime,
//
//   x_(n+1) - x_n = epsilon_n * (n+1) - 1.
//
// If one period has sign sum zero, the p-step drift C_r at phase r is
// constant from cycle to cycle.  The exact identities are
//
//   C_(r+1) - C_r = p * epsilon_r,
//   sum_r C_r = -p^2.
//
// Hence some phase has negative drift, so a zero-sign-sum periodic word
// cannot preserve a lower candidate floor.  Negative sign sum also breaks
// the floor, while positive sign sum makes every fixed phase diverge.
//
// The program exhausts all words in a requested period range.  It checks
// the zero-sum identities only; the accompanying paper argument proves the
// asymptotic consequences.
//
// Usage: periodic_candidate_nogo_check [first_period] [last_period]

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>

namespace {

using Count = std::uint64_t;
using Signed = std::int64_t;

unsigned ParsePeriod(const char* text) {
  const unsigned long parsed = std::stoul(text);
  if (parsed == 0UL || parsed > 24UL)
    throw std::invalid_argument("period must lie in 1..24");
  return static_cast<unsigned>(parsed);
}

Signed Sign(Count word, unsigned phase) {
  return ((word >> phase) & 1ULL) != 0ULL ? 1 : -1;
}

struct Totals {
  Count words = 0;
  Count negative = 0;
  Count positive = 0;
  Count balanced = 0;
  Count identity_failures = 0;
  Count no_negative_phase = 0;
};

void CheckPeriod(unsigned period, Totals& totals) {
  const Count word_count = 1ULL << period;
  for (Count word = 0; word < word_count; ++word) {
    ++totals.words;
    Signed sign_sum = 0;
    Signed drift = -static_cast<Signed>(period);
    for (unsigned phase = 0; phase < period; ++phase) {
      const Signed sign = Sign(word, phase);
      sign_sum += sign;
      drift += sign * static_cast<Signed>(phase + 1U);
    }

    if (sign_sum < 0) {
      ++totals.negative;
      continue;
    }
    if (sign_sum > 0) {
      ++totals.positive;
      continue;
    }

    ++totals.balanced;
    const Signed initial_drift = drift;
    Signed drift_sum = 0;
    Signed minimum_drift = drift;
    for (unsigned phase = 0; phase < period; ++phase) {
      drift_sum += drift;
      minimum_drift = std::min(minimum_drift, drift);
      drift += static_cast<Signed>(period) * Sign(word, phase);
    }
    if (drift != initial_drift ||
        drift_sum != -static_cast<Signed>(period) *
                         static_cast<Signed>(period))
      ++totals.identity_failures;
    if (minimum_drift >= 0) ++totals.no_negative_phase;
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const unsigned first = argc >= 2 ? ParsePeriod(argv[1]) : 1U;
    const unsigned last = argc >= 3 ? ParsePeriod(argv[2]) : 16U;
    if (first > last)
      throw std::invalid_argument("first_period must be <= last_period");

    Totals totals;
    for (unsigned period = first; period <= last; ++period)
      CheckPeriod(period, totals);

    std::cout << "periodic-candidate-nogo periods=[" << first << ',' << last
              << "] checkedWords=" << totals.words << '\n';
    std::cout << "negativeSignSum=" << totals.negative
              << " positiveSignSum=" << totals.positive
              << " balanced=" << totals.balanced << '\n';
    std::cout << "balancedIdentityFailures=" << totals.identity_failures
              << " balancedWithoutNegativePhase="
              << totals.no_negative_phase << '\n';
    if (totals.identity_failures != 0U ||
        totals.no_negative_phase != 0U)
      throw std::runtime_error("periodic drift identity failed");
    std::cout << "all balanced words satisfy sum(C_r)=-p^2 and have a "
                 "negative-drift phase\n";
    return EXIT_SUCCESS;
  } catch (const std::exception& error) {
    std::cerr << "periodic-candidate-nogo error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
}
