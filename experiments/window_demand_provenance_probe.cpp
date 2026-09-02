// Exact canonical-orbit falsifier for H-20260902-02.
//
// A low supplied use is a state clock m with positive forced candidate
// c = a m - (m+1) <= m such that the exposed successor demand w = a m - 1
// is already visited by clock m.  The demand's canonical first occurrence
// is classified as subtraction-born (clock t) or addition-born (clock b).
// The probe aggregates every low supplied use into dyadic use-clock windows
// [2^k, 2^(k+1)) across all candidates and tests three frozen statements:
//
//   H-W  in every window containing both an addition-born demand with a
//        positive birth blocker e = w - 2b and a subtraction-born demand,
//        the blocker set E(W) meets the subtraction-born demand set S(W);
//   H-S  every subtraction-born low supplied demand satisfies 2t < w;
//   H-A  every addition-born low supplied demand satisfies 2b < w, i.e.
//        its birth addition was blocked, not truncated.
//
// The per-window census is printed in full so that the discovery and
// holdout ranges can be read without rerunning the search.

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <unordered_set>
#include <vector>

namespace {

using Clock = std::uint32_t;
using Value = std::uint64_t;

constexpr Clock kNoClock = std::numeric_limits<Clock>::max();
constexpr std::size_t kWitnessLimit = 5U;

class DenseHistory {
 public:
  bool Contains(Value value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < seen_.size() &&
           ((seen_[word] >> (value & 63U)) & 1ULL) != 0U;
  }

  Clock First(Value value) const {
    const std::size_t index = static_cast<std::size_t>(value);
    return index < first_.size() ? first_[index] : kNoClock;
  }

  bool AdditionBorn(Value value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < addition_born_.size() &&
           ((addition_born_[word] >> (value & 63U)) & 1ULL) != 0U;
  }

  void Record(Value value, Clock clock, bool addition_born) {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    if (word >= seen_.size()) {
      seen_.resize(word + 1U, 0U);
      addition_born_.resize(word + 1U, 0U);
    }
    const std::uint64_t mask = 1ULL << (value & 63U);
    if ((seen_[word] & mask) != 0U) return;
    seen_[word] |= mask;
    if (addition_born) addition_born_[word] |= mask;
    const std::size_t index = static_cast<std::size_t>(value);
    if (index >= first_.size()) first_.resize(index + 1U, kNoClock);
    first_[index] = clock;
  }

 private:
  std::vector<std::uint64_t> seen_;
  std::vector<std::uint64_t> addition_born_;
  std::vector<Clock> first_;
};

struct UseWitness {
  Clock use = 0U;
  Value candidate = 0U;
  Value demand = 0U;
  Clock birth = 0U;
};

struct Window {
  std::uint64_t low_uses = 0U;
  std::uint64_t high_uses = 0U;
  std::uint64_t subtraction_born = 0U;
  std::uint64_t addition_blocked = 0U;
  std::uint64_t addition_truncated = 0U;
  std::uint64_t near_diagonal = 0U;
  std::unordered_set<Value> candidates;
  std::unordered_set<Value> external;
  std::unordered_set<Value> subtractions;
};

Clock ParseClock(const char* text) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed == 0U || parsed > 2000000000ULL)
    throw std::invalid_argument("horizon must be in 1..2,000,000,000");
  return static_cast<Clock>(parsed);
}

std::size_t WindowIndex(Clock clock) {
  std::size_t index = 0U;
  while ((static_cast<std::uint64_t>(1) << (index + 1U)) <= clock) ++index;
  return index;
}

std::uint64_t IntersectionSize(const std::unordered_set<Value>& left,
                               const std::unordered_set<Value>& right) {
  const auto& small = left.size() <= right.size() ? left : right;
  const auto& large = left.size() <= right.size() ? right : left;
  std::uint64_t count = 0U;
  for (const Value value : small)
    if (large.find(value) != large.end()) ++count;
  return count;
}

void PrintWitnesses(const char* label, const std::vector<UseWitness>& list,
                    std::uint64_t total) {
  std::cout << label << '=' << (total == 0U ? "not-refuted" : "REFUTED")
            << " violations=" << total;
  for (const UseWitness& witness : list)
    std::cout << " (m=" << witness.use << ",c=" << witness.candidate
              << ",w=" << witness.demand << ",birth=" << witness.birth << ')';
  std::cout << '\n';
}

void Run(Clock horizon) {
  DenseHistory history;
  history.Record(0U, 0U, false);
  std::vector<Window> windows;
  std::vector<UseWitness> s_violations, a_violations;
  std::uint64_t s_total = 0U, a_total = 0U;
  std::uint64_t low_uses = 0U, high_uses = 0U;
  Value value = 0U;

  for (std::uint64_t raw = 1U; raw <= horizon; ++raw) {
    const Clock use_clock = static_cast<Clock>(raw - 1U);
    const bool positive = value > raw;
    const Value candidate = positive ? value - raw : 0U;
    const bool subtraction = positive && !history.Contains(candidate);
    const bool forced_positive = positive && !subtraction;
    const Value demand = value - 1U;

    if (subtraction) {
      value = candidate;
    } else {
      value += raw;
    }
    history.Record(value, static_cast<Clock>(raw), !subtraction);

    if (!forced_positive || !history.Contains(demand)) continue;
    const std::size_t index = WindowIndex(use_clock);
    if (index >= windows.size()) windows.resize(index + 1U);
    Window& window = windows[index];
    if (candidate > use_clock) {
      ++high_uses;
      ++window.high_uses;
      continue;
    }
    ++low_uses;
    ++window.low_uses;
    window.candidates.insert(candidate);
    const Clock birth = history.First(demand);
    if (birth == kNoClock) throw std::runtime_error("missing first clock");
    const std::uint64_t twice_birth = 2ULL * birth;
    const UseWitness witness{use_clock, candidate, demand, birth};
    if (history.AdditionBorn(demand)) {
      if (twice_birth < demand) {
        ++window.addition_blocked;
        window.external.insert(demand - twice_birth);
      } else {
        ++window.addition_truncated;
        ++a_total;
        if (a_violations.size() < kWitnessLimit) a_violations.push_back(witness);
      }
    } else {
      ++window.subtraction_born;
      window.subtractions.insert(demand);
      if (twice_birth >= demand) {
        ++window.near_diagonal;
        ++s_total;
        if (s_violations.size() < kWitnessLimit) s_violations.push_back(witness);
      }
    }
  }

  std::cout << "window-demand-provenance horizon=" << horizon
            << " lowSuppliedUses=" << low_uses
            << " highSuppliedUses=" << high_uses
            << " windows=" << windows.size() << '\n';
  std::cout << "window k:[2^k,2^(k+1)) low high candidates sBorn aBlocked"
               " aTruncated nearDiagonal |E| |S| |E&S|\n";
  std::uint64_t applicable = 0U, refuting = 0U;
  std::vector<std::size_t> refuting_windows;
  for (std::size_t k = 0U; k < windows.size(); ++k) {
    const Window& window = windows[k];
    const std::uint64_t overlap =
        IntersectionSize(window.external, window.subtractions);
    const bool testable =
        !window.external.empty() && !window.subtractions.empty();
    if (testable) {
      ++applicable;
      if (overlap == 0U) {
        ++refuting;
        refuting_windows.push_back(k);
      }
    }
    std::cout << "window " << k << ' ' << window.low_uses << ' '
              << window.high_uses << ' ' << window.candidates.size() << ' '
              << window.subtraction_born << ' ' << window.addition_blocked
              << ' ' << window.addition_truncated << ' '
              << window.near_diagonal << ' ' << window.external.size() << ' '
              << window.subtractions.size() << ' ' << overlap << '\n';
  }
  std::cout << "H-W=" << (refuting == 0U ? "not-refuted" : "REFUTED")
            << " applicableWindows=" << applicable
            << " collisionFreeWindows=" << refuting;
  for (const std::size_t k : refuting_windows) std::cout << ' ' << k;
  std::cout << '\n';
  PrintWitnesses("H-S", s_violations, s_total);
  PrintWitnesses("H-A", a_violations, a_total);
}

}  // namespace

int main(int argc, char** argv) {
  try {
    Run(argc >= 2 ? ParseClock(argv[1]) : 2000000U);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
