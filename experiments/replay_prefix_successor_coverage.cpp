// Empirical audit for ReplayPrefixSuccessorCoverage.
//
// For every numerically eligible replay clock C, inspect all earlier orbit
// values a(f) above the crossing anchor a(C).  The Lean coverage theorem can
// eliminate C when every successor a(f)+1 has already occurred by a cutoff,
// provided the orbit also has a low witness at that cutoff.
//
// This program only discovers candidate certificates.  Its output is not
// imported into Lean.
//
// Usage:
//   replay_prefix_successor_coverage [N=1000000] [Cmax=1000]
//                                    [cutoff=99734] [Cmin=112]

// N must cover both Cmax+1 and the first occurrences being inspected.

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

struct BitSet {
  std::vector<std::uint64_t> words;

  bool get(std::uint64_t value) const {
    const std::uint64_t word = value >> 6;
    return word < words.size() &&
           ((words[word] >> (value & 63)) & 1ULL) != 0;
  }

  void set(std::uint64_t value) {
    const std::uint64_t word = value >> 6;
    if (word >= words.size()) words.resize(word + 1, 0);
    words[word] |= 1ULL << (value & 63);
  }
};

int main(int argc, char** argv) {
  const std::uint64_t steps =
      argc > 1 ? std::stoull(argv[1]) : 1000000ULL;
  std::uint64_t clockMax =
      argc > 2 ? std::stoull(argv[2]) : 1000ULL;
  const std::uint64_t cutoff =
      argc > 3 ? std::stoull(argv[3]) : 99734ULL;
  const std::uint64_t clockMin =
      argc > 4 ? std::stoull(argv[4]) : 112ULL;

  if (steps == 0) return 0;
  clockMax = std::min(clockMax, steps - 1);

  const auto unset = std::numeric_limits<std::uint64_t>::max();
  std::vector<std::uint64_t> orbit(steps + 1, 0);
  std::vector<std::uint64_t> firstOccurrence(1, 0);
  BitSet seen;
  seen.set(0);

  std::uint64_t value = 0;
  for (std::uint64_t step = 1; step <= steps; ++step) {
    const bool subtract = value > step && !seen.get(value - step);
    value = subtract ? value - step : value + step;
    orbit[step] = value;
    if (value >= firstOccurrence.size())
      firstOccurrence.resize(value + 1, unset);
    if (!seen.get(value)) {
      firstOccurrence[value] = step;
      seen.set(value);
    }
  }

  std::uint64_t eligible = 0;
  std::uint64_t covered = 0;
  std::uint64_t firstUncoveredClock = unset;

  std::cout << "steps=" << steps << " clockRange=[" << clockMin << ","
            << clockMax << "] cutoff=" << cutoff;
  if (cutoff <= steps)
    std::cout << " cutoffValue=" << orbit[cutoff];
  else
    std::cout << " cutoffValue=outside-run";
  std::cout << "\n";
  std::cout << "clock,anchor,worstSuccessor,worstFirst,covered\n";

  for (std::uint64_t clock = clockMin; clock <= clockMax; ++clock) {
    const bool numericReplayClock =
        clock + 1 < orbit[clock] &&
        orbit[clock + 1] == orbit[clock] + (clock + 1);
    if (!numericReplayClock) continue;
    ++eligible;

    bool coverage = true;
    std::uint64_t worstSuccessor = 0;
    std::uint64_t worstFirst = 0;
    for (std::uint64_t time = 0; time < clock; ++time) {
      if (orbit[time] <= orbit[clock]) continue;
      const std::uint64_t successor = orbit[time] + 1;
      const std::uint64_t first =
          successor < firstOccurrence.size()
              ? firstOccurrence[successor]
              : unset;
      if (first == unset || first > cutoff || successor > cutoff) {
        coverage = false;
      }
      if (first == unset || first > worstFirst) {
        worstFirst = first;
        worstSuccessor = successor;
      }
    }

    if (coverage) {
      ++covered;
    } else if (firstUncoveredClock == unset) {
      firstUncoveredClock = clock;
    }

    std::cout << clock << "," << orbit[clock] << "," << worstSuccessor
              << ",";
    if (worstFirst == unset)
      std::cout << "unseen";
    else
      std::cout << worstFirst;
    std::cout << "," << (coverage ? "yes" : "no") << "\n";
  }

  std::cout << "eligible=" << eligible << " covered=" << covered
            << " firstUncoveredClock=";
  if (firstUncoveredClock == unset)
    std::cout << "none";
  else
    std::cout << firstUncoveredClock;
  std::cout << "\n";
}
