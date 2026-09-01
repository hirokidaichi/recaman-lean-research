// Candidate-reuse probe for the actual standard Recamán orbit.
//
// The branch-A "burst stream" theory posits a hypothetical recurring
// candidate value c whose use at clock m demands that c + m be visited by
// clock m+1.  The hypothetical branch is unobservable, but the real orbit
// does reuse forced-addition candidate values, so one exact pass measures
// the empirical structure of real candidate reuse:
//
//   Metric 1  per-value use lists: every forced addition at clock m+1 with
//             positive visited candidate v = a(m) - (m+1) counts as a use
//             of v at clock m.  Values used once live in a compact
//             first-use map; the second use promotes the value to a full
//             use-clock list.
//   Metric 2  use-gap ratios: for values with >= 3 uses, histograms of the
//             consecutive use-clock ratios m2/m1 and m3/m2 (first three
//             uses) plus all consecutive pairs, in buckets <1.1, 1.1-1.5,
//             1.5-2, 2-3, 3-10, >10.  A self-supply lattice predicts
//             doubling-like ratios; generic reuse predicts small ratios.
//   Metric 3  successor demand: a use of v at clock m makes the step at
//             m+1 a forced addition, so a(m+1) = a(m) + (m+1) and the next
//             candidate is w = a(m+1) - (m+2) = a(m) - 1 = v + m.  Per
//             decade of m, the fraction of exposed w already visited at
//             clock m+1 (equivalently, a second consecutive forced
//             addition, conditioned on positive-candidate reuse).
//   Metric 4  birth-clock halving: for each exposed visited w, its first
//             occurrence clock j is classified j < w/2, w/2 <= j < w, or
//             j >= w, per decade of m, together with whether the birth
//             step at clock j was a subtraction or an addition.  The burst
//             theory's addition-birth halving predicts j < ~w/2 for
//             addition-born values.
//   Metric 5  the ten most reused values: value, use count, first and last
//             use clocks, first occurrence clock.
//
// Decades bucket the use clock m (decade k holds 10^k <= m < 10^{k+1};
// decade 0 also holds m < 10).
//
// Usage: candidate_reuse_probe [horizon]

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {

using Clock = std::uint32_t;
using Value = std::uint64_t;
using Count = std::uint64_t;

constexpr Clock kNoClock = std::numeric_limits<Clock>::max();
constexpr std::size_t kMaxDecades = 12U;
constexpr std::size_t kRatioBuckets = 6U;
constexpr std::size_t kTopValues = 10U;

constexpr Value kKnownPrefix[16] = {1U,  3U,  6U,  2U,  7U, 13U, 20U, 12U,
                                    21U, 11U, 22U, 10U, 23U, 9U, 24U, 8U};

const char* const kRatioBucketNames[kRatioBuckets] = {
    "<1.1", "1.1-1.5", "1.5-2", "2-3", "3-10", ">10"};

class DenseBits {
 public:
  bool Contains(Value value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < words_.size() &&
           ((words_[word] >> (value & 63U)) & 1ULL) != 0U;
  }

  void Insert(Value value) {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    if (word >= words_.size()) {
      std::size_t grown = words_.empty() ? 1024U : words_.size();
      while (grown <= word) grown += grown / 2U + 1U;
      words_.resize(grown, 0U);
    }
    words_[word] |= 1ULL << (value & 63U);
  }

  std::size_t Bytes() const { return words_.size() * sizeof(std::uint64_t); }

 private:
  std::vector<std::uint64_t> words_;
};

class DenseFirstClock {
 public:
  Clock Lookup(Value value) const {
    const std::size_t index = static_cast<std::size_t>(value);
    return index < first_.size() ? first_[index] : kNoClock;
  }

  void Record(Value value, Clock clock) {
    const std::size_t index = static_cast<std::size_t>(value);
    if (index >= first_.size()) {
      std::size_t grown = first_.empty() ? 1024U : first_.size();
      while (grown <= index) grown += grown / 2U + 1U;
      first_.resize(grown, kNoClock);
    }
    if (first_[index] == kNoClock) first_[index] = clock;
  }

  std::size_t Bytes() const { return first_.size() * sizeof(Clock); }

 private:
  std::vector<Clock> first_;
};

struct RatioHistogram {
  std::array<Count, kRatioBuckets> buckets{};

  void Add(double ratio) {
    std::size_t index = kRatioBuckets - 1U;
    if (ratio < 1.1) {
      index = 0U;
    } else if (ratio < 1.5) {
      index = 1U;
    } else if (ratio < 2.0) {
      index = 2U;
    } else if (ratio < 3.0) {
      index = 3U;
    } else if (ratio < 10.0) {
      index = 4U;
    }
    ++buckets[index];
  }

  Count Total() const {
    Count total = 0U;
    for (const Count bucket : buckets) total += bucket;
    return total;
  }
};

struct UseDecade {
  Count uses = 0U;
  Count exposed_visited = 0U;
  Count birth_lt_half = 0U;
  Count birth_half_to_w = 0U;
  Count birth_ge_w = 0U;
  Count addition_born = 0U;
  Count subtraction_born = 0U;
};

struct TopValue {
  Value value = 0U;
  Count uses = 0U;
  Clock first_use = 0U;
  Clock last_use = 0U;
  Clock first_occurrence = 0U;
};

Clock ParseClock(const char* text) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed == 0U || parsed > 2000000000ULL)
    throw std::invalid_argument("horizon must be in 1..2,000,000,000");
  return static_cast<Clock>(parsed);
}

double Fraction(Count part, Count whole) {
  return whole == 0U ? 0.0
                     : static_cast<double>(part) / static_cast<double>(whole);
}

void PrintRatioHistogram(const char* label, const RatioHistogram& histogram) {
  const Count total = histogram.Total();
  std::cout << "metric2 " << label << " pairs=" << total;
  for (std::size_t index = 0U; index < kRatioBuckets; ++index) {
    std::cout << ' ' << kRatioBucketNames[index] << ':'
              << histogram.buckets[index] << '(' << std::fixed
              << std::setprecision(4)
              << Fraction(histogram.buckets[index], total) << std::defaultfloat
              << ')';
  }
  std::cout << '\n';
}

void AnalyzeCandidateReuse(Clock horizon) {
  const auto started = std::chrono::steady_clock::now();

  DenseBits seen;
  seen.Insert(0U);
  DenseFirstClock first_clock;
  first_clock.Record(0U, 0U);
  DenseBits addition_born;

  std::unordered_map<Value, Clock> single_use;
  std::unordered_map<Value, std::vector<Clock>> multi_use;
  single_use.reserve(static_cast<std::size_t>(horizon) / 3U + 1024U);
  multi_use.reserve(static_cast<std::size_t>(horizon) / 24U + 1024U);

  Value value = 0U, maximum_value = 0U;
  Count additions = 0U, subtractions = 0U, uses_total = 0U;
  std::array<UseDecade, kMaxDecades> use_decades{};
  Count birth_cross[2][3] = {{0U, 0U, 0U}, {0U, 0U, 0U}};

  std::size_t use_decade = 0U;
  Count use_decade_threshold = 10U;

  for (Count raw = 1U; raw <= horizon; ++raw) {
    const Count use_clock = raw - 1U;
    if (use_clock >= use_decade_threshold) {
      ++use_decade;
      use_decade_threshold *= 10U;
    }

    const bool positive = value > raw;
    const Value candidate = positive ? value - raw : 0U;
    const bool subtraction = positive && !seen.Contains(candidate);

    bool used = false;
    Value exposed = 0U;
    if (subtraction) {
      ++subtractions;
      value = candidate;
    } else {
      ++additions;
      if (positive) {
        used = true;
        ++uses_total;
        exposed = value - 1U;  // v + m = a(m) - 1: the next candidate.
        auto repeated = multi_use.find(candidate);
        if (repeated != multi_use.end()) {
          repeated->second.push_back(static_cast<Clock>(use_clock));
        } else {
          auto single = single_use.find(candidate);
          if (single == single_use.end()) {
            single_use.emplace(candidate, static_cast<Clock>(use_clock));
          } else {
            std::vector<Clock> clocks{single->second,
                                      static_cast<Clock>(use_clock)};
            multi_use.emplace(candidate, std::move(clocks));
            single_use.erase(single);
          }
        }
      }
      value += raw;
    }

    maximum_value = std::max(maximum_value, value);
    if (!seen.Contains(value)) {
      seen.Insert(value);
      first_clock.Record(value, static_cast<Clock>(raw));
      if (!subtraction) addition_born.Insert(value);
    }

    if (raw <= 16U && value != kKnownPrefix[raw - 1U])
      throw std::runtime_error("known prefix mismatch");

    if (used) {
      UseDecade& decade = use_decades[use_decade];
      ++decade.uses;
      if (seen.Contains(exposed)) {  // a(m+1) != w, so timing is harmless.
        ++decade.exposed_visited;
        const Count birth = first_clock.Lookup(exposed);
        if (birth == kNoClock)
          throw std::runtime_error("visited exposed value missing birth");
        const bool by_addition = addition_born.Contains(exposed);
        if (by_addition) {
          ++decade.addition_born;
        } else {
          ++decade.subtraction_born;
        }
        std::size_t birth_class = 2U;
        if (2U * birth < exposed) {
          birth_class = 0U;
          ++decade.birth_lt_half;
        } else if (birth < exposed) {
          birth_class = 1U;
          ++decade.birth_half_to_w;
        } else {
          ++decade.birth_ge_w;
        }
        ++birth_cross[by_addition ? 1U : 0U][birth_class];
      }
    }
  }

  const auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - started);

  std::cout << "candidate-reuse horizon=" << horizon
            << " elapsedMs=" << elapsed.count() << '\n';
  std::cout << "  finalValue=" << value << " maxValue=" << maximum_value
            << " seenMB=" << seen.Bytes() / (1024U * 1024U)
            << " firstClockMB=" << first_clock.Bytes() / (1024U * 1024U)
            << " birthTypeMB=" << addition_born.Bytes() / (1024U * 1024U)
            << '\n';
  std::cout << "  steps: additions=" << additions
            << " subtractions=" << subtractions
            << " positiveBlockedUses=" << uses_total << '\n';

  Count multi_max_uses = 0U;
  Count values_three_plus = 0U;
  std::vector<Count> use_count_histogram;
  auto count_uses = [&](Count uses) {
    if (uses >= use_count_histogram.size())
      use_count_histogram.resize(uses + 1U, 0U);
    ++use_count_histogram[uses];
  };
  for (const auto& [reused, clocks] : multi_use) {
    (void)reused;
    count_uses(clocks.size());
    multi_max_uses = std::max<Count>(multi_max_uses, clocks.size());
    if (clocks.size() >= 3U) ++values_three_plus;
  }
  std::cout << "metric1 distinctUsedValues="
            << single_use.size() + multi_use.size()
            << " singleUse=" << single_use.size()
            << " multiUse=" << multi_use.size()
            << " threePlusUse=" << values_three_plus
            << " maxUses=" << multi_max_uses << '\n';
  std::cout << "metric1 useCountHistogram (uses:values) 1:"
            << single_use.size();
  for (std::size_t uses = 2U; uses < use_count_histogram.size(); ++uses)
    if (use_count_histogram[uses] != 0U)
      std::cout << ' ' << uses << ':' << use_count_histogram[uses];
  std::cout << '\n';

  RatioHistogram ratio_21, ratio_32, ratio_all;
  for (const auto& [reused, clocks] : multi_use) {
    (void)reused;
    if (clocks.size() < 3U) continue;
    ratio_21.Add(static_cast<double>(clocks[1]) /
                 static_cast<double>(clocks[0]));
    ratio_32.Add(static_cast<double>(clocks[2]) /
                 static_cast<double>(clocks[1]));
    for (std::size_t index = 1U; index < clocks.size(); ++index)
      ratio_all.Add(static_cast<double>(clocks[index]) /
                    static_cast<double>(clocks[index - 1U]));
  }
  PrintRatioHistogram("ratio m2/m1 (>=3 uses)", ratio_21);
  PrintRatioHistogram("ratio m3/m2 (>=3 uses)", ratio_32);
  PrintRatioHistogram("ratio all consecutive (>=3 uses)", ratio_all);

  Count uses_sum = 0U, visited_sum = 0U;
  for (std::size_t index = 0U; index < kMaxDecades; ++index) {
    const UseDecade& decade = use_decades[index];
    if (decade.uses == 0U) continue;
    uses_sum += decade.uses;
    visited_sum += decade.exposed_visited;
    std::cout << "metric3 decade=" << index << " uses=" << decade.uses
              << " exposedVisited=" << decade.exposed_visited
              << " continuationFrac=" << std::fixed << std::setprecision(6)
              << Fraction(decade.exposed_visited, decade.uses)
              << std::defaultfloat << '\n';
  }
  std::cout << "metric3 overall uses=" << uses_sum
            << " exposedVisited=" << visited_sum
            << " continuationFrac=" << std::fixed << std::setprecision(6)
            << Fraction(visited_sum, uses_sum) << std::defaultfloat << '\n';

  for (std::size_t index = 0U; index < kMaxDecades; ++index) {
    const UseDecade& decade = use_decades[index];
    if (decade.exposed_visited == 0U) continue;
    std::cout << "metric4 decade=" << index << " exposedVisited="
              << decade.exposed_visited << " birthLtHalf=" << std::fixed
              << std::setprecision(6)
              << Fraction(decade.birth_lt_half, decade.exposed_visited)
              << " birthHalfToW="
              << Fraction(decade.birth_half_to_w, decade.exposed_visited)
              << " birthGeW="
              << Fraction(decade.birth_ge_w, decade.exposed_visited)
              << std::defaultfloat << " subBorn=" << decade.subtraction_born
              << " addBorn=" << decade.addition_born << '\n';
  }
  for (std::size_t born = 0U; born < 2U; ++born) {
    const Count row_total = birth_cross[born][0] + birth_cross[born][1] +
                            birth_cross[born][2];
    std::cout << "metric4 overall " << (born == 1U ? "addBorn" : "subBorn")
              << "=" << row_total;
    if (row_total != 0U) {
      std::cout << " birthLtHalf=" << std::fixed << std::setprecision(6)
                << Fraction(birth_cross[born][0], row_total)
                << " birthHalfToW=" << Fraction(birth_cross[born][1], row_total)
                << " birthGeW=" << Fraction(birth_cross[born][2], row_total)
                << std::defaultfloat;
    }
    std::cout << '\n';
  }

  std::vector<TopValue> top;
  top.reserve(multi_use.size());
  for (const auto& [reused, clocks] : multi_use) {
    top.push_back(TopValue{reused, clocks.size(), clocks.front(),
                           clocks.back(), first_clock.Lookup(reused)});
  }
  const std::size_t shown = std::min<std::size_t>(top.size(), kTopValues);
  std::partial_sort(top.begin(), top.begin() + static_cast<std::ptrdiff_t>(shown),
                    top.end(), [](const TopValue& left, const TopValue& right) {
                      if (left.uses != right.uses) return left.uses > right.uses;
                      return left.value < right.value;
                    });
  std::cout << "metric5 topReused (value,uses,firstUse,lastUse,firstOccur):";
  for (std::size_t index = 0U; index < shown; ++index) {
    const TopValue& entry = top[index];
    std::cout << " (" << entry.value << ',' << entry.uses << ','
              << entry.first_use << ',' << entry.last_use << ','
              << entry.first_occurrence << ')';
  }
  std::cout << '\n';
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Clock horizon = argc >= 2 ? ParseClock(argv[1]) : 100000000U;
    AnalyzeCandidateReuse(horizon);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
