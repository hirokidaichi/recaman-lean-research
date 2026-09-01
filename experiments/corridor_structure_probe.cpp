// Corridor-structure probe for the actual standard Recamán orbit.
//
// Branch A of the missing-target kernel (eventual-high-candidate corridor)
// needs the empirical rhythm of the real orbit.  One exact pass measures:
//
//   Metric 1  forced-addition rays: maximal runs of consecutive addition
//             steps, with running maxima checkpointed at 10^6..10^9, the
//             longest runs (start clock, length), and the full run-length
//             histogram at the final horizon.
//   Metric 2  mex-relative cone classes of subtraction landings: a landing
//             v = a(n+1) at clock n+1 is cone-interior when
//             v < (n+2) + m(n) (m = current mex before the step), else
//             cone-exterior; per-decade counts plus the exterior excess
//             v - (n+2) - m(n) distribution (exact min/max, reservoir
//             median).
//   Metric 3  candidate-vs-mex: per decade, how often the positive
//             subtraction candidate d(n) = a(n) - (n+1) sits below, at, or
//             above the current mex ("low candidate" regime frequency).
//   Metric 4  blocked-addition provenance ages: for additions forced by a
//             visited positive candidate, age = n - firstClock(d(n));
//             per-decade blocked counts, reservoir median age, exact max
//             age, and the ancient-reuse fraction (age >= n/2).  Needs a
//             dense first-clock table (~4 bytes per reachable value), so it
//             is disabled by default above 3*10^8 steps.
//
// Decades bucket the acting clock n+1 (decade k holds 10^k <= n+1 < 10^{k+1}).
// Medians marked "~" come from a 65536-slot reservoir sample; unmarked
// medians are exact (the reservoir saw every value).
//
// Usage: corridor_structure_probe [horizon] [track_ages(0|1)]

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
#include <utility>
#include <vector>

namespace {

using Clock = std::uint32_t;
using Value = std::uint64_t;
using Count = std::uint64_t;

constexpr Clock kNoClock = std::numeric_limits<Clock>::max();
constexpr std::size_t kMaxDecades = 12U;
constexpr std::size_t kTopRunCapacity = 64U;

constexpr Value kKnownPrefix[16] = {1U,  3U,  6U,  2U,  7U, 13U, 20U, 12U,
                                    21U, 11U, 22U, 10U, 23U, 9U, 24U, 8U};

class DenseSeen {
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

std::uint64_t NextRandom(std::uint64_t& state) {
  state += 0x9E3779B97F4A7C15ULL;
  std::uint64_t mixed = state;
  mixed = (mixed ^ (mixed >> 30U)) * 0xBF58476D1CE4E5B9ULL;
  mixed = (mixed ^ (mixed >> 27U)) * 0x94D049BB133111EBULL;
  return mixed ^ (mixed >> 31U);
}

class Reservoir {
 public:
  void Offer(Value sample, std::uint64_t& rng) {
    ++offered_;
    if (samples_.size() < kCapacity) {
      samples_.push_back(sample);
      return;
    }
    const std::uint64_t slot = NextRandom(rng) % offered_;
    if (slot < kCapacity) samples_[static_cast<std::size_t>(slot)] = sample;
  }

  bool Empty() const { return samples_.empty(); }
  bool Exact() const { return offered_ <= kCapacity; }

  Value Median() const {
    if (samples_.empty()) return 0U;
    std::vector<Value> sorted = samples_;
    std::sort(sorted.begin(), sorted.end());
    return sorted[(sorted.size() - 1U) / 2U];
  }

 private:
  static constexpr std::size_t kCapacity = 1U << 16U;
  std::vector<Value> samples_;
  Count offered_ = 0U;
};

struct ConeDecade {
  Count landings = 0U;
  Count interior = 0U;
  Count exterior = 0U;
  Value exterior_min = std::numeric_limits<Value>::max();
  Value exterior_max = 0U;
  Reservoir exterior_excess;
};

struct CandidateDecade {
  Count states = 0U;
  Count positive = 0U;
  Count low = 0U;
  Count equal = 0U;
  Count high = 0U;
};

struct AgeDecade {
  Count blocked = 0U;
  Count ancient = 0U;
  Count max_age = 0U;
  Reservoir ages;
};

struct RunRecord {
  Clock start = 0U;
  Count length = 0U;
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

void PrintMedian(const Reservoir& reservoir) {
  if (reservoir.Empty()) {
    std::cout << "median=-";
    return;
  }
  std::cout << "median" << (reservoir.Exact() ? "=" : "~=")
            << reservoir.Median();
}

void AnalyzeCorridorStructure(Clock horizon, bool track_ages) {
  const auto started = std::chrono::steady_clock::now();

  DenseSeen seen;
  seen.Insert(0U);
  DenseFirstClock first_clock;
  if (track_ages) first_clock.Record(0U, 0U);

  Value value = 0U, mex = 1U, maximum_value = 0U;
  std::uint64_t rng = 0x243F6A8885A308D3ULL;

  std::array<ConeDecade, kMaxDecades> cone_decades{};
  std::array<CandidateDecade, kMaxDecades> candidate_decades{};
  std::array<AgeDecade, kMaxDecades> age_decades{};

  const Count checkpoints[4] = {1000000ULL, 10000000ULL, 100000000ULL,
                                1000000000ULL};
  std::vector<std::pair<Count, Count>> checkpoint_maxima;

  Clock run_start = 0U;
  Count run_length = 0U;
  Count max_run = 0U;
  std::vector<Count> histogram;
  std::vector<RunRecord> top_runs;
  Count runs_closed = 0U;
  Count additions = 0U, subtractions = 0U, blocked_total = 0U;

  Count top_minimum = 0U;
  auto close_run = [&]() {
    if (run_length == 0U) return;
    ++runs_closed;
    if (run_length >= histogram.size()) histogram.resize(run_length + 1U, 0U);
    ++histogram[run_length];
    if (top_runs.size() < kTopRunCapacity) {
      top_runs.push_back(RunRecord{run_start, run_length});
      if (top_runs.size() == kTopRunCapacity) {
        top_minimum = std::min_element(
            top_runs.begin(), top_runs.end(),
            [](const RunRecord& left, const RunRecord& right) {
              return left.length < right.length;
            })->length;
      }
    } else if (run_length > top_minimum) {
      auto weakest = std::min_element(
          top_runs.begin(), top_runs.end(),
          [](const RunRecord& left, const RunRecord& right) {
            return left.length < right.length;
          });
      *weakest = RunRecord{run_start, run_length};
      top_minimum = std::min_element(
          top_runs.begin(), top_runs.end(),
          [](const RunRecord& left, const RunRecord& right) {
            return left.length < right.length;
          })->length;
    }
    run_length = 0U;
  };

  std::size_t decade = 0U;
  Count decade_threshold = 10U;
  std::size_t checkpoint_index = 0U;

  for (Count raw = 1U; raw <= horizon; ++raw) {
    if (raw >= decade_threshold) {
      ++decade;
      decade_threshold *= 10U;
    }

    const bool positive = value > raw;
    const Value candidate = positive ? value - raw : 0U;

    CandidateDecade& m3 = candidate_decades[decade];
    ++m3.states;
    if (positive) {
      ++m3.positive;
      if (candidate < mex) {
        ++m3.low;
      } else if (candidate == mex) {
        ++m3.equal;
      } else {
        ++m3.high;
      }
    }

    const bool subtraction = positive && !seen.Contains(candidate);
    if (subtraction) {
      ++subtractions;
      close_run();
      ConeDecade& m2 = cone_decades[decade];
      ++m2.landings;
      const Value cone_bound = raw + 1U + mex;
      if (candidate < cone_bound) {
        ++m2.interior;
      } else {
        ++m2.exterior;
        const Value excess = candidate - cone_bound;
        m2.exterior_min = std::min(m2.exterior_min, excess);
        m2.exterior_max = std::max(m2.exterior_max, excess);
        m2.exterior_excess.Offer(excess, rng);
      }
      value = candidate;
    } else {
      ++additions;
      if (run_length == 0U) run_start = static_cast<Clock>(raw);
      ++run_length;
      max_run = std::max(max_run, run_length);
      if (positive) {
        ++blocked_total;
        AgeDecade& m4 = age_decades[decade];
        ++m4.blocked;
        if (track_ages) {
          const Clock first = first_clock.Lookup(candidate);
          if (first == kNoClock)
            throw std::runtime_error("blocked candidate missing first clock");
          const Count state_time = raw - 1U;
          const Count age = state_time - first;
          if (2U * age >= state_time) ++m4.ancient;
          m4.max_age = std::max(m4.max_age, age);
          m4.ages.Offer(age, rng);
        }
      }
      value += raw;
    }

    maximum_value = std::max(maximum_value, value);
    seen.Insert(value);
    if (track_ages) first_clock.Record(value, static_cast<Clock>(raw));
    while (seen.Contains(mex)) ++mex;

    if (raw <= 16U && value != kKnownPrefix[raw - 1U])
      throw std::runtime_error("known prefix mismatch");

    if (checkpoint_index < 4U && raw == checkpoints[checkpoint_index]) {
      checkpoint_maxima.emplace_back(raw, max_run);
      ++checkpoint_index;
    }
  }

  const Count censored_run = run_length;
  const Clock censored_start = run_start;
  close_run();

  const auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - started);

  std::cout << "corridor-structure horizon=" << horizon
            << " trackAges=" << (track_ages ? 1 : 0)
            << " elapsedMs=" << elapsed.count() << '\n';
  std::cout << "  finalValue=" << value << " finalMex=" << mex
            << " maxValue=" << maximum_value
            << " seenMB=" << seen.Bytes() / (1024U * 1024U)
            << " firstClockMB=" << first_clock.Bytes() / (1024U * 1024U)
            << '\n';
  std::cout << "  steps: additions=" << additions
            << " (blockedPositiveCandidate=" << blocked_total
            << ") subtractions=" << subtractions
            << " additionRuns=" << runs_closed << '\n';

  std::cout << "metric1 maxAdditionRun:";
  for (const auto& [at, maximum] : checkpoint_maxima)
    std::cout << " h=" << at << ":" << maximum;
  std::cout << " final(h=" << horizon << "):" << max_run << '\n';
  if (censored_run != 0U) {
    std::cout << "metric1 censoredFinalRun start=" << censored_start
              << " length=" << censored_run
              << " (closed into histogram/top list)" << '\n';
  }

  std::sort(top_runs.begin(), top_runs.end(),
            [](const RunRecord& left, const RunRecord& right) {
              if (left.length != right.length) return left.length > right.length;
              return left.start < right.start;
            });
  std::cout << "metric1 longestRuns (startClock,length):";
  const std::size_t shown = std::min<std::size_t>(top_runs.size(), 10U);
  for (std::size_t index = 0U; index < shown; ++index)
    std::cout << " (" << top_runs[index].start << ','
              << top_runs[index].length << ')';
  std::cout << '\n';

  std::cout << "metric1 runHistogram (length:count):";
  for (std::size_t length = 1U; length < histogram.size(); ++length)
    if (histogram[length] != 0U)
      std::cout << ' ' << length << ':' << histogram[length];
  std::cout << '\n';

  Count cone_landings = 0U, cone_interior = 0U, cone_exterior = 0U;
  for (std::size_t index = 0U; index < kMaxDecades; ++index) {
    const ConeDecade& m2 = cone_decades[index];
    if (m2.landings == 0U) continue;
    cone_landings += m2.landings;
    cone_interior += m2.interior;
    cone_exterior += m2.exterior;
    std::cout << "metric2 decade=" << index << " landings=" << m2.landings
              << " interior=" << m2.interior << " exterior=" << m2.exterior
              << " exteriorFrac=" << std::fixed << std::setprecision(6)
              << Fraction(m2.exterior, m2.landings) << std::defaultfloat;
    if (m2.exterior != 0U) {
      std::cout << " excess(min=" << m2.exterior_min << ' ';
      PrintMedian(m2.exterior_excess);
      std::cout << " max=" << m2.exterior_max << ')';
    }
    std::cout << '\n';
  }
  std::cout << "metric2 overall landings=" << cone_landings
            << " interior=" << cone_interior << " exterior=" << cone_exterior
            << " exteriorFrac=" << std::fixed << std::setprecision(6)
            << Fraction(cone_exterior, cone_landings) << std::defaultfloat
            << '\n';

  Count states_total = 0U, positive_total = 0U, low_total = 0U;
  for (std::size_t index = 0U; index < kMaxDecades; ++index) {
    const CandidateDecade& m3 = candidate_decades[index];
    if (m3.states == 0U) continue;
    states_total += m3.states;
    positive_total += m3.positive;
    low_total += m3.low;
    std::cout << "metric3 decade=" << index << " states=" << m3.states
              << " positiveCandidate=" << m3.positive << " low=" << m3.low
              << " equal=" << m3.equal << " high=" << m3.high
              << " lowFracOfPositive=" << std::fixed << std::setprecision(6)
              << Fraction(m3.low, m3.positive)
              << " lowFracOfStates=" << Fraction(m3.low, m3.states)
              << std::defaultfloat << '\n';
  }
  std::cout << "metric3 overall states=" << states_total
            << " positiveCandidate=" << positive_total << " low=" << low_total
            << " lowFracOfPositive=" << std::fixed << std::setprecision(6)
            << Fraction(low_total, positive_total) << std::defaultfloat
            << '\n';

  for (std::size_t index = 0U; index < kMaxDecades; ++index) {
    const AgeDecade& m4 = age_decades[index];
    if (m4.blocked == 0U) continue;
    std::cout << "metric4 decade=" << index << " blockedAdds=" << m4.blocked;
    if (track_ages) {
      std::cout << " age(";
      PrintMedian(m4.ages);
      std::cout << " max=" << m4.max_age << ") ancientFrac=" << std::fixed
                << std::setprecision(6) << Fraction(m4.ancient, m4.blocked)
                << std::defaultfloat;
    } else {
      std::cout << " (ages not tracked at this horizon)";
    }
    std::cout << '\n';
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Clock horizon = argc >= 2 ? ParseClock(argv[1]) : 100000000U;
    const bool track_ages = argc >= 3
        ? std::stoull(argv[2]) != 0U
        : horizon <= 300000000U;
    AnalyzeCorridorStructure(horizon, track_ages);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
