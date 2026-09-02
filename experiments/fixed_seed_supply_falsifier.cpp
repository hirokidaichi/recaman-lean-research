// Fixed-seed falsifier for the burst-stream supply conjecture.
//
// This program has two independent discovery passes.
//
//  (1) Replay the canonical seed through a frozen horizon and look for chains
//      of the same positive low candidate c.  Each counted use must be entered
//      by subtraction, emit three additions, have c+m born after the seed and
//      by time m+1, and have d(t)>t at every strict interior time between uses.
//
//  (2) Synthesize finite candidate-return words on the three burst supply
//      lattices n=2m+2, 3m+4, 4m+7.  Every proposed word is replayed with the
//      exact greedy rule from one fixed finite State.  An addition candidate
//      not produced earlier is put in the seed, but a counted demand may not
//      be.  This makes the principal obstruction directly observable: a
//      future addition blocker placed in the seed can make an earlier planned
//      subtraction illegal.
//
// A finite success is a countermodel only to a finite local deficit claim.
// A finite failure is not a proof that no infinite fixed-seed stream exists.
//
// Usage:
//   fixed_seed_supply_falsifier [canonical_horizon] [random_trials_per_depth]

// Frozen defaults: canonical_horizon=2,000,000, trials=4,096, RNG seed
// 20260901.  Depths 2, 3, and 4 are sampled separately; depth 1 also receives
// a deterministic exhaustive parameter pass over m0=4..256 and c=1..32.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <optional>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {

using Nat = std::uint64_t;

constexpr Nat kDefaultCanonicalHorizon = 2000000U;
constexpr Nat kDefaultTrials = 4096U;
constexpr Nat kRandomSeed = 20260901U;
constexpr Nat kMaxSynthesisClock = 100000U;
constexpr Nat kExtendedDiagnosticHorizon = 1000000U;

struct FixedSeed {
  Nat boundary = 0U;
  Nat value = 0U;
  std::vector<Nat> seen;
  Nat candidate = 0U;
  std::vector<Nat> planned_uses;
  Nat planned_end = 0U;
};

enum class Failure {
  kNone,
  kNoReturnWord,
  kClockFailure,
  kSeedSubtractionCollision,
  kHistorySubtractionCollision,
  kMissingAdditionBlocker,
  kPreloadedDemand,
  kLateDemand,
  kUseShape,
  kInadmissibleDensity,
  kInadmissibleHeight,
};

// When set, a synthesized seed must satisfy the two canonical history
// invariants `valuesThrough_length` and `a_le_upperTri`: at most
// boundary + 1 distinct values, all at most boundary * (boundary + 1) / 2.
bool g_canonical_density = false;

// Smallest observed excess |seen| - (boundary + 1) over all synthesized
// plans, with the plan that attains it, reported in canonical-density mode.
struct DensityExcess {
  bool found = false;
  Nat excess = 0U;
  Nat seed_size = 0U;
  Nat boundary = 0U;
  Nat candidate = 0U;
  std::size_t depth = 0U;
};
DensityExcess g_density_excess;

const char* FailureName(Failure failure) {
  switch (failure) {
    case Failure::kNone:
      return "exact";
    case Failure::kNoReturnWord:
      return "no_return_word";
    case Failure::kClockFailure:
      return "clock_or_floor_failure";
    case Failure::kSeedSubtractionCollision:
      return "seed_subtraction_collision";
    case Failure::kHistorySubtractionCollision:
      return "history_subtraction_collision";
    case Failure::kMissingAdditionBlocker:
      return "missing_addition_blocker";
    case Failure::kPreloadedDemand:
      return "preloaded_counted_demand";
    case Failure::kLateDemand:
      return "late_or_absent_counted_demand";
    case Failure::kUseShape:
      return "use_shape_failure";
    case Failure::kInadmissibleDensity:
      return "inadmissible_history_density";
    case Failure::kInadmissibleHeight:
      return "inadmissible_history_height";
  }
  return "unknown";
}

Nat ParseBound(const char* text, Nat lower, Nat upper, const char* name) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed < lower || parsed > upper) {
    throw std::invalid_argument(std::string(name) + " must lie in " +
                                std::to_string(lower) + ".." +
                                std::to_string(upper));
  }
  return static_cast<Nat>(parsed);
}

Nat SumInterval(Nat first, Nat last) {
  if (first > last) return 0U;
  const Nat count = last - first + 1U;
  if ((count & 1U) == 0U) return (count / 2U) * (first + last);
  return count * ((first + last) / 2U);
}

Nat SumFirst(Nat first, Nat count) {
  if (count == 0U) return 0U;
  return SumInterval(first, first + count - 1U);
}

Nat Candidate(Nat time, Nat value) {
  const Nat clock = time + 1U;
  return clock < value ? value - clock : 0U;
}

Nat BurstLattice(Nat m, std::size_t lattice) {
  if (lattice == 0U) return 2U * m + 2U;
  if (lattice == 1U) return 3U * m + 4U;
  return 4U * m + 7U;
}

struct ReturnWord {
  std::vector<unsigned char> addition;
};

bool CheckReturnWord(Nat m, Nat c, const ReturnWord& word) {
  Nat d = c;
  const Nat length = static_cast<Nat>(word.addition.size());
  if (length < 3U || word.addition[0] == 0U ||
      word.addition[1] == 0U || word.addition[2] == 0U) {
    return false;
  }
  for (Nat offset = 0U; offset < length; ++offset) {
    const Nat time = m + offset;
    if (word.addition[static_cast<std::size_t>(offset)] != 0U) {
      d += time;
    } else {
      if (d < time + 2U) return false;
      d -= time + 2U;
    }
    if (offset + 1U < length && d <= time + 1U) return false;
  }
  return d == c;
}

std::vector<Nat> FeasibleCardinalities(Nat m, Nat n) {
  if (n <= m + 2U) return {};
  const Nat length = n - m;
  const Nat rhs = SumInterval(m + 1U, n) + length;
  if ((rhs & 1U) != 0U) return {};
  const Nat target = rhs / 2U;
  std::vector<Nat> result;
  for (Nat count = 3U; count <= length; ++count) {
    if (count > std::numeric_limits<Nat>::max() / (m + 1U)) break;
    const Nat base = count * (m + 1U);
    if (target < base + 3U) continue;
    const Nat remaining = count - 3U;
    const Nat residual = target - base - 3U;
    const Nat minimum = SumFirst(3U, remaining);
    const Nat maximum = remaining == 0U
                            ? 0U
                            : SumInterval(length - remaining, length - 1U);
    if (minimum <= residual && residual <= maximum) result.push_back(count);
  }
  return result;
}

std::optional<ReturnWord> PrefixHeavyReturnWord(Nat m, Nat n, Nat c) {
  const Nat length = n - m;
  const Nat rhs = SumInterval(m + 1U, n) + length;
  if ((rhs & 1U) != 0U) return std::nullopt;
  const Nat target = rhs / 2U;
  for (const Nat count : FeasibleCardinalities(m, n)) {
    std::vector<Nat> indices(static_cast<std::size_t>(count));
    for (Nat index = 0U; index < count; ++index) {
      indices[static_cast<std::size_t>(index)] = index;
    }
    const Nat minimum = count * (m + 1U) +
                        count * (count - 1U) / 2U;
    Nat delta = target - minimum;
    for (Nat index = count; index-- > 3U;) {
      const Nat maximum = index + 1U < count
                              ? indices[static_cast<std::size_t>(index + 1U)] -
                                    1U
                              : length - 1U;
      const Nat current = indices[static_cast<std::size_t>(index)];
      const Nat shift = std::min(delta, maximum - current);
      indices[static_cast<std::size_t>(index)] += shift;
      delta -= shift;
    }
    if (delta != 0U) continue;
    ReturnWord word{std::vector<unsigned char>(
        static_cast<std::size_t>(length), 0U)};
    for (const Nat index : indices) {
      word.addition[static_cast<std::size_t>(index)] = 1U;
    }
    if (CheckReturnWord(m, c, word)) return word;
  }
  return std::nullopt;
}

std::optional<ReturnWord> RandomReturnWord(Nat m, Nat n, Nat c,
                                           std::mt19937_64& generator) {
  const Nat length = n - m;
  const Nat rhs = SumInterval(m + 1U, n) + length;
  if ((rhs & 1U) != 0U) return std::nullopt;
  const Nat target = rhs / 2U;
  const std::vector<Nat> feasible = FeasibleCardinalities(m, n);
  if (feasible.empty()) return std::nullopt;

  for (Nat retry = 0U; retry < 32U; ++retry) {
    const Nat count = feasible[static_cast<std::size_t>(
        generator() % static_cast<Nat>(feasible.size()))];
    const Nat remaining_count = count - 3U;
    Nat residual = target - count * (m + 1U) - 3U;
    Nat lower = 3U;
    std::vector<Nat> indices{0U, 1U, 2U};
    bool failed = false;
    for (Nat chosen = 0U; chosen < remaining_count; ++chosen) {
      const Nat remaining = remaining_count - chosen - 1U;
      const Nat maximum_remaining =
          remaining == 0U
              ? 0U
              : SumInterval(length - remaining, length - 1U);
      const Nat lower_from_sum = residual > maximum_remaining
                                     ? residual - maximum_remaining
                                     : 0U;
      const Nat constant = remaining * (remaining + 1U) / 2U;
      const Nat upper_from_sum =
          (residual - constant) / (remaining + 1U);
      const Nat upper_from_slots = length - remaining - 1U;
      const Nat choice_lower = std::max(lower, lower_from_sum);
      const Nat choice_upper = std::min(upper_from_sum, upper_from_slots);
      if (choice_lower > choice_upper) {
        failed = true;
        break;
      }
      const Nat choice = choice_lower +
                         generator() % (choice_upper - choice_lower + 1U);
      indices.push_back(choice);
      residual -= choice;
      lower = choice + 1U;
    }
    if (failed || residual != 0U) continue;
    ReturnWord word{std::vector<unsigned char>(
        static_cast<std::size_t>(length), 0U)};
    for (const Nat index : indices) {
      word.addition[static_cast<std::size_t>(index)] = 1U;
    }
    if (CheckReturnWord(m, c, word)) return word;
  }
  return std::nullopt;
}

struct SynthesisResult {
  Failure failure = Failure::kNone;
  Nat failure_time = 0U;
  Nat failure_candidate = 0U;
  std::optional<FixedSeed> seed;
  std::vector<std::pair<Nat, Nat>> demand_births;
};

SynthesisResult Synthesize(const std::vector<Nat>& uses, Nat c,
                           const std::vector<ReturnWord>& words) {
  if (uses.size() != words.size() + 1U || uses.empty()) {
    throw std::logic_error("invalid synthesis shape");
  }
  const Nat boundary = uses.front() - 1U;
  const Nat last_use = uses.back();
  const Nat final_pre_time = last_use + 2U;
  std::vector<unsigned char> intended(
      static_cast<std::size_t>(final_pre_time - boundary + 1U), 0U);
  intended[0] = static_cast<unsigned char>('S');
  for (std::size_t interval = 0U; interval < words.size(); ++interval) {
    const Nat m = uses[interval];
    const Nat n = uses[interval + 1U];
    if (words[interval].addition.size() !=
        static_cast<std::size_t>(n - m)) {
      throw std::logic_error("wrong return-word length");
    }
    for (Nat offset = 0U; offset < n - m; ++offset) {
      intended[static_cast<std::size_t>(m + offset - boundary)] =
          words[interval].addition[static_cast<std::size_t>(offset)] != 0U
              ? static_cast<unsigned char>('A')
              : static_cast<unsigned char>('S');
    }
  }
  for (Nat time = last_use; time <= last_use + 2U; ++time) {
    intended[static_cast<std::size_t>(time - boundary)] =
        static_cast<unsigned char>('A');
  }

  const Nat start_value = c + 2U * uses.front() + 1U;
  std::vector<Nat> values(intended.size() + 1U, 0U);
  std::vector<Nat> candidates(intended.size(), 0U);
  values[0] = start_value;
  std::unordered_map<Nat, Nat> planned_first;
  planned_first.emplace(start_value, boundary);
  for (std::size_t index = 0U; index < intended.size(); ++index) {
    const Nat time = boundary + static_cast<Nat>(index);
    const Nat clock = time + 1U;
    const Nat value = values[index];
    candidates[index] = Candidate(time, value);
    if (intended[index] == static_cast<unsigned char>('S')) {
      if (value < clock) {
        return {Failure::kClockFailure, time, candidates[index],
                std::nullopt, {}};
      }
      values[index + 1U] = value - clock;
    } else {
      values[index + 1U] = value + clock;
    }
    planned_first.emplace(values[index + 1U], time + 1U);
  }

  std::set<Nat> initial{0U, start_value};
  for (std::size_t index = 0U; index < intended.size(); ++index) {
    if (intended[index] != static_cast<unsigned char>('A')) continue;
    const Nat time = boundary + static_cast<Nat>(index);
    const Nat candidate = candidates[index];
    const auto first = planned_first.find(candidate);
    if (first == planned_first.end() || first->second > time) {
      initial.insert(candidate);
    }
  }

  if (g_canonical_density) {
    const Nat upper_tri = boundary * (boundary + 1U) / 2U;
    const Nat seed_size = static_cast<Nat>(initial.size());
    if (seed_size > boundary + 1U) {
      const Nat excess = seed_size - (boundary + 1U);
      if (!g_density_excess.found || excess < g_density_excess.excess) {
        g_density_excess = DensityExcess{true, excess, seed_size, boundary,
                                         c, words.size()};
      }
      return {Failure::kInadmissibleDensity, boundary, seed_size,
              std::nullopt, {}};
    }
    if (*initial.rbegin() > upper_tri) {
      return {Failure::kInadmissibleHeight, boundary, *initial.rbegin(),
              std::nullopt, {}};
    }
  }

  for (std::size_t index = 1U; index < uses.size(); ++index) {
    const Nat demand = c + uses[index];
    if (initial.find(demand) != initial.end()) {
      return {Failure::kPreloadedDemand, uses[index], demand,
              std::nullopt, {}};
    }
  }

  std::unordered_map<Nat, Nat> first;
  first.reserve(initial.size() + intended.size() * 2U + 1U);
  for (const Nat value : initial) first.emplace(value, boundary);
  Nat value = start_value;
  std::vector<Nat> actual_candidates(intended.size() + 1U, 0U);
  std::vector<unsigned char> actual_signs(intended.size() + 1U, 0U);
  for (std::size_t index = 0U; index < intended.size(); ++index) {
    const Nat time = boundary + static_cast<Nat>(index);
    const Nat clock = time + 1U;
    const Nat candidate = Candidate(time, value);
    actual_candidates[index] = candidate;
    const bool positive = clock < value;
    const auto occurrence = first.find(candidate);
    const bool seen = occurrence != first.end();
    const bool subtract = positive && !seen;
    const unsigned char actual = subtract ? static_cast<unsigned char>('S')
                                          : static_cast<unsigned char>('A');
    actual_signs[index] = actual;
    if (actual != intended[index]) {
      Failure failure = Failure::kMissingAdditionBlocker;
      if (intended[index] == static_cast<unsigned char>('S')) {
        if (!positive) {
          failure = Failure::kClockFailure;
        } else if (initial.find(candidate) != initial.end()) {
          failure = Failure::kSeedSubtractionCollision;
        } else {
          failure = Failure::kHistorySubtractionCollision;
        }
      }
      return {failure, time, candidate, std::nullopt, {}};
    }
    value = subtract ? value - clock : value + clock;
    first.emplace(value, time + 1U);
  }
  actual_candidates[intended.size()] =
      Candidate(final_pre_time + 1U, value);

  std::vector<std::pair<Nat, Nat>> births;
  for (std::size_t use_index = 0U; use_index < uses.size(); ++use_index) {
    const Nat use = uses[use_index];
    const std::size_t state_index =
        static_cast<std::size_t>(use - boundary);
    if (state_index == 0U ||
        actual_signs[state_index - 1U] != static_cast<unsigned char>('S') ||
        actual_candidates[state_index] != c || c == 0U || c > use ||
        actual_signs[state_index] != static_cast<unsigned char>('A') ||
        actual_signs[state_index + 1U] != static_cast<unsigned char>('A') ||
        actual_signs[state_index + 2U] != static_cast<unsigned char>('A')) {
      return {Failure::kUseShape, use, actual_candidates[state_index],
              std::nullopt, {}};
    }
    if (use_index == 0U) continue;
    const Nat demand = c + use;
    const auto occurrence = first.find(demand);
    if (occurrence == first.end() || occurrence->second <= boundary ||
        occurrence->second > use + 1U) {
      return {Failure::kLateDemand, use, demand, std::nullopt, {}};
    }
    births.emplace_back(use, occurrence->second);
  }

  FixedSeed seed;
  seed.boundary = boundary;
  seed.value = start_value;
  seed.seen.assign(initial.begin(), initial.end());
  seed.candidate = c;
  seed.planned_uses.assign(uses.begin() + 1, uses.end());
  seed.planned_end = last_use + 3U;
  return {Failure::kNone, 0U, 0U, seed, births};
}

struct EventScan {
  Nat qualifying = 0U;
  Nat valid_links = 0U;
  Nat max_chain = 0U;
  std::optional<Nat> first_nonhigh_after_plan;
  std::vector<std::pair<Nat, Nat>> events;
};

EventScan ScanOneCandidate(const FixedSeed& seed, Nat horizon) {
  if (horizon <= seed.boundary + 3U) return {};
  const Nat simulation_end = horizon + 3U;
  std::unordered_map<Nat, Nat> first;
  first.reserve(seed.seen.size() +
                static_cast<std::size_t>(simulation_end - seed.boundary) *
                    2U);
  for (const Nat seeded : seed.seen) first.emplace(seeded, seed.boundary);
  Nat value = seed.value;
  const std::size_t span =
      static_cast<std::size_t>(simulation_end - seed.boundary + 1U);
  std::vector<Nat> candidates(span, 0U);
  std::vector<unsigned char> signs(span + 1U, 0U);
  for (Nat clock = seed.boundary + 1U; clock <= simulation_end; ++clock) {
    const Nat time = clock - 1U;
    const std::size_t index =
        static_cast<std::size_t>(time - seed.boundary);
    const Nat candidate = Candidate(time, value);
    candidates[index] = candidate;
    const bool subtract = clock < value && first.find(candidate) == first.end();
    signs[static_cast<std::size_t>(clock - seed.boundary)] =
        subtract ? static_cast<unsigned char>('S')
                 : static_cast<unsigned char>('A');
    value = subtract ? value - clock : value + clock;
    first.emplace(value, clock);
  }

  EventScan result;
  Nat last_bad = seed.boundary;
  std::optional<Nat> previous;
  Nat chain = 0U;
  for (Nat m = seed.boundary + 1U; m <= horizon; ++m) {
    const std::size_t state_index =
        static_cast<std::size_t>(m - seed.boundary);
    const std::size_t clock_index = state_index;
    const Nat c = candidates[state_index];
    bool qualifies = false;
    Nat birth = 0U;
    if (c == seed.candidate && 0U < c && c <= m &&
        signs[clock_index] == static_cast<unsigned char>('S') &&
        signs[clock_index + 1U] == static_cast<unsigned char>('A') &&
        signs[clock_index + 2U] == static_cast<unsigned char>('A') &&
        signs[clock_index + 3U] == static_cast<unsigned char>('A')) {
      const auto occurrence = first.find(c + m);
      if (occurrence != first.end() && seed.boundary < occurrence->second &&
          occurrence->second <= m + 1U) {
        qualifies = true;
        birth = occurrence->second;
      }
    }
    if (qualifies) {
      ++result.qualifying;
      result.events.emplace_back(m, birth);
      if (previous.has_value() && last_bad <= *previous) {
        ++result.valid_links;
        ++chain;
      } else {
        chain = 1U;
      }
      previous = m;
      result.max_chain = std::max(result.max_chain, chain);
    }
    if (candidates[state_index] <= m) {
      last_bad = m;
      if (m > seed.planned_end &&
          !result.first_nonhigh_after_plan.has_value()) {
        result.first_nonhigh_after_plan = m;
      }
    }
  }
  return result;
}

struct CanonicalScan {
  Nat low_entries = 0U;
  Nat burst_entries = 0U;
  Nat internal_demands = 0U;
  Nat valid_links = 0U;
  Nat max_chain = 0U;
  Nat distinct_candidates = 0U;
};

CanonicalScan ScanCanonical(Nat horizon) {
  const Nat simulation_end = horizon + 3U;
  std::unordered_map<Nat, Nat> first;
  first.reserve(static_cast<std::size_t>(simulation_end) * 2U);
  first.emplace(0U, 0U);
  Nat value = 0U;
  std::vector<Nat> candidates(
      static_cast<std::size_t>(simulation_end + 1U), 0U);
  std::vector<unsigned char> signs(
      static_cast<std::size_t>(simulation_end + 1U), 0U);
  for (Nat clock = 1U; clock <= simulation_end; ++clock) {
    const Nat time = clock - 1U;
    const Nat candidate = Candidate(time, value);
    candidates[static_cast<std::size_t>(time)] = candidate;
    const bool subtract = clock < value && first.find(candidate) == first.end();
    signs[static_cast<std::size_t>(clock)] =
        subtract ? static_cast<unsigned char>('S')
                 : static_cast<unsigned char>('A');
    value = subtract ? value - clock : value + clock;
    first.emplace(value, clock);
  }

  struct ChainState {
    Nat previous = 0U;
    Nat chain = 0U;
    bool has_previous = false;
  };
  std::unordered_map<Nat, ChainState> chains;
  Nat last_bad = 0U;
  CanonicalScan result;
  for (Nat m = 1U; m <= horizon; ++m) {
    const Nat c = candidates[static_cast<std::size_t>(m)];
    const bool low_entry = 0U < c && c <= m &&
                           signs[static_cast<std::size_t>(m)] ==
                               static_cast<unsigned char>('S');
    if (low_entry) {
      ++result.low_entries;
      const bool burst =
          signs[static_cast<std::size_t>(m + 1U)] ==
              static_cast<unsigned char>('A') &&
          signs[static_cast<std::size_t>(m + 2U)] ==
              static_cast<unsigned char>('A') &&
          signs[static_cast<std::size_t>(m + 3U)] ==
              static_cast<unsigned char>('A');
      if (burst) {
        ++result.burst_entries;
        const auto occurrence = first.find(c + m);
        if (occurrence != first.end() && 0U < occurrence->second &&
            occurrence->second <= m + 1U) {
          ++result.internal_demands;
          ChainState& state = chains[c];
          if (state.has_previous && last_bad <= state.previous) {
            ++result.valid_links;
            ++state.chain;
          } else {
            state.chain = 1U;
          }
          state.previous = m;
          state.has_previous = true;
          result.max_chain = std::max(result.max_chain, state.chain);
        }
      }
    }
    if (candidates[static_cast<std::size_t>(m)] <= m) last_bad = m;
  }
  result.distinct_candidates = static_cast<Nat>(chains.size());
  return result;
}

void PrintSeed(const FixedSeed& seed) {
  Nat fingerprint = 1469598103934665603ULL;
  const auto mix = [&fingerprint](Nat value) {
    fingerprint ^= value;
    fingerprint *= 1099511628211ULL;
  };
  mix(seed.boundary);
  mix(seed.value);
  mix(seed.candidate);
  for (const Nat value : seed.seen) mix(value);
  std::cout << "best fixedSeed boundary=" << seed.boundary
            << " value=" << seed.value << " c=" << seed.candidate
            << " seedSize=" << seed.seen.size()
            << " fingerprint=" << fingerprint
            << " bootstrapUse=" << seed.boundary + 1U << " seenFirst=";
  const std::size_t first_limit =
      std::min<std::size_t>(seed.seen.size(), 12U);
  for (std::size_t index = 0U; index < first_limit; ++index) {
    if (index != 0U) std::cout << ',';
    std::cout << seed.seen[index];
  }
  std::cout << " seenLast=";
  const std::size_t last_start =
      seed.seen.size() > 12U ? seed.seen.size() - 12U : 0U;
  for (std::size_t index = last_start; index < seed.seen.size(); ++index) {
    if (index != last_start) std::cout << ',';
    std::cout << seed.seen[index];
  }
  std::cout << " plannedCountedUses=";
  for (std::size_t index = 0U; index < seed.planned_uses.size(); ++index) {
    if (index != 0U) std::cout << ',';
    std::cout << seed.planned_uses[index];
  }
  std::cout << '\n';
}

void PrintEventScan(const char* label, Nat horizon, const EventScan& scan) {
  std::cout << label << " horizon=" << horizon
            << " qualifyingUses=" << scan.qualifying
            << " strictHighLinks=" << scan.valid_links
            << " maxChain=" << scan.max_chain
            << " firstNonHighAfterPlan=";
  if (scan.first_nonhigh_after_plan.has_value()) {
    std::cout << *scan.first_nonhigh_after_plan;
  } else {
    std::cout << "none";
  }
  std::cout << " events=";
  const std::size_t limit = std::min<std::size_t>(scan.events.size(), 12U);
  for (std::size_t index = 0U; index < limit; ++index) {
    if (index != 0U) std::cout << ',';
    std::cout << scan.events[index].first << "@birth"
              << scan.events[index].second;
  }
  if (scan.events.size() > limit) std::cout << ",...";
  std::cout << '\n';
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Nat canonical_horizon =
        argc >= 2 ? ParseBound(argv[1], 1000U, 10000000U,
                               "canonical_horizon")
                  : kDefaultCanonicalHorizon;
    const Nat trials =
        argc >= 3 ? ParseBound(argv[2], 1U, 1000000U,
                               "random_trials_per_depth")
                  : kDefaultTrials;
    g_canonical_density =
        argc >= 4 && ParseBound(argv[3], 0U, 1U, "canonical_density") == 1U;
    if (g_canonical_density) {
      std::cout << "seed admissibility=canonical_density"
                   " (|seen| <= boundary+1, max seen <= upperTri boundary)\n";
    }

    const CanonicalScan canonical = ScanCanonical(canonical_horizon);
    std::cout << "canonical discovery horizon=" << canonical_horizon
              << " lowEntryUses=" << canonical.low_entries
              << " threeAdditionBursts=" << canonical.burst_entries
              << " internalDemandUses=" << canonical.internal_demands
              << " distinctCandidates=" << canonical.distinct_candidates
              << " strictHighLinks=" << canonical.valid_links
              << " maxChain=" << canonical.max_chain << '\n';

    std::map<Failure, Nat> deterministic_census;
    std::optional<FixedSeed> best_seed;
    std::vector<std::pair<Nat, Nat>> best_births;
    for (Nat m = 4U; m <= 256U; ++m) {
      for (Nat c = 1U; c <= std::min<Nat>(32U, m); ++c) {
        for (std::size_t lattice = 0U; lattice < 3U; ++lattice) {
          const Nat n = BurstLattice(m, lattice);
          const auto word = PrefixHeavyReturnWord(m, n, c);
          if (!word.has_value()) {
            ++deterministic_census[Failure::kNoReturnWord];
            continue;
          }
          const SynthesisResult result = Synthesize({m, n}, c, {*word});
          ++deterministic_census[result.failure];
          if (result.seed.has_value() &&
              (!best_seed.has_value() ||
               result.seed->planned_uses.size() >
                   best_seed->planned_uses.size())) {
            best_seed = result.seed;
            best_births = result.demand_births;
          }
        }
      }
    }

    std::cout << "synthesis deterministic depth=1 cases=";
    Nat deterministic_total = 0U;
    for (const auto& [failure, count] : deterministic_census) {
      deterministic_total += count;
      std::cout << FailureName(failure) << ':' << count << ' ';
    }
    std::cout << "total:" << deterministic_total << '\n';

    std::mt19937_64 generator(kRandomSeed);
    for (Nat depth = 2U; depth <= 4U; ++depth) {
      std::map<Failure, Nat> census;
      for (Nat trial = 0U; trial < trials; ++trial) {
        const Nat m0 = 4U + generator() % 253U;
        const Nat c = 1U + generator() % std::min<Nat>(32U, m0);
        std::vector<Nat> uses{m0};
        std::vector<ReturnWord> words;
        Failure failure = Failure::kNone;
        for (Nat interval = 0U; interval < depth; ++interval) {
          const Nat m = uses.back();
          const Nat n = BurstLattice(m,
                                     static_cast<std::size_t>(generator() % 3U));
          if (n > kMaxSynthesisClock) {
            failure = Failure::kNoReturnWord;
            break;
          }
          const auto word = RandomReturnWord(m, n, c, generator);
          if (!word.has_value()) {
            failure = Failure::kNoReturnWord;
            break;
          }
          uses.push_back(n);
          words.push_back(*word);
        }
        if (failure != Failure::kNone) {
          ++census[failure];
          continue;
        }
        const SynthesisResult result = Synthesize(uses, c, words);
        ++census[result.failure];
        if (result.seed.has_value() &&
            (!best_seed.has_value() ||
             result.seed->planned_uses.size() >
                 best_seed->planned_uses.size())) {
          best_seed = result.seed;
          best_births = result.demand_births;
        }
      }
      std::cout << "synthesis random depth=" << depth
                << " rngSeed=" << kRandomSeed << " trials=" << trials
                << ' ';
      for (const auto& [failure, count] : census) {
        std::cout << FailureName(failure) << ':' << count << ' ';
      }
      std::cout << '\n';
    }

    if (g_canonical_density) {
      std::cout << "density excess min=";
      if (g_density_excess.found) {
        std::cout << g_density_excess.excess
                  << " seedSize=" << g_density_excess.seed_size
                  << " boundary=" << g_density_excess.boundary
                  << " c=" << g_density_excess.candidate
                  << " intervals=" << g_density_excess.depth;
      } else {
        std::cout << "none";
      }
      std::cout << '\n';
    }

    if (!best_seed.has_value()) {
      std::cout << "best fixedSeed none\n";
      return EXIT_SUCCESS;
    }

    PrintSeed(*best_seed);
    std::cout << "best demandBirths=";
    for (std::size_t index = 0U; index < best_births.size(); ++index) {
      if (index != 0U) std::cout << ',';
      std::cout << best_births[index].first << "<-"
                << best_births[index].second;
    }
    std::cout << '\n';

    const Nat holdout_horizon =
        std::min<Nat>(10000000U, 10U * best_seed->planned_end);
    PrintEventScan("frozen holdout", holdout_horizon,
                   ScanOneCandidate(*best_seed, holdout_horizon));
    const Nat diagnostic_horizon =
        std::max(holdout_horizon, kExtendedDiagnosticHorizon);
    PrintEventScan("extended diagnostic", diagnostic_horizon,
                   ScanOneCandidate(*best_seed, diagnostic_horizon));
    std::cout << "interpretation finite computation only; no infinite "
                 "fixed-seed claim proved or refuted\n";
    return EXIT_SUCCESS;
  } catch (const std::exception& error) {
    std::cerr << "fixed_seed_supply_falsifier error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
}
