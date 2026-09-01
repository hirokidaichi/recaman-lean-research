// Search arbitrary finite-history Recaman states for an upward reset that is
// not a global right record.  A witness shows exactly which full-orbit
// provenance assumptions are missing from the local target-comb laws.

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <limits>
#include <random>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

namespace {

using Clock = std::uint32_t;
using Value = std::uint64_t;

struct Step {
  Clock clock = 0U;
  Value old_value = 0U;
  Value new_value = 0U;
  Value old_mex = 0U;
  Value new_mex = 0U;
  bool subtraction = false;
};

struct Chain {
  Value target = 0U;
  Clock start = 0U;
  Clock end = 0U;
  Value entry = 0U;
  Value blocker = 0U;
};

struct ActiveChain {
  enum class Phase : std::uint8_t { expect_add, expect_resolution };

  Value target = 0U;
  Clock start = 0U;
  Value entry = 0U;
  Value landing = 0U;
  Phase phase = Phase::expect_add;
};

struct TargetState {
  Chain previous{};
  bool has_previous = false;
  Value maximum_upper = 0U;
};

struct Witness {
  std::uint64_t seed_mask = 0U;
  Value initial_value = 0U;
  Clock next_clock = 0U;
  Chain previous{};
  Chain next{};
  Value prior_upper = 0U;
  Clock blocker_first = 0U;
  bool blocker_first_subtraction = false;
  Value blocker_first_predecessor = 0U;
  std::vector<Step> trace;
};

struct ReturnStats {
  std::uint64_t seeds = 0U;
  std::uint64_t seeds_with_witness = 0U;
  std::uint64_t witnesses = 0U;
  std::uint64_t witness_origin_addition = 0U;
  std::uint64_t witness_origin_subtraction = 0U;
  std::uint64_t witness_origin_seed = 0U;
  std::uint64_t returned = 0U;
  std::uint64_t returned_addition_origin = 0U;
  std::uint64_t returned_subtraction_origin = 0U;
  std::uint64_t returned_seed_origin = 0U;
  std::uint64_t censored = 0U;
  std::uint64_t censored_addition_origin = 0U;
  std::uint64_t censored_subtraction_origin = 0U;
  std::uint64_t censored_seed_origin = 0U;
  std::uint64_t delay_sum = 0U;
  Clock maximum_delay = 0U;
  Value maximum_delay_target = 0U;
  Clock maximum_delay_witness_clock = 0U;
  Clock maximum_delay_return_clock = 0U;
  Clock maximum_addition_delay = 0U;
  Value maximum_addition_delay_target = 0U;
  Clock maximum_addition_delay_witness_clock = 0U;
  Clock maximum_addition_delay_return_clock = 0U;
  Value first_censored_target = 0U;
  Clock first_censored_witness_clock = 0U;
  Value first_censored_previous_blocker = 0U;
  Value first_censored_next_blocker = 0U;
  Value first_censored_prior_upper = 0U;
};

Clock ParseClock(const char* text) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed == 0U || parsed > std::numeric_limits<Clock>::max()) {
    throw std::invalid_argument("positive uint32 argument required");
  }
  return static_cast<Clock>(parsed);
}

bool Contains(const std::vector<std::uint64_t>& seen, Value value) {
  const std::size_t word = static_cast<std::size_t>(value >> 6U);
  return word < seen.size() &&
         ((seen[word] >> (value & 63U)) & 1ULL) != 0U;
}

void Insert(std::vector<std::uint64_t>& seen, Value value) {
  const std::size_t word = static_cast<std::size_t>(value >> 6U);
  if (word >= seen.size()) {
    seen.resize(word + 1U, 0U);
  }
  seen[word] |= 1ULL << (value & 63U);
}

Value Mex(const std::vector<std::uint64_t>& seen) {
  Value value = 0U;
  while (Contains(seen, value)) {
    ++value;
  }
  return value;
}

bool LowCandidateSide(Value value, Clock next_clock, Value target) {
  return value <= next_clock || value - next_clock < target;
}

bool Simulate(std::uint64_t seed_mask, Value initial_value,
              Clock next_clock, Clock steps, bool require_addition_origin,
              Witness& witness,
              bool require_record_subtraction_origin = false) {
  std::vector<std::uint64_t> seen(1U, seed_mask);
  Value value = initial_value;
  Value mex = Mex(seen);
  ActiveChain active;
  bool chain_active = false;
  std::unordered_map<Value, TargetState> states;
  std::unordered_map<Value, std::tuple<Clock, bool, Value>> origins;
  std::vector<Step> trace;
  trace.reserve(steps);

  auto finish_chain = [&](Clock clock, bool target_terminated,
                          Value blocker) {
    const Chain chain{active.target, active.start, clock, active.entry,
                      blocker};
    TargetState& state = states[chain.target];
    if (target_terminated) {
      state = TargetState{};
    } else if (state.has_previous &&
               state.previous.blocker < chain.blocker) {
      const auto origin = origins.find(chain.blocker);
      const bool origin_is_subtraction =
          origin != origins.end() && std::get<1>(origin->second);
      const bool acceptable = require_record_subtraction_origin
          ? state.maximum_upper <= chain.blocker && origin_is_subtraction
          : chain.blocker < state.maximum_upper &&
              (!require_addition_origin ||
                (origin != origins.end() && !origin_is_subtraction));
      if (acceptable) {
        const Clock first =
            origin == origins.end() ? 0U : std::get<0>(origin->second);
        const bool first_subtraction =
            origin != origins.end() && std::get<1>(origin->second);
        const Value first_predecessor =
            origin == origins.end() ? 0U : std::get<2>(origin->second);
        witness = Witness{seed_mask, initial_value, next_clock,
                          state.previous, chain, state.maximum_upper,
                          first, first_subtraction, first_predecessor, trace};
        chain_active = false;
        return true;
      }
      state.maximum_upper = std::max(state.maximum_upper, chain.entry);
      state.previous = chain;
    } else if (!target_terminated) {
      state.maximum_upper = state.has_previous
                                ? std::max(state.maximum_upper, chain.entry)
                                : chain.entry;
      state.previous = chain;
      state.has_previous = true;
    }
    chain_active = false;
    return false;
  };

  for (std::uint64_t offset = 0U; offset < steps; ++offset) {
    const std::uint64_t raw_clock =
        static_cast<std::uint64_t>(next_clock) + offset;
    if (raw_clock > std::numeric_limits<Clock>::max()) {
      break;
    }
    const Clock clock = static_cast<Clock>(raw_clock);
    const Value old_value = value;
    const Value old_mex = mex;
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool subtraction = positive && !Contains(seen, candidate);
    if (!subtraction && value >
                            std::numeric_limits<Value>::max() - clock) {
      break;
    }
    const Value next_value = subtraction ? candidate : value + clock;
    const bool next_was_seen = Contains(seen, next_value);

    if (chain_active) {
      if (active.phase == ActiveChain::Phase::expect_add) {
        if (subtraction) {
          chain_active = false;
        } else {
          active.phase = ActiveChain::Phase::expect_resolution;
        }
      } else if (subtraction) {
        if (next_value + 1U != active.landing) {
          chain_active = false;
        } else {
          active.landing = next_value;
          active.phase = ActiveChain::Phase::expect_add;
        }
      } else if (finish_chain(clock, false, active.landing - 1U)) {
        witness.trace.push_back(
            Step{clock, old_value, next_value, old_mex, old_mex,
                 subtraction});
        return true;
      }
    }

    value = next_value;
    if (!next_was_seen) {
      origins.emplace(value,
                      std::tuple<Clock, bool, Value>{clock, subtraction,
                                                     old_value});
    }
    Insert(seen, value);
    while (Contains(seen, mex)) {
      ++mex;
    }
    trace.push_back(Step{clock, old_value, value, old_mex, mex,
                         subtraction});

    if (chain_active && mex != old_mex &&
        finish_chain(clock, true, old_mex)) {
      return true;
    }

    if (!chain_active && subtraction && mex == old_mex && value > mex &&
        LowCandidateSide(value, static_cast<Clock>(clock + 1U), mex)) {
      active = ActiveChain{mex, clock, value, value,
                           ActiveChain::Phase::expect_add};
      chain_active = true;
    }
  }
  return false;
}

ReturnStats SimulateReturns(const std::vector<std::uint64_t>& seed_seen,
                            Value initial_value, Clock next_clock,
                            Clock steps,
                            bool stop_after_first_witness_return = false) {
  std::vector<std::uint64_t> seen = seed_seen;
  std::vector<std::uint64_t> first_addition;
  std::vector<std::uint64_t> first_subtraction;
  Value value = initial_value;
  Value mex = Mex(seen);
  ActiveChain active;
  bool chain_active = false;
  TargetState state;
  std::vector<Clock> pending_witnesses;
  std::vector<char> pending_origins;
  Value pending_target = 0U;
  Value pending_previous_blocker = 0U;
  Value pending_next_blocker = 0U;
  Value pending_prior_upper = 0U;
  bool seed_has_witness = false;
  ReturnStats result;
  result.seeds = 1U;

  auto finish_chain = [&](Clock clock, bool target_terminated,
                          Value blocker) {
    const Chain chain{active.target, active.start, clock, active.entry,
                      blocker};
    if (target_terminated) {
      state = TargetState{};
    } else {
      if (state.has_previous && state.previous.blocker < chain.blocker &&
          chain.blocker < state.maximum_upper) {
        ++result.witnesses;
        const char origin = Contains(first_addition, chain.blocker)
                                ? 'A'
                                : (Contains(first_subtraction, chain.blocker)
                                       ? 'S'
                                       : 'H');
        if (origin == 'A') {
          ++result.witness_origin_addition;
        } else if (origin == 'S') {
          ++result.witness_origin_subtraction;
        } else {
          ++result.witness_origin_seed;
        }
        seed_has_witness = true;
        if (pending_witnesses.empty()) {
          pending_target = chain.target;
          pending_previous_blocker = state.previous.blocker;
          pending_next_blocker = chain.blocker;
          pending_prior_upper = state.maximum_upper;
        } else if (pending_target != chain.target) {
          throw std::runtime_error("pending RLR witnesses changed target");
        }
        pending_witnesses.push_back(clock);
        pending_origins.push_back(origin);
      }
      state.maximum_upper = state.has_previous
                                ? std::max(state.maximum_upper, chain.entry)
                                : chain.entry;
      state.previous = chain;
      state.has_previous = true;
    }
    chain_active = false;
  };

  for (std::uint64_t offset = 0U; offset < steps; ++offset) {
    const std::uint64_t raw_clock =
        static_cast<std::uint64_t>(next_clock) + offset;
    if (raw_clock > std::numeric_limits<Clock>::max()) {
      break;
    }
    const Clock clock = static_cast<Clock>(raw_clock);
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool subtraction = positive && !Contains(seen, candidate);
    if (!subtraction &&
        value > std::numeric_limits<Value>::max() - clock) {
      break;
    }
    const Value old_mex = mex;
    const Value next_value = subtraction ? candidate : value + clock;
    const bool next_was_seen = Contains(seen, next_value);

    if (chain_active) {
      if (active.phase == ActiveChain::Phase::expect_add) {
        if (subtraction) {
          chain_active = false;
        } else {
          active.phase = ActiveChain::Phase::expect_resolution;
        }
      } else if (subtraction) {
        if (next_value + 1U != active.landing) {
          chain_active = false;
        } else {
          active.landing = next_value;
          active.phase = ActiveChain::Phase::expect_add;
        }
      } else {
        finish_chain(clock, false, active.landing - 1U);
      }
    }

    value = next_value;
    if (!next_was_seen) {
      Insert(subtraction ? first_subtraction : first_addition, value);
    }
    Insert(seen, value);
    while (Contains(seen, mex)) {
      ++mex;
    }

    if (chain_active && mex != old_mex) {
      finish_chain(clock, true, old_mex);
    }

    if (mex != old_mex && !pending_witnesses.empty()) {
      if (pending_target != old_mex) {
        throw std::runtime_error("RLR target did not match old mex");
      }
      for (std::size_t index = 0U; index < pending_witnesses.size();
           ++index) {
        const Clock witness_clock = pending_witnesses[index];
        const Clock delay = static_cast<Clock>(clock - witness_clock);
        ++result.returned;
        if (pending_origins[index] == 'A') {
          ++result.returned_addition_origin;
          if (result.maximum_addition_delay < delay) {
            result.maximum_addition_delay = delay;
            result.maximum_addition_delay_target = old_mex;
            result.maximum_addition_delay_witness_clock = witness_clock;
            result.maximum_addition_delay_return_clock = clock;
          }
        } else if (pending_origins[index] == 'S') {
          ++result.returned_subtraction_origin;
        } else {
          ++result.returned_seed_origin;
        }
        result.delay_sum += delay;
        if (result.maximum_delay < delay) {
          result.maximum_delay = delay;
          result.maximum_delay_target = old_mex;
          result.maximum_delay_witness_clock = witness_clock;
          result.maximum_delay_return_clock = clock;
        }
      }
      pending_witnesses.clear();
      pending_origins.clear();
      if (stop_after_first_witness_return) {
        break;
      }
    }

    if (!chain_active && subtraction && mex == old_mex && value > mex &&
        LowCandidateSide(value, static_cast<Clock>(clock + 1U), mex)) {
      active = ActiveChain{mex, clock, value, value,
                           ActiveChain::Phase::expect_add};
      chain_active = true;
    }
  }

  result.censored = pending_witnesses.size();
  for (char origin : pending_origins) {
    if (origin == 'A') {
      ++result.censored_addition_origin;
    } else if (origin == 'S') {
      ++result.censored_subtraction_origin;
    } else {
      ++result.censored_seed_origin;
    }
  }
  if (!pending_witnesses.empty()) {
    result.first_censored_target = pending_target;
    result.first_censored_witness_clock = pending_witnesses.front();
    result.first_censored_previous_blocker = pending_previous_blocker;
    result.first_censored_next_blocker = pending_next_blocker;
    result.first_censored_prior_upper = pending_prior_upper;
  }
  result.seeds_with_witness = seed_has_witness ? 1U : 0U;
  return result;
}

void MergeReturnStats(ReturnStats& total, const ReturnStats& next) {
  total.seeds += next.seeds;
  total.seeds_with_witness += next.seeds_with_witness;
  total.witnesses += next.witnesses;
  total.witness_origin_addition += next.witness_origin_addition;
  total.witness_origin_subtraction += next.witness_origin_subtraction;
  total.witness_origin_seed += next.witness_origin_seed;
  total.returned += next.returned;
  total.returned_addition_origin += next.returned_addition_origin;
  total.returned_subtraction_origin += next.returned_subtraction_origin;
  total.returned_seed_origin += next.returned_seed_origin;
  total.censored += next.censored;
  total.censored_addition_origin += next.censored_addition_origin;
  total.censored_subtraction_origin += next.censored_subtraction_origin;
  total.censored_seed_origin += next.censored_seed_origin;
  total.delay_sum += next.delay_sum;
  if (total.maximum_delay < next.maximum_delay) {
    total.maximum_delay = next.maximum_delay;
    total.maximum_delay_target = next.maximum_delay_target;
    total.maximum_delay_witness_clock = next.maximum_delay_witness_clock;
    total.maximum_delay_return_clock = next.maximum_delay_return_clock;
  }
  if (total.maximum_addition_delay < next.maximum_addition_delay) {
    total.maximum_addition_delay = next.maximum_addition_delay;
    total.maximum_addition_delay_target =
        next.maximum_addition_delay_target;
    total.maximum_addition_delay_witness_clock =
        next.maximum_addition_delay_witness_clock;
    total.maximum_addition_delay_return_clock =
        next.maximum_addition_delay_return_clock;
  }
}

void PrintReturnStats(const char* label, Clock steps,
                      const ReturnStats& stats) {
  std::cout << label << " steps=" << steps << " seeds=" << stats.seeds
            << " seedsWithRLR=" << stats.seeds_with_witness
            << " witnesses=" << stats.witnesses
            << " origin(add/sub/seed)=" << stats.witness_origin_addition
            << '/' << stats.witness_origin_subtraction << '/'
            << stats.witness_origin_seed
            << " returned=" << stats.returned
            << " returnedByOrigin(add/sub/seed)="
            << stats.returned_addition_origin << '/'
            << stats.returned_subtraction_origin << '/'
            << stats.returned_seed_origin
            << " censored=" << stats.censored
            << " censoredByOrigin(add/sub/seed)="
            << stats.censored_addition_origin << '/'
            << stats.censored_subtraction_origin << '/'
            << stats.censored_seed_origin;
  if (stats.returned != 0U) {
    std::cout << " averageDelay=" << stats.delay_sum / stats.returned
              << " maximumDelay=" << stats.maximum_delay
              << " maxWitness=(target=" << stats.maximum_delay_target
              << ",witness=" << stats.maximum_delay_witness_clock
              << ",return=" << stats.maximum_delay_return_clock << ')';
  }
  if (stats.returned_addition_origin != 0U) {
    std::cout << " maximumAdditionDelay=" << stats.maximum_addition_delay
              << " maxAdditionWitness=(target="
              << stats.maximum_addition_delay_target << ",witness="
              << stats.maximum_addition_delay_witness_clock << ",return="
              << stats.maximum_addition_delay_return_clock << ')';
  }
  std::cout << '\n';
}

void PrintWitness(const Witness& witness, Clock seed_limit) {
  std::cout << "seeded upward-reset witness\n  seen={";
  bool first = true;
  for (Value value = 0U; value < seed_limit; ++value) {
    if (((witness.seed_mask >> value) & 1ULL) == 0U) {
      continue;
    }
    std::cout << (first ? "" : ",") << value;
    first = false;
  }
  std::cout << "} current=" << witness.initial_value
            << " nextClock=" << witness.next_clock << '\n';
  std::cout << "  previous=(m=" << witness.previous.target
            << ",clocks=[" << witness.previous.start << ','
            << witness.previous.end << "],interval=["
            << witness.previous.blocker + 1U << ','
            << witness.previous.entry << "],blocker="
            << witness.previous.blocker << ")\n";
  std::cout << "  next=(m=" << witness.next.target << ",clocks=["
            << witness.next.start << ',' << witness.next.end
            << "],interval=[" << witness.next.blocker + 1U << ','
            << witness.next.entry << "],blocker=" << witness.next.blocker
            << ") priorUpper=" << witness.prior_upper << '\n';
  std::cout << "  nextBlockerOrigin=";
  if (witness.blocker_first == 0U) {
    std::cout << "seed";
  } else {
    std::cout << (witness.blocker_first_subtraction ? "sub" : "add")
              << '@' << witness.blocker_first << " predecessor="
              << witness.blocker_first_predecessor;
  }
  std::cout << '\n';
  std::cout << "  trace:\n";
  for (const Step& step : witness.trace) {
    std::cout << "    n=" << step.clock << ' ' << step.old_value
              << (step.subtraction ? " - " : " + ") << step.clock
              << " -> " << step.new_value << " mex=" << step.old_mex
              << "->" << step.new_mex << '\n';
  }
}

void Search(Clock seed_limit, Clock max_next_clock, Clock steps) {
  if (seed_limit < 2U || seed_limit > 24U) {
    throw std::invalid_argument("seedLimit must be in 2..24");
  }
  const std::uint64_t masks = 1ULL << seed_limit;
  std::uint64_t states = 0U;
  for (std::uint64_t mask = 1U; mask < masks; mask += 2U) {
    const Clock distinct = static_cast<Clock>(__builtin_popcountll(mask));
    Value largest_seed_value = 0U;
    for (Value candidate = 0U; candidate < seed_limit; ++candidate) {
      if (((mask >> candidate) & 1ULL) != 0U) {
        largest_seed_value = candidate;
      }
    }
    for (Value current = 0U; current < seed_limit; ++current) {
      if (((mask >> current) & 1ULL) == 0U) {
        continue;
      }
      for (Clock next_clock = 1U; next_clock <= max_next_clock;
           ++next_clock) {
        // Necessary (but very far from sufficient) conditions for a genuine
        // prefix of length next_clock-1: at most next_clock visited values,
        // no value beyond the all-addition triangular bound, and the current
        // value has the forced parity of 1+...+(next_clock-1).
        const Value previous_clock = static_cast<Value>(next_clock - 1U);
        const Value triangular = previous_clock * (previous_clock + 1U) / 2U;
        if (distinct > next_clock || largest_seed_value > triangular ||
            ((current ^ triangular) & 1U) != 0U) {
          continue;
        }
        ++states;
        Witness witness;
        if (Simulate(mask, current, next_clock, steps, false, witness)) {
          std::cout << "searchedStates=" << states << '\n';
          PrintWitness(witness, seed_limit);
          return;
        }
      }
    }
  }
  std::cout << "no witness after searchedStates=" << states << '\n';
}

void SearchSignedWalks(Clock max_next_clock, Clock steps,
                       bool require_addition_origin,
                       bool require_record_subtraction_origin = false) {
  if (max_next_clock < 2U || max_next_clock > 12U) {
    throw std::invalid_argument("walk maxNextClock must be in 2..12");
  }
  std::uint64_t states = 0U;
  for (Clock next_clock = 2U; next_clock <= max_next_clock; ++next_clock) {
    bool found = false;
    std::function<void(Clock, Value, std::uint64_t)> visit =
        [&](Clock clock, Value value, std::uint64_t mask) {
          if (found) {
            return;
          }
          if (clock == next_clock) {
            ++states;
            Witness witness;
            if (Simulate(mask, value, next_clock, steps,
                         require_addition_origin, witness,
                         require_record_subtraction_origin)) {
              std::cout << "signed-walk seed"
                        << (require_addition_origin ? " (addition origin)" : "")
                        << (require_record_subtraction_origin
                              ? " (record subtraction origin)" : "")
                        << " searchedStates=" << states << '\n';
              PrintWitness(witness, 64U);
              found = true;
            }
            return;
          }
          const Value addition = value + clock;
          if (addition < 64U) {
            visit(static_cast<Clock>(clock + 1U), addition,
                  mask | (1ULL << addition));
          }
          if (value > clock) {
            const Value subtraction = value - clock;
            visit(static_cast<Clock>(clock + 1U), subtraction,
                  mask | (1ULL << subtraction));
          }
        };
    visit(1U, 0U, 1ULL);
    if (found) {
      return;
    }
  }
  std::cout << "no signed-walk witness"
            << (require_addition_origin ? " with addition origin" : "")
            << (require_record_subtraction_origin
                  ? " with record subtraction origin" : "")
            << " after searchedStates=" << states << '\n';
}

void AuditReturnGrid(Clock seed_limit, Clock max_next_clock, Clock steps) {
  if (seed_limit < 2U || seed_limit > 20U) {
    throw std::invalid_argument("return-grid seedLimit must be in 2..20");
  }
  const std::uint64_t masks = 1ULL << seed_limit;
  ReturnStats total;
  for (std::uint64_t mask = 1U; mask < masks; mask += 2U) {
    const Clock distinct = static_cast<Clock>(__builtin_popcountll(mask));
    Value largest_seed_value = 0U;
    for (Value candidate = 0U; candidate < seed_limit; ++candidate) {
      if (((mask >> candidate) & 1ULL) != 0U) {
        largest_seed_value = candidate;
      }
    }
    const std::vector<std::uint64_t> seen{mask};
    for (Value current = 0U; current < seed_limit; ++current) {
      if (((mask >> current) & 1ULL) == 0U) {
        continue;
      }
      for (Clock next_clock = 1U; next_clock <= max_next_clock;
           ++next_clock) {
        const Value previous_clock = static_cast<Value>(next_clock - 1U);
        const Value triangular = previous_clock * (previous_clock + 1U) / 2U;
        if (distinct > next_clock || largest_seed_value > triangular ||
            ((current ^ triangular) & 1U) != 0U) {
          continue;
        }
        MergeReturnStats(total,
                         SimulateReturns(seen, current, next_clock, steps));
      }
    }
  }
  PrintReturnStats("return-grid", steps, total);
}

void AuditRandomSignedWalkReturns(std::uint64_t seed_count,
                                  Clock maximum_next_clock, Clock steps,
                                  std::uint64_t random_seed,
                                  Clock censored_followup_steps) {
  if (maximum_next_clock < 3U || maximum_next_clock > 10000U) {
    throw std::invalid_argument(
        "random-walk maxNextClock must be in 3..10000");
  }
  std::mt19937_64 generator(random_seed);
  std::uniform_int_distribution<Clock> clock_distribution(
      3U, maximum_next_clock);
  ReturnStats total;
  std::uint64_t censored_seed_count = 0U;
  for (std::uint64_t sample = 0U; sample < seed_count; ++sample) {
    const Clock next_clock = clock_distribution(generator);
    std::vector<std::uint64_t> seen(1U, 1ULL);
    Value value = 0U;
    for (Clock clock = 1U; clock < next_clock; ++clock) {
      const bool can_subtract = value > clock;
      const bool choose_subtraction = can_subtract &&
                                      ((generator() & 1ULL) != 0U);
      if (choose_subtraction) {
        value = static_cast<Value>(value - clock);
      } else {
        if (value > std::numeric_limits<Value>::max() - clock) {
          throw std::overflow_error("signed-walk seed value overflow");
        }
        value = static_cast<Value>(value + clock);
      }
      Insert(seen, value);
    }
    const ReturnStats outcome =
        SimulateReturns(seen, value, next_clock, steps);
    MergeReturnStats(total, outcome);
    if (outcome.censored != 0U) {
      ++censored_seed_count;
      std::cout << "  censoredSeed sample=" << sample
                << " nextClock=" << next_clock << " current=" << value
                << " target=" << outcome.first_censored_target
                << " witnessClock="
                << outcome.first_censored_witness_clock
                << " blocker=" << outcome.first_censored_previous_blocker
                << "->" << outcome.first_censored_next_blocker
                << " priorUpper=" << outcome.first_censored_prior_upper;
      if (censored_followup_steps > steps) {
        const ReturnStats followup = SimulateReturns(
            seen, value, next_clock, censored_followup_steps);
        std::cout << " followupSteps=" << censored_followup_steps
                  << " followupReturned=" << followup.returned
                  << " followupCensored=" << followup.censored;
        if (followup.returned != 0U) {
          std::cout << " followupMaxDelay=" << followup.maximum_delay
                    << " returnClock="
                    << followup.maximum_delay_return_clock;
        }
      }
      std::cout << '\n';
    }
  }
  PrintReturnStats("return-random-signed-walk", steps, total);
  std::cout << "  censoredSeeds=" << censored_seed_count << '\n';
}

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc >= 2 && std::string(argv[1]) == "--return-seed") {
      if (argc < 6) {
        throw std::invalid_argument(
            "--return-seed current nextClock steps seenValue...");
      }
      const Value current = std::stoull(argv[2]);
      const Clock next_clock = ParseClock(argv[3]);
      const Clock steps = ParseClock(argv[4]);
      std::vector<std::uint64_t> seen;
      for (int index = 5; index < argc; ++index) {
        Insert(seen, std::stoull(argv[index]));
      }
      if (!Contains(seen, current)) {
        throw std::invalid_argument("current must be present in seen values");
      }
      const ReturnStats stats =
          SimulateReturns(seen, current, next_clock, steps, true);
      PrintReturnStats("return-seed", steps, stats);
      return EXIT_SUCCESS;
    }
    if (argc >= 2 && std::string(argv[1]) == "--return-grid") {
      const Clock seed_limit = argc >= 3 ? ParseClock(argv[2]) : 10U;
      const Clock max_next_clock = argc >= 4 ? ParseClock(argv[3]) : 20U;
      const Clock steps = argc >= 5 ? ParseClock(argv[4]) : 10000U;
      AuditReturnGrid(seed_limit, max_next_clock, steps);
      return EXIT_SUCCESS;
    }
    if (argc >= 2 && std::string(argv[1]) == "--return-walks") {
      const std::uint64_t seed_count =
          argc >= 3 ? std::stoull(argv[2]) : 10000U;
      const Clock maximum_next_clock =
          argc >= 4 ? ParseClock(argv[3]) : 80U;
      const Clock steps = argc >= 5 ? ParseClock(argv[4]) : 10000U;
      const std::uint64_t random_seed =
          argc >= 6 ? std::stoull(argv[5]) : 20260831ULL;
      const Clock censored_followup_steps =
          argc >= 7 ? ParseClock(argv[6]) : steps;
      AuditRandomSignedWalkReturns(seed_count, maximum_next_clock, steps,
                                   random_seed, censored_followup_steps);
      return EXIT_SUCCESS;
    }
    if (argc >= 2 &&
        (std::string(argv[1]) == "--walk" ||
         std::string(argv[1]) == "--walk-any" ||
         std::string(argv[1]) == "--walk-record-sub")) {
      const bool require_addition_origin =
          std::string(argv[1]) == "--walk";
      const bool require_record_subtraction_origin =
          std::string(argv[1]) == "--walk-record-sub";
      const Clock max_next_clock = argc >= 3 ? ParseClock(argv[2]) : 12U;
      const Clock steps = argc >= 4 ? ParseClock(argv[3]) : 300U;
      SearchSignedWalks(max_next_clock, steps, require_addition_origin,
                        require_record_subtraction_origin);
      return EXIT_SUCCESS;
    }
    const Clock seed_limit = argc >= 2 ? ParseClock(argv[1]) : 12U;
    const Clock max_next_clock = argc >= 3 ? ParseClock(argv[2]) : 16U;
    const Clock steps = argc >= 4 ? ParseClock(argv[3]) : 160U;
    Search(seed_limit, max_next_clock, steps);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
