// Exact standard-prefix audit of target-relative high-candidate runs.
//
// At state time n the candidate for clock n+1 is
//   c_n = max(a(n) - (n+1), 0).
// Relative to the current mex target it is low, equal, or high.  We measure
// strict-high blocks between strict-low states, and separately retain the
// equality state which visits the target and ends an epoch.

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace {

using Clock = std::uint32_t;
using Value = std::uint64_t;
using Count = std::uint64_t;

class DenseSeen {
 public:
  bool Contains(Value value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < words_.size() &&
           ((words_[word] >> (value & 63U)) & 1ULL) != 0U;
  }

  void Insert(Value value) {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    if (word >= words_.size()) words_.resize(word + 1U, 0U);
    words_[word] |= 1ULL << (value & 63U);
  }

  std::size_t Bytes() const { return words_.size() * sizeof(std::uint64_t); }

 private:
  std::vector<std::uint64_t> words_;
};

enum class Side : std::uint8_t { low, equal, high };

struct TerminalComb {
  Value target = 0U;
  Clock epoch_start = 0U;
  Clock start = 0U;
  Clock end = 0U;
  Value entry = 0U;
  Value blocker = 0U;
};

struct ActiveComb {
  enum class Phase : std::uint8_t { expect_add, expect_resolution };
  Value target = 0U;
  Clock epoch_start = 0U;
  Clock start = 0U;
  Value entry = 0U;
  Value landing = 0U;
  Phase phase = Phase::expect_add;
};

struct EpochStats {
  Value target = 0U;
  Clock start = 0U;
  Clock last_candidate_time = 0U;
  Count candidate_states = 0U;
  Count low = 0U;
  Count equal = 0U;
  Count high = 0U;
  Count adjacent_low_gaps = 0U;
  Count entry_starts = 0U;
  Count history_terminals = 0U;
  Count target_terminations = 0U;
  Count censored_combs = 0U;
  bool saw_low = false;
  Clock current_high = 0U;
  Clock initial_high = 0U;
  Clock suffix_high = 0U;
  std::vector<Clock> inter_low_runs;
  std::vector<Clock> low_offsets;
};

struct RunData {
  std::vector<EpochStats> epochs;
  std::vector<TerminalComb> terminals;
  Value final_value = 0U;
  Value final_mex = 0U;
  Value maximum_value = 0U;
  std::size_t seen_bytes = 0U;
};

struct OriginInfo {
  Clock first = 0U;
  Value parent = 0U;
  Value mex_at_first = 0U;
  bool subtraction = false;
};

Clock ParseClock(const char* text) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed == 0U || parsed > 2000000000ULL)
    throw std::invalid_argument("horizon must be in 1..2,000,000,000");
  return static_cast<Clock>(parsed);
}

Value Candidate(Value value, Clock next_clock) {
  return value > next_clock ? value - next_clock : 0U;
}

Side CandidateSide(Value value, Clock next_clock, Value target) {
  const Value candidate = Candidate(value, next_clock);
  if (candidate < target) return Side::low;
  if (target < candidate) return Side::high;
  return Side::equal;
}

void ObserveCandidate(EpochStats& epoch, Clock state_time, Side side) {
  ++epoch.candidate_states;
  epoch.last_candidate_time = state_time;
  if (side == Side::high) {
    ++epoch.high;
    epoch.current_high = static_cast<Clock>(epoch.current_high + 1U);
    return;
  }
  if (side == Side::equal) {
    ++epoch.equal;
    return;
  }
  ++epoch.low;
  epoch.low_offsets.push_back(
      static_cast<Clock>(state_time - epoch.start));
  if (!epoch.saw_low) {
    epoch.initial_high = epoch.current_high;
    epoch.saw_low = true;
  } else {
    epoch.inter_low_runs.push_back(epoch.current_high);
    if (epoch.current_high == 0U) ++epoch.adjacent_low_gaps;
  }
  epoch.current_high = 0U;
}

void FinishEpoch(EpochStats& epoch) {
  epoch.suffix_high = epoch.current_high;
}

RunData Generate(Clock horizon) {
  DenseSeen seen;
  seen.Insert(0U);
  Value value = 0U, mex = 1U, maximum_value = 0U;
  Clock epoch_start = 0U;
  EpochStats epoch;
  epoch.target = mex;
  epoch.start = epoch_start;
  ActiveComb active;
  bool comb_active = false;
  RunData result;

  auto finish_comb = [&](Clock clock, bool target_terminated, Value blocker) {
    if (target_terminated) {
      ++epoch.target_terminations;
    } else {
      ++epoch.history_terminals;
      result.terminals.push_back(TerminalComb{
          active.target, active.epoch_start, active.start, clock,
          active.entry, blocker});
    }
    comb_active = false;
  };

  for (std::uint64_t raw = 1U; raw <= horizon; ++raw) {
    const Clock clock = static_cast<Clock>(raw);
    const Clock state_time = static_cast<Clock>(clock - 1U);
    ObserveCandidate(epoch, state_time,
                     CandidateSide(value, clock, mex));

    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool subtraction = positive && !seen.Contains(candidate);
    const Value old_mex = mex;
    const Value next_value = subtraction ? candidate : value + clock;

    if (comb_active) {
      if (active.phase == ActiveComb::Phase::expect_add) {
        if (subtraction) throw std::runtime_error("comb expected addition");
        active.phase = ActiveComb::Phase::expect_resolution;
      } else if (subtraction) {
        if (next_value + 1U != active.landing)
          throw std::runtime_error("nonconsecutive comb landing");
        active.landing = next_value;
        active.phase = ActiveComb::Phase::expect_add;
      } else {
        finish_comb(clock, false, active.landing - 1U);
      }
    }

    value = next_value;
    maximum_value = std::max(maximum_value, value);
    seen.Insert(value);
    while (seen.Contains(mex)) ++mex;

    if (comb_active && mex != old_mex)
      finish_comb(clock, true, old_mex);

    if (mex != old_mex) {
      FinishEpoch(epoch);
      result.epochs.push_back(std::move(epoch));
      epoch_start = clock;
      epoch = EpochStats{};
      epoch.target = mex;
      epoch.start = epoch_start;
    }

    if (!comb_active && subtraction && mex == old_mex && value > mex &&
        CandidateSide(value, static_cast<Clock>(clock + 1U), mex) ==
            Side::low) {
      active = ActiveComb{mex, epoch_start, clock, value, value,
                          ActiveComb::Phase::expect_add};
      comb_active = true;
      ++epoch.entry_starts;
    }
  }

  if (comb_active) ++epoch.censored_combs;
  FinishEpoch(epoch);
  result.epochs.push_back(std::move(epoch));
  result.final_value = value;
  result.final_mex = mex;
  result.maximum_value = maximum_value;
  result.seen_bytes = seen.Bytes();
  return result;
}

std::unordered_map<Value, OriginInfo> CollectOrigins(
    Clock horizon, const std::vector<TerminalComb>& terminals) {
  std::unordered_set<Value> requested;
  requested.reserve(terminals.size() * 2U + 1U);
  for (const TerminalComb& terminal : terminals)
    requested.insert(terminal.blocker);
  std::unordered_map<Value, OriginInfo> origins;
  origins.reserve(requested.size() * 2U + 1U);

  DenseSeen seen;
  seen.Insert(0U);
  Value value = 0U, mex = 1U;
  for (std::uint64_t raw = 1U; raw <= horizon; ++raw) {
    const Clock clock = static_cast<Clock>(raw);
    const Value parent = value;
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool subtraction = positive && !seen.Contains(candidate);
    value = subtraction ? candidate : value + clock;
    const bool first = !seen.Contains(value);
    seen.Insert(value);
    while (seen.Contains(mex)) ++mex;
    if (first && requested.find(value) != requested.end()) {
      origins.emplace(value, OriginInfo{clock, parent, mex, subtraction});
    }
  }
  if (origins.size() != requested.size())
    throw std::runtime_error("not all blocker origins were recovered");
  return origins;
}

Clock Percentile(std::vector<Clock> values, std::size_t percentile) {
  if (values.empty()) return 0U;
  std::sort(values.begin(), values.end());
  const std::size_t index = std::min(
      values.size() - 1U, values.size() * percentile / 100U);
  return values[index];
}

Count CountLowInTailFraction(const EpochStats& epoch, Count denominator) {
  if (epoch.candidate_states == 0U) return 0U;
  const Count threshold =
      epoch.candidate_states * (denominator - 1U) / denominator;
  return static_cast<Count>(std::count_if(
      epoch.low_offsets.begin(), epoch.low_offsets.end(),
      [&](Clock offset) { return offset >= threshold; }));
}

Count CountLowInLast(const EpochStats& epoch, Count width) {
  if (epoch.candidate_states == 0U) return 0U;
  const Count threshold = epoch.candidate_states > width
      ? epoch.candidate_states - width
      : 0U;
  return static_cast<Count>(std::count_if(
      epoch.low_offsets.begin(), epoch.low_offsets.end(),
      [&](Clock offset) { return offset >= threshold; }));
}

Clock MaximumObservedRun(const EpochStats& epoch) {
  Clock maximum = std::max(epoch.initial_high, epoch.suffix_high);
  for (Clock run : epoch.inter_low_runs) maximum = std::max(maximum, run);
  return maximum;
}

void PrintEpochs(const RunData& data) {
  Count total_states = 0U, total_low = 0U, total_equal = 0U;
  Count total_high = 0U, total_starts = 0U, total_terminals = 0U;
  Count total_target_terminations = 0U, total_censored = 0U;
  Clock global_maximum_run = 0U;
  std::cout << "high-candidate epochs:\n";
  for (const EpochStats& epoch : data.epochs) {
    total_states += epoch.candidate_states;
    total_low += epoch.low;
    total_equal += epoch.equal;
    total_high += epoch.high;
    total_starts += epoch.entry_starts;
    total_terminals += epoch.history_terminals;
    total_target_terminations += epoch.target_terminations;
    total_censored += epoch.censored_combs;
    global_maximum_run =
        std::max(global_maximum_run, MaximumObservedRun(epoch));
    const Count tail_tenth_low = CountLowInTailFraction(epoch, 10U);
    const Count tail_tenth_size = (epoch.candidate_states + 9U) / 10U;
    const Count last_million_low = CountLowInLast(epoch, 1000000U);
    const Count last_million_size =
        std::min<Count>(epoch.candidate_states, 1000000U);
    std::cout << "  target=" << epoch.target << " start=" << epoch.start
              << " candidateStates=" << epoch.candidate_states
              << " side(low/equal/high)=" << epoch.low << '/'
              << epoch.equal << '/' << epoch.high << " lowPpm="
              << (epoch.candidate_states == 0U
                      ? 0U
                      : epoch.low * 1000000U / epoch.candidate_states)
              << " interLowRuns=" << epoch.inter_low_runs.size()
              << " adjacentLow=" << epoch.adjacent_low_gaps
              << " run(p50/p90/p99/maxObserved)="
              << Percentile(epoch.inter_low_runs, 50U) << '/'
              << Percentile(epoch.inter_low_runs, 90U) << '/'
              << Percentile(epoch.inter_low_runs, 99U) << '/'
              << MaximumObservedRun(epoch)
              << " prefix/suffix=" << epoch.initial_high << '/'
              << epoch.suffix_high << " tail10Low=" << tail_tenth_low << '/'
              << tail_tenth_size << " last1MLow=" << last_million_low << '/'
              << last_million_size << " macro(start/terminal/target/censor)="
              << epoch.entry_starts << '/' << epoch.history_terminals << '/'
              << epoch.target_terminations << '/' << epoch.censored_combs
              << " terminalPerStartPpm="
              << (epoch.entry_starts == 0U
                      ? 0U
                      : epoch.history_terminals * 1000000U /
                            epoch.entry_starts)
              << " terminalPerLowPpm="
              << (epoch.low == 0U
                      ? 0U
                      : epoch.history_terminals * 1000000U / epoch.low)
              << '\n';
  }
  std::cout << "high-candidate global:\n"
            << "  candidateStates=" << total_states
            << " side(low/equal/high)=" << total_low << '/'
            << total_equal << '/' << total_high << " lowPpm="
            << total_low * 1000000U / total_states
            << " maximumObservedRun=" << global_maximum_run << '\n'
            << "  macro(start/terminal/target/censor)=" << total_starts << '/'
            << total_terminals << '/' << total_target_terminations << '/'
            << total_censored << " terminalPerStartPpm="
            << (total_starts == 0U
                    ? 0U
                    : total_terminals * 1000000U / total_starts)
            << " terminalPerLowPpm="
            << (total_low == 0U
                    ? 0U
                    : total_terminals * 1000000U / total_low)
            << '\n';
}

void PrintSemanticAudit(
    const RunData& data,
    const std::unordered_map<Value, OriginInfo>& origins) {
  struct Counts {
    Count terminals = 0U;
    Count parent_current_ready = 0U;
    Count first_current_ready = 0U;
    Count same_budget = 0U;
    Count direct_current_child = 0U;
    Count addition = 0U;
    Count subtraction = 0U;
    Count numerical_violations = 0U;
  } global;
  std::unordered_map<Value, Counts> by_target;
  std::unordered_map<Value, std::size_t> previous;

  std::cout << "terminal semantic-child audit:\n";
  for (std::size_t index = 0U; index < data.terminals.size(); ++index) {
    const TerminalComb& terminal = data.terminals[index];
    const OriginInfo origin = origins.at(terminal.blocker);
    Counts& local = by_target[terminal.target];
    const bool parent_ready =
        terminal.target <= static_cast<Value>(terminal.start) + 1U &&
        terminal.target <= terminal.entry;
    const bool first_ready =
        terminal.target <= static_cast<Value>(origin.first) + 1U;
    const bool same_budget = origin.mex_at_first == terminal.target;
    const bool direct_current = first_ready && same_budget;
    const bool numerical_ok = terminal.target < terminal.blocker &&
        origin.first < terminal.start && terminal.blocker < terminal.entry;

    for (Counts* counts : {&local, &global}) {
      ++counts->terminals;
      if (parent_ready) ++counts->parent_current_ready;
      if (first_ready) ++counts->first_current_ready;
      if (same_budget) ++counts->same_budget;
      if (direct_current) ++counts->direct_current_child;
      if (origin.subtraction) {
        ++counts->subtraction;
      } else {
        ++counts->addition;
      }
      if (!numerical_ok) ++counts->numerical_violations;
    }

    const auto previous_it = previous.find(terminal.target);
    const bool upward = previous_it != previous.end() &&
        data.terminals[previous_it->second].blocker < terminal.blocker;
    if (upward) {
      const TerminalComb& prior = data.terminals[previous_it->second];
      std::cout << "  upward target=" << terminal.target
                << " priorBlocker=" << prior.blocker
                << " s=" << terminal.start << " entry=" << terminal.entry
                << " blocker=" << terminal.blocker
                << " firstTime=" << origin.first
                << " origin=" << (origin.subtraction ? "sub" : "add")
                << " originParent=" << origin.parent
                << " mexAtFirst=" << origin.mex_at_first
                << " firstReady=" << first_ready
                << " sameBudget=" << same_budget
                << " currentDirect=" << direct_current << '\n'
                << "    parentCurrent=(h=" << terminal.start
                << ",anchor=value=" << terminal.entry
                << ") debt=(h=" << terminal.start
                << ",anchor=" << terminal.entry << ",localFirst="
                << origin.first << ") historicalChild=(h="
                << terminal.start << ",anchor=value=" << terminal.blocker
                << ") currentAtFirst=(h=" << origin.first
                << ",anchor=value=" << terminal.blocker << ")\n";
    }
    previous[terminal.target] = index;
  }

  for (const auto& [target, counts] : by_target) {
    std::cout << "  semantic target=" << target
              << " terminals=" << counts.terminals
              << " parentCurrentReady=" << counts.parent_current_ready
              << " firstCurrentReady=" << counts.first_current_ready
              << " sameBudgetAtFirst=" << counts.same_budget
              << " directCurrentChild=" << counts.direct_current_child
              << " origin(add/sub)=" << counts.addition << '/'
              << counts.subtraction << " numericalViolations="
              << counts.numerical_violations << '\n';
  }
  std::cout << "terminal semantic global:\n"
            << "  terminals=" << global.terminals
            << " parentCurrentReady=" << global.parent_current_ready
            << " firstCurrentReady=" << global.first_current_ready
            << " sameBudgetAtFirst=" << global.same_budget
            << " directCurrentChild=" << global.direct_current_child
            << " origin(add/sub)=" << global.addition << '/'
            << global.subtraction << " numericalViolations="
            << global.numerical_violations << '\n'
            << "  local adapter nodes: parent targetStartNode(s); debt keeps"
               " horizon s and entry anchor; normal child keeps horizon s but"
               " reanchors to historical blocker\n";
}

void Analyze(Clock horizon) {
  const RunData data = Generate(horizon);
  std::cout << "target-high-candidate horizon=" << horizon
            << " finalValue=" << data.final_value
            << " mex=" << data.final_mex
            << " epochs=" << data.epochs.size()
            << " terminals=" << data.terminals.size()
            << " maxValue=" << data.maximum_value
            << " seenMiB=" << data.seen_bytes / (1024U * 1024U) << '\n';
  PrintEpochs(data);
  const std::unordered_map<Value, OriginInfo> origins =
      CollectOrigins(horizon, data.terminals);
  PrintSemanticAudit(data, origins);
}

}  // namespace

int main(int argc, char** argv) {
  try {
    Analyze(argc >= 2 ? ParseClock(argv[1]) : 20000000U);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
