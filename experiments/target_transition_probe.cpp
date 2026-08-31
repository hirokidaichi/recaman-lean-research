#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
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

struct Occurrence {
  Clock first;
  Clock last;
  Clock count;
  bool first_was_subtraction;
  Value first_predecessor;
};

enum class Side : std::uint8_t { low = 0U, equal = 1U, high = 2U };

struct EpochStats {
  Value target = 0U;
  Clock start = 0U;
  Clock end = 0U;
  std::uint64_t above_states = 0U;
  std::array<std::uint64_t, 3U> side_counts{};
  std::array<std::array<std::uint64_t, 3U>, 3U> transitions{};
  std::array<std::array<std::uint64_t, 3U>, 3U> subtraction_transitions{};
};

struct ChainStats {
  Value target = 0U;
  Clock start_clock = 0U;
  Clock end_clock = 0U;
  Value entry = 0U;
  Value exit = 0U;
  Clock landings = 0U;
  bool target_terminated = false;
  Value blocker = 0U;
  Clock blocker_first = 0U;
  Clock blocker_last = 0U;
  Clock blocker_occurrences = 0U;
  bool blocker_first_was_subtraction = false;
  Value blocker_first_predecessor = 0U;
  Clock blocker_forced_uses = 0U;
};

struct ActiveChain {
  enum class Phase : std::uint8_t { expect_add, expect_resolution };

  Value target;
  Clock start_clock;
  Value entry;
  Value current_landing;
  Clock landings;
  Phase phase;
};

struct TargetBlocker {
  Value target;
  Value blocker;

  bool operator==(const TargetBlocker&) const = default;
};

struct TargetBlockerHash {
  std::size_t operator()(const TargetBlocker& key) const {
    const std::size_t first = std::hash<Value>{}(key.target);
    const std::size_t second = std::hash<Value>{}(key.blocker);
    return first ^ (second + 0x9e3779b97f4a7c15ULL + (first << 6U) +
                    (first >> 2U));
  }
};

struct MacroWitness {
  Value target = 0U;
  Clock previous_end = 0U;
  Clock next_start = 0U;
  Value previous_blocker = 0U;
  Value next_entry = 0U;
  Value next_blocker = 0U;
  Clock next_blocker_first = 0U;
  bool next_blocker_first_was_subtraction = false;
  Value next_blocker_first_predecessor = 0U;
  std::int64_t amount = 0;
};

Clock ParseHorizon(const char* text) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed == 0U || parsed > std::numeric_limits<Clock>::max()) {
    throw std::invalid_argument("horizon must be in 1..2^32-1");
  }
  return static_cast<Clock>(parsed);
}

Side CandidateSide(Value value, Clock next_clock, Value target) {
  const Value candidate = value > next_clock ? value - next_clock : 0U;
  if (candidate < target) {
    return Side::low;
  }
  if (candidate == target) {
    return Side::equal;
  }
  return Side::high;
}

const char* SideName(Side side) {
  switch (side) {
    case Side::low:
      return "L";
    case Side::equal:
      return "E";
    case Side::high:
      return "H";
  }
  return "?";
}

void PrintEpoch(const EpochStats& epoch) {
  const std::uint64_t duration =
      static_cast<std::uint64_t>(epoch.end) - epoch.start + 1U;
  std::cout << "  m=" << epoch.target << " interval=[" << epoch.start << ','
            << epoch.end << "] duration=" << duration
            << " above=" << epoch.above_states << " sides(L/E/H)="
            << epoch.side_counts[0] << '/' << epoch.side_counts[1] << '/'
            << epoch.side_counts[2] << " transitions=";
  bool first = true;
  for (std::size_t from = 0U; from < 3U; ++from) {
    for (std::size_t to = 0U; to < 3U; ++to) {
      const std::uint64_t count = epoch.transitions[from][to];
      if (count == 0U) {
        continue;
      }
      if (!first) {
        std::cout << ',';
      }
      first = false;
      std::cout << SideName(static_cast<Side>(from))
                << SideName(static_cast<Side>(to)) << ':' << count;
    }
  }
  if (first) {
    std::cout << "none";
  }
  std::cout << '\n';
  std::cout << "    subtraction-caused=";
  first = true;
  for (std::size_t from = 0U; from < 3U; ++from) {
    for (std::size_t to = 0U; to < 3U; ++to) {
      const std::uint64_t count = epoch.subtraction_transitions[from][to];
      if (count == 0U) {
        continue;
      }
      if (!first) {
        std::cout << ',';
      }
      first = false;
      std::cout << SideName(static_cast<Side>(from))
                << SideName(static_cast<Side>(to)) << ':' << count;
    }
  }
  if (first) {
    std::cout << "none";
  }
  std::cout << '\n';
}

void Analyze(Clock horizon) {
  std::unordered_map<Value, Occurrence> occurrences;
  occurrences.reserve(static_cast<std::size_t>(horizon) * 2U / 3U + 1U);
  occurrences.emplace(0U, Occurrence{0U, 0U, 1U, false, 0U});

  Value value = 0U;
  Value mex = 1U;
  EpochStats epoch{mex, 0U, 0U};
  std::vector<EpochStats> epochs;
  std::vector<ChainStats> chains;
  std::unordered_map<Value, Clock> blocker_uses;
  std::unordered_map<Value, Clock> forced_blocker_uses;
  std::unordered_map<TargetBlocker, Clock, TargetBlockerHash>
      target_blocker_uses;

  bool previous_side_valid = false;
  Side previous_side = Side::low;
  Value previous_high_excess = 0U;
  bool previous_step_was_subtraction = false;
  ActiveChain active{};
  bool chain_active = false;

  std::uint64_t subtractions = 0U;
  std::uint64_t forced_additions = 0U;
  std::uint64_t low_states = 0U;
  std::uint64_t low_forced_violations = 0U;
  std::uint64_t low_to_low = 0U;
  std::uint64_t high_to_low = 0U;
  std::uint64_t exit_window_violations = 0U;
  Value smallest_exit_window_slack = std::numeric_limits<Value>::max();
  std::uint64_t maximum_exit_window_ppm = 0U;
  std::uint64_t chain_protocol_violations = 0U;

  auto finish_chain = [&](Clock clock, bool target_terminated,
                          Value blocker) {
    ChainStats result;
    result.target = active.target;
    result.start_clock = active.start_clock;
    result.end_clock = clock;
    result.entry = active.entry;
    result.exit = active.current_landing;
    result.landings = active.landings;
    result.target_terminated = target_terminated;
    result.blocker = blocker;
    if (!target_terminated) {
      const auto position = occurrences.find(blocker);
      if (position == occurrences.end()) {
        ++chain_protocol_violations;
      } else {
        result.blocker_first = position->second.first;
        result.blocker_last = position->second.last;
        result.blocker_occurrences = position->second.count;
        result.blocker_first_was_subtraction =
            position->second.first_was_subtraction;
        result.blocker_first_predecessor =
            position->second.first_predecessor;
        result.blocker_forced_uses = forced_blocker_uses[blocker];
        ++blocker_uses[blocker];
        ++target_blocker_uses[TargetBlocker{active.target, blocker}];
      }
    }
    chains.push_back(result);
    chain_active = false;
  };

  for (std::uint64_t raw_clock = 1U; raw_clock <= horizon; ++raw_clock) {
    const Clock clock = static_cast<Clock>(raw_clock);

    const bool above = mex < value;
    const Side side = CandidateSide(value, clock, mex);
    if (above) {
      ++epoch.above_states;
      ++epoch.side_counts[static_cast<std::size_t>(side)];
      if (side == Side::low) {
        ++low_states;
      }
      if (previous_side_valid) {
        ++epoch.transitions[static_cast<std::size_t>(previous_side)]
                           [static_cast<std::size_t>(side)];
        if (previous_step_was_subtraction) {
          ++epoch.subtraction_transitions
              [static_cast<std::size_t>(previous_side)]
              [static_cast<std::size_t>(side)];
        }
        if (previous_side == Side::low && side == Side::low) {
          ++low_to_low;
        }
        if (previous_side == Side::high && side == Side::low) {
          ++high_to_low;
          if (previous_high_excess >= clock) {
            ++exit_window_violations;
          } else {
            smallest_exit_window_slack = std::min(
                smallest_exit_window_slack,
                static_cast<Value>(clock) - previous_high_excess);
            maximum_exit_window_ppm = std::max(
                maximum_exit_window_ppm,
                previous_high_excess * 1000000U /
                    static_cast<std::uint64_t>(clock));
          }
        }
      }
      previous_side = side;
      previous_high_excess =
          side == Side::high ? value - clock - mex : 0U;
      previous_side_valid = true;
    } else {
      previous_side_valid = false;
    }

    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const auto candidate_position = occurrences.find(candidate);
    const bool seen = positive && candidate_position != occurrences.end();
    const bool subtract = positive && !seen;
    if (!subtract && seen) {
      ++forced_blocker_uses[candidate];
    }

    if (above && side == Side::low && subtract) {
      ++low_forced_violations;
    }

    const Value old_mex = mex;
    const Value old_value = value;
    const Value new_value = subtract ? candidate : value + clock;
    if (subtract) {
      ++subtractions;
    } else {
      ++forced_additions;
    }

    if (chain_active) {
      if (active.phase == ActiveChain::Phase::expect_add) {
        if (subtract) {
          ++chain_protocol_violations;
          chain_active = false;
        } else {
          active.phase = ActiveChain::Phase::expect_resolution;
        }
      } else if (subtract) {
        if (new_value + 1U != active.current_landing) {
          ++chain_protocol_violations;
          chain_active = false;
        } else {
          active.current_landing = new_value;
          ++active.landings;
          active.phase = ActiveChain::Phase::expect_add;
        }
      } else {
        const Value blocker = active.current_landing - 1U;
        finish_chain(clock, false, blocker);
      }
    }

    value = new_value;
    auto [value_position, inserted] = occurrences.emplace(
        value, Occurrence{clock, clock, 1U, subtract, old_value});
    if (!inserted) {
      value_position->second.last = clock;
      ++value_position->second.count;
    }
    while (occurrences.find(mex) != occurrences.end()) {
      ++mex;
    }

    if (chain_active && mex != old_mex) {
      finish_chain(clock, true, old_mex);
    }

    if (!chain_active && subtract && mex == old_mex && value > mex) {
      const Side landing_side = CandidateSide(value, clock + 1U, mex);
      if (landing_side == Side::low) {
        active = ActiveChain{mex, clock, value, value, 1U,
                             ActiveChain::Phase::expect_add};
        chain_active = true;
      }
    }

    if (mex != old_mex) {
      epoch.end = clock;
      epochs.push_back(epoch);
      epoch = EpochStats{mex, clock, clock};
      previous_side_valid = false;
    } else {
      epoch.end = clock;
      previous_step_was_subtraction = subtract;
    }
  }

  const std::uint64_t open_chains = chain_active ? 1U : 0U;
  epochs.push_back(epoch);

  std::unordered_map<Value, ChainStats> previous_terminal_by_target;
  std::uint64_t macro_edges = 0U;
  std::uint64_t blocker_up = 0U;
  std::uint64_t blocker_down = 0U;
  std::uint64_t blocker_equal = 0U;
  std::uint64_t upward_subtraction_origin = 0U;
  std::uint64_t upward_addition_origin = 0U;
  std::uint64_t upward_origin_violations = 0U;
  std::uint64_t first_time_up = 0U;
  std::uint64_t first_time_down = 0U;
  std::uint64_t first_time_equal = 0U;
  std::uint64_t separator_violations = 0U;
  std::uint64_t macro_identity_violations = 0U;
  std::int64_t signed_entry_motion_sum = 0;
  std::uint64_t fresh_length_sum = 0U;
  MacroWitness largest_blocker_rise;
  MacroWitness largest_blocker_fall;
  std::vector<MacroWitness> upward_edges;

  for (const ChainStats& chain : chains) {
    if (chain.target_terminated) {
      previous_terminal_by_target.erase(chain.target);
      continue;
    }
    const auto previous_position =
        previous_terminal_by_target.find(chain.target);
    if (previous_position != previous_terminal_by_target.end()) {
      const ChainStats& previous = previous_position->second;
      ++macro_edges;
      const std::int64_t entry_motion =
          static_cast<std::int64_t>(chain.entry) -
          static_cast<std::int64_t>(previous.blocker);
      const std::int64_t blocker_motion =
          static_cast<std::int64_t>(chain.blocker) -
          static_cast<std::int64_t>(previous.blocker);
      const std::uint64_t fresh_length = chain.entry - chain.blocker;
      signed_entry_motion_sum += entry_motion;
      fresh_length_sum += fresh_length;
      if (blocker_motion !=
          entry_motion - static_cast<std::int64_t>(fresh_length)) {
        ++macro_identity_violations;
      }
      if (chain.blocker < previous.blocker &&
          previous.blocker <= chain.entry) {
        ++separator_violations;
      }
      if (blocker_motion > 0) {
        ++blocker_up;
        if (chain.blocker_first_was_subtraction) {
          ++upward_subtraction_origin;
          if (chain.blocker_first_predecessor <= chain.entry) {
            ++upward_origin_violations;
          }
        } else {
          ++upward_addition_origin;
          if (chain.blocker <= chain.blocker_first_predecessor) {
            ++upward_origin_violations;
          }
        }
        upward_edges.push_back(MacroWitness{
            chain.target, previous.end_clock, chain.start_clock,
            previous.blocker, chain.entry, chain.blocker,
            chain.blocker_first, chain.blocker_first_was_subtraction,
            chain.blocker_first_predecessor,
            blocker_motion});
        if (blocker_motion > largest_blocker_rise.amount) {
          largest_blocker_rise = MacroWitness{
              chain.target, previous.end_clock, chain.start_clock,
              previous.blocker, chain.entry, chain.blocker,
              chain.blocker_first, chain.blocker_first_was_subtraction,
              chain.blocker_first_predecessor,
              blocker_motion};
        }
      } else if (blocker_motion < 0) {
        ++blocker_down;
        const std::int64_t fall = -blocker_motion;
        if (fall > largest_blocker_fall.amount) {
          largest_blocker_fall = MacroWitness{
              chain.target, previous.end_clock, chain.start_clock,
              previous.blocker, chain.entry, chain.blocker,
              chain.blocker_first, chain.blocker_first_was_subtraction,
              chain.blocker_first_predecessor,
              fall};
        }
      } else {
        ++blocker_equal;
      }
      if (chain.blocker_first > previous.blocker_first) {
        ++first_time_up;
      } else if (chain.blocker_first < previous.blocker_first) {
        ++first_time_down;
      } else {
        ++first_time_equal;
      }
    }
    previous_terminal_by_target[chain.target] = chain;
  }

  std::sort(epochs.begin(), epochs.end(), [](const EpochStats& lhs,
                                              const EpochStats& rhs) {
    const std::uint64_t lhs_duration =
        static_cast<std::uint64_t>(lhs.end) - lhs.start + 1U;
    const std::uint64_t rhs_duration =
        static_cast<std::uint64_t>(rhs.end) - rhs.start + 1U;
    if (lhs_duration != rhs_duration) {
      return lhs_duration > rhs_duration;
    }
    return lhs.target < rhs.target;
  });

  std::sort(chains.begin(), chains.end(), [](const ChainStats& lhs,
                                              const ChainStats& rhs) {
    if (lhs.landings != rhs.landings) {
      return lhs.landings > rhs.landings;
    }
    return lhs.start_clock < rhs.start_clock;
  });

  std::uint64_t target_terminated = 0U;
  std::uint64_t history_terminated = 0U;
  std::uint64_t blocker_age_sum = 0U;
  Clock oldest_blocker_age = 0U;
  ChainStats oldest_blocker_chain;
  std::uint64_t singleton_blockers = 0U;
  std::uint64_t subtraction_origin_blockers = 0U;
  std::uint64_t subtraction_origin_lift_violations = 0U;
  Value smallest_subtraction_origin_lift = std::numeric_limits<Value>::max();
  Clock maximum_terminal_blocker_forced_uses = 0U;
  for (const ChainStats& chain : chains) {
    if (chain.target_terminated) {
      ++target_terminated;
    } else {
      ++history_terminated;
      if (chain.blocker_occurrences == 1U) {
        ++singleton_blockers;
      }
      if (chain.blocker_first_was_subtraction) {
        ++subtraction_origin_blockers;
        if (chain.blocker_first_predecessor <= chain.entry) {
          ++subtraction_origin_lift_violations;
        } else {
          smallest_subtraction_origin_lift = std::min(
              smallest_subtraction_origin_lift,
              chain.blocker_first_predecessor - chain.entry);
        }
      }
      maximum_terminal_blocker_forced_uses = std::max(
          maximum_terminal_blocker_forced_uses, chain.blocker_forced_uses);
      const Clock age = chain.end_clock - chain.blocker_last;
      blocker_age_sum += age;
      if (age > oldest_blocker_age) {
        oldest_blocker_age = age;
        oldest_blocker_chain = chain;
      }
    }
  }

  Value most_reused_blocker = 0U;
  Clock most_reused_blocker_count = 0U;
  for (const auto& [blocker, count] : blocker_uses) {
    if (count > most_reused_blocker_count) {
      most_reused_blocker = blocker;
      most_reused_blocker_count = count;
    }
  }
  Clock most_reused_target_blocker = 0U;
  for (const auto& [key, count] : target_blocker_uses) {
    static_cast<void>(key);
    most_reused_target_blocker = std::max(most_reused_target_blocker, count);
  }

  std::cout << "target-transition horizon=" << horizon
            << " finalValue=" << value << " mex=" << mex
            << " distinctValues=" << occurrences.size() << '\n';
  std::cout << "  operations: subtractions=" << subtractions
            << " additions=" << forced_additions << '\n';
  std::cout << "  candidate transitions: lowStates=" << low_states
            << " lowForcedViolations=" << low_forced_violations
            << " LL=" << low_to_low << " HL=" << high_to_low
            << " exitWindowViolations=" << exit_window_violations;
  if (high_to_low != 0U &&
      smallest_exit_window_slack != std::numeric_limits<Value>::max()) {
    std::cout << " minExitSlack=" << smallest_exit_window_slack
              << " maxExitWindowPpm=" << maximum_exit_window_ppm;
  }
  std::cout << '\n';
  std::cout << "  descending comb chains: total=" << chains.size()
            << " targetTerminated=" << target_terminated
            << " historyTerminated=" << history_terminated
            << " openAtHorizon=" << open_chains
            << " protocolViolations=" << chain_protocol_violations << '\n';
  std::cout << "  blocker reuse: globalMax=" << most_reused_blocker_count
            << " blocker=" << most_reused_blocker
            << " withinTargetMax=" << most_reused_target_blocker
            << " singleton=" << singleton_blockers << '/'
            << history_terminated << " subtractionOrigin="
            << subtraction_origin_blockers << '/' << history_terminated
            << " subtractionLiftViolations="
            << subtraction_origin_lift_violations;
  if (subtraction_origin_blockers != 0U &&
      smallest_subtraction_origin_lift != std::numeric_limits<Value>::max()) {
    std::cout << " minSubtractionLift=" << smallest_subtraction_origin_lift;
  }
  std::cout
            << " maxAllForcedUses=" << maximum_terminal_blocker_forced_uses;
  if (history_terminated != 0U) {
    std::cout << " averageAge=" << (blocker_age_sum / history_terminated)
              << " oldestAge=" << oldest_blocker_age
              << " oldest=(m=" << oldest_blocker_chain.target
              << ",clock=" << oldest_blocker_chain.end_clock
              << ",blocker=" << oldest_blocker_chain.blocker
              << ",last=" << oldest_blocker_chain.blocker_last << ')';
  }
  std::cout << '\n';
  if (!upward_edges.empty()) {
    std::cout << "    upward resets:\n";
    const std::size_t upward_limit =
        std::min<std::size_t>(30U, upward_edges.size());
    for (std::size_t index = 0U; index < upward_limit; ++index) {
      const MacroWitness& edge = upward_edges[index];
      std::cout << "      m=" << edge.target << " clocks=["
                << edge.previous_end << ',' << edge.next_start << "] b="
                << edge.previous_blocker << " entry=" << edge.next_entry
                << " b'=" << edge.next_blocker
                << " rise=" << edge.amount
                << " fresh=" << edge.next_entry - edge.next_blocker
                << " b'first=" << edge.next_blocker_first
                << " origin="
                << (edge.next_blocker_first_was_subtraction ? "sub" : "add")
                << " predecessor=" << edge.next_blocker_first_predecessor
                << '\n';
    }
  }
  std::cout << "  macro edges: total=" << macro_edges
            << " blocker(up/down/equal)=" << blocker_up << '/'
            << blocker_down << '/' << blocker_equal
            << " firstTime(up/down/equal)=" << first_time_up << '/'
            << first_time_down << '/' << first_time_equal
            << " upwardOrigin(sub/add)=" << upward_subtraction_origin << '/'
            << upward_addition_origin
            << " upwardOriginViolations=" << upward_origin_violations
            << " separatorViolations=" << separator_violations
            << " identityViolations=" << macro_identity_violations << '\n';
  std::cout << "    signedEntryMotionSum=" << signed_entry_motion_sum
            << " freshLengthSum=" << fresh_length_sum;
  if (largest_blocker_rise.amount != 0) {
    std::cout << " largestRise=" << largest_blocker_rise.amount
              << " (m=" << largest_blocker_rise.target
              << ",b=" << largest_blocker_rise.previous_blocker
              << ",entry=" << largest_blocker_rise.next_entry
              << ",b'=" << largest_blocker_rise.next_blocker << ')';
  }
  if (largest_blocker_fall.amount != 0) {
    std::cout << " largestFall=" << largest_blocker_fall.amount
              << " (m=" << largest_blocker_fall.target
              << ",b=" << largest_blocker_fall.previous_blocker
              << ",entry=" << largest_blocker_fall.next_entry
              << ",b'=" << largest_blocker_fall.next_blocker << ')';
  }
  std::cout << '\n';

  std::cout << "longest mex epochs:\n";
  const std::size_t epoch_limit = std::min<std::size_t>(15U, epochs.size());
  for (std::size_t index = 0U; index < epoch_limit; ++index) {
    PrintEpoch(epochs[index]);
  }

  std::cout << "longest descending comb chains:\n";
  const std::size_t chain_limit = std::min<std::size_t>(15U, chains.size());
  for (std::size_t index = 0U; index < chain_limit; ++index) {
    const ChainStats& chain = chains[index];
    std::cout << "  m=" << chain.target << " clocks=[" << chain.start_clock
              << ',' << chain.end_clock << "] entry=" << chain.entry
              << " exit=" << chain.exit << " landings=" << chain.landings;
    if (chain.target_terminated) {
      std::cout << " terminal=target";
    } else {
      std::cout << " terminal=history blocker=" << chain.blocker
                << " first=" << chain.blocker_first
                << " last=" << chain.blocker_last
                << " occurrences=" << chain.blocker_occurrences
                << " origin="
                << (chain.blocker_first_was_subtraction ? "sub" : "add")
                << " forcedUses=" << chain.blocker_forced_uses
                << " age=" << chain.end_clock - chain.blocker_last;
    }
    std::cout << '\n';
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Clock horizon = argc >= 2 ? ParseHorizon(argv[1]) : 1000000U;
    Analyze(horizon);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
