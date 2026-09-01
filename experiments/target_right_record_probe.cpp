// Memory-light probe for the global upward right-record conjecture.
//
// Unlike target_transition_probe.cpp, this stores the Recaman history as a
// dense bitset and keeps only completed target-comb summaries.  This makes it
// practical to push the same exact-orbit check substantially beyond 20M.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

namespace {

using Clock = std::uint32_t;
using Value = std::uint64_t;

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
      words_.resize(word + 1U, 0U);
    }
    words_[word] |= 1ULL << (value & 63U);
  }

  std::size_t Bytes() const { return words_.size() * sizeof(std::uint64_t); }

 private:
  std::vector<std::uint64_t> words_;
};

struct Chain {
  Value target = 0U;
  Clock start = 0U;
  Clock end = 0U;
  Value entry = 0U;
  Value blocker = 0U;
  bool target_terminated = false;
};

struct ActiveChain {
  enum class Phase : std::uint8_t { expect_add, expect_resolution };

  Value target = 0U;
  Clock start = 0U;
  Value entry = 0U;
  Value landing = 0U;
  Phase phase = Phase::expect_add;
};

struct Origin {
  Clock first = 0U;
  bool subtraction = false;
  Value predecessor = 0U;
};

struct UpwardEdge {
  Value target = 0U;
  Clock previous_end = 0U;
  Clock next_start = 0U;
  Value previous_blocker = 0U;
  Value next_entry = 0U;
  Value next_blocker = 0U;
  Value prior_upper = 0U;
};

struct Summary {
  std::uint64_t history_terminated = 0U;
  std::uint64_t macro_edges = 0U;
  std::uint64_t up = 0U;
  std::uint64_t down = 0U;
  std::uint64_t equal = 0U;
  std::uint64_t up_right_record = 0U;
  std::uint64_t up_gap_insertion = 0U;
  std::uint64_t down_left_record = 0U;
  std::uint64_t down_gap_insertion = 0U;
  Value minimum_up_gap = std::numeric_limits<Value>::max();
  Value maximum_up_gap = 0U;
  Value up_gap_mass = 0U;
  std::vector<UpwardEdge> upward_edges;
};

Clock ParseClock(const char* text) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed == 0U || parsed > std::numeric_limits<Clock>::max()) {
    throw std::invalid_argument("horizon must be in 1..2^32-1");
  }
  return static_cast<Clock>(parsed);
}

bool LowCandidateSide(Value value, Clock next_clock, Value target) {
  return value <= next_clock || value - next_clock < target;
}

Summary Summarize(const std::vector<Chain>& chains, Clock horizon) {
  struct TargetState {
    Chain previous{};
    bool has_previous = false;
    Value minimum_lower = 0U;
    Value maximum_upper = 0U;
  };

  std::unordered_map<Value, TargetState> states;
  Summary result;
  for (const Chain& chain : chains) {
    if (chain.end > horizon) {
      break;
    }
    TargetState& state = states[chain.target];
    if (chain.target_terminated) {
      state = TargetState{};
      continue;
    }
    ++result.history_terminated;
    const Value lower = chain.blocker + 1U;
    if (state.has_previous) {
      ++result.macro_edges;
      if (state.previous.blocker < chain.blocker) {
        ++result.up;
        const Value gap = chain.blocker - state.maximum_upper;
        if (state.maximum_upper <= chain.blocker) {
          ++result.up_right_record;
          result.minimum_up_gap = std::min(result.minimum_up_gap, gap);
          result.maximum_up_gap = std::max(result.maximum_up_gap, gap);
          result.up_gap_mass += gap;
        } else {
          ++result.up_gap_insertion;
        }
        result.upward_edges.push_back(UpwardEdge{
            chain.target, state.previous.end, chain.start,
            state.previous.blocker, chain.entry, chain.blocker,
            state.maximum_upper});
      } else if (chain.blocker < state.previous.blocker) {
        ++result.down;
        if (chain.entry < state.minimum_lower) {
          ++result.down_left_record;
        } else {
          ++result.down_gap_insertion;
        }
      } else {
        ++result.equal;
      }
    }
    if (!state.has_previous) {
      state.minimum_lower = lower;
      state.maximum_upper = chain.entry;
      state.has_previous = true;
    } else {
      state.minimum_lower = std::min(state.minimum_lower, lower);
      state.maximum_upper = std::max(state.maximum_upper, chain.entry);
    }
    state.previous = chain;
  }
  return result;
}

std::unordered_map<Value, Origin> ReplayOrigins(
    Clock horizon, const std::vector<UpwardEdge>& edges) {
  std::unordered_map<Value, Origin> origins;
  origins.reserve(edges.size() * 2U + 1U);
  for (const UpwardEdge& edge : edges) {
    origins.emplace(edge.next_blocker, Origin{});
  }

  DenseSeen seen;
  seen.Insert(0U);
  Value value = 0U;
  std::size_t unresolved = origins.size();
  for (std::uint64_t raw_clock = 1U;
       raw_clock <= horizon && unresolved != 0U; ++raw_clock) {
    const Clock clock = static_cast<Clock>(raw_clock);
    const Value predecessor = value;
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool subtraction = positive && !seen.Contains(candidate);
    value = subtraction ? candidate : value + clock;
    auto position = origins.find(value);
    if (position != origins.end() && position->second.first == 0U) {
      position->second = Origin{clock, subtraction, predecessor};
      --unresolved;
    }
    seen.Insert(value);
  }
  return origins;
}

std::unordered_map<Value, Origin> ReplayChainBlockerOrigins(
    Clock horizon, const std::vector<Chain>& chains) {
  std::unordered_map<Value, Origin> origins;
  origins.reserve(chains.size() + 1U);
  for (const Chain& chain : chains) {
    if (!chain.target_terminated && chain.end <= horizon) {
      origins.emplace(chain.blocker, Origin{});
    }
  }

  DenseSeen seen;
  seen.Insert(0U);
  Value value = 0U;
  std::size_t unresolved = origins.size();
  for (std::uint64_t raw_clock = 1U;
       raw_clock <= horizon && unresolved != 0U; ++raw_clock) {
    const Clock clock = static_cast<Clock>(raw_clock);
    const Value predecessor = value;
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool subtraction = positive && !seen.Contains(candidate);
    value = subtraction ? candidate : value + clock;
    auto position = origins.find(value);
    if (position != origins.end() && position->second.first == 0U) {
      position->second = Origin{clock, subtraction, predecessor};
      --unresolved;
    }
    seen.Insert(value);
  }
  return origins;
}

struct SideWordStats {
  Clock switches = 0U;
  bool has_rlr = false;
  bool has_lrl = false;
  char first = '?';
  char last = '?';
};

SideWordStats MeasureSideWord(const std::vector<char>& word) {
  SideWordStats result;
  if (word.empty()) {
    return result;
  }
  result.first = word.front();
  result.last = word.back();
  char two_back = '?';
  char previous = '?';
  for (char side : word) {
    if (side == previous) {
      continue;
    }
    if (previous != '?') {
      ++result.switches;
    }
    if (two_back == 'R' && previous == 'L' && side == 'R') {
      result.has_rlr = true;
    }
    if (two_back == 'L' && previous == 'R' && side == 'L') {
      result.has_lrl = true;
    }
    two_back = previous;
    previous = side;
  }
  return result;
}

void AnalyzeSideWords(Clock horizon, const std::vector<Chain>& chains) {
  const auto origins = ReplayChainBlockerOrigins(horizon, chains);
  std::unordered_map<Value, std::vector<Chain>> groups;
  for (const Chain& chain : chains) {
    if (!chain.target_terminated && chain.end <= horizon) {
      groups[chain.target].push_back(chain);
    }
  }

  std::array<std::uint64_t, 4U> post_switch_histogram{};
  std::array<std::uint64_t, 4U> pre_switch_histogram{};
  std::uint64_t terminal_instances = 0U;
  std::uint64_t post_rlr = 0U;
  std::uint64_t post_lrl = 0U;
  std::uint64_t pre_rlr = 0U;
  std::uint64_t intervals_straddling_first = 0U;
  Clock maximum_post_switches = 0U;
  Clock maximum_pre_switches = 0U;
  Value maximum_post_switch_blocker = 0U;
  Value maximum_pre_switch_blocker = 0U;
  std::uint64_t upward_instances = 0U;
  std::uint64_t upward_post_rlr = 0U;
  std::uint64_t upward_with_pre_first_right = 0U;
  std::array<std::uint64_t, 4U> upward_post_switch_histogram{};
  std::uint64_t upward_first_before_previous_start = 0U;
  std::uint64_t upward_first_within_previous_comb = 0U;
  std::uint64_t upward_first_after_previous_end = 0U;
  std::uint64_t upward_birth_hull_empty = 0U;
  std::uint64_t upward_birth_record_violations = 0U;
  std::uint64_t upward_post_birth_record_violations = 0U;
  std::uint64_t upward_birth_straddles = 0U;
  std::uint64_t upward_birth_straddle_violations = 0U;
  Value minimum_upward_birth_slack = std::numeric_limits<Value>::max();
  Value maximum_upward_birth_slack = 0U;
  Value minimum_upward_post_birth_slack =
      std::numeric_limits<Value>::max();
  Value maximum_upward_post_birth_slack = 0U;
  Value minimum_upward_straddle_slack =
      std::numeric_limits<Value>::max();
  Value maximum_upward_straddle_slack = 0U;
  Clock maximum_upward_post_switches = 0U;
  std::vector<std::string> upward_hull_rows;

  for (const auto& [target, group] : groups) {
    static_cast<void>(target);
    for (std::size_t current_index = 0U; current_index < group.size();
         ++current_index) {
      const Chain& current = group[current_index];
      const Value blocker = current.blocker;
      const Clock first_time = origins.at(blocker).first;
      std::vector<char> pre_word;
      std::vector<char> post_word;
      bool pre_first_right = false;
      bool has_pre_birth_hull = false;
      bool has_post_birth_hull = false;
      bool has_birth_straddle = false;
      Value pre_birth_maximum_entry = 0U;
      Value post_birth_maximum_entry = 0U;
      Value straddling_maximum_entry = 0U;
      for (std::size_t index = 0U; index <= current_index; ++index) {
        const Chain& interval = group[index];
        char side = '?';
        if (interval.entry <= blocker) {
          side = 'L';
        } else if (blocker <= interval.blocker) {
          // interval lower = interval.blocker+1 >= blocker+1.
          side = 'R';
        }
        if (interval.end < first_time) {
          if (side != '?') {
            pre_word.push_back(side);
            pre_first_right = pre_first_right || side == 'R';
          }
          if (index < current_index) {
            has_pre_birth_hull = true;
            pre_birth_maximum_entry =
                std::max(pre_birth_maximum_entry, interval.entry);
          }
        } else if (first_time < interval.start) {
          if (side == '?') {
            throw std::runtime_error(
                "post-first fresh interval contains fixed blocker");
          }
          post_word.push_back(side);
          if (index < current_index) {
            has_post_birth_hull = true;
            post_birth_maximum_entry =
                std::max(post_birth_maximum_entry, interval.entry);
          }
        } else {
          ++intervals_straddling_first;
          if (index < current_index) {
            has_birth_straddle = true;
            straddling_maximum_entry =
                std::max(straddling_maximum_entry, interval.entry);
          }
        }
      }

      const SideWordStats pre = MeasureSideWord(pre_word);
      const SideWordStats post = MeasureSideWord(post_word);
      ++terminal_instances;
      ++post_switch_histogram[std::min<Clock>(post.switches, 3U)];
      ++pre_switch_histogram[std::min<Clock>(pre.switches, 3U)];
      if (post.has_rlr) {
        ++post_rlr;
      }
      if (post.has_lrl) {
        ++post_lrl;
      }
      if (pre.has_rlr) {
        ++pre_rlr;
      }
      if (maximum_post_switches < post.switches) {
        maximum_post_switches = post.switches;
        maximum_post_switch_blocker = blocker;
      }
      if (maximum_pre_switches < pre.switches) {
        maximum_pre_switches = pre.switches;
        maximum_pre_switch_blocker = blocker;
      }

      const bool upward = current_index != 0U &&
                          group[current_index - 1U].blocker < blocker;
      if (upward) {
        ++upward_instances;
        ++upward_post_switch_histogram[
            std::min<Clock>(post.switches, 3U)];
        if (post.has_rlr) {
          ++upward_post_rlr;
        }
        if (pre_first_right) {
          ++upward_with_pre_first_right;
        }
        maximum_upward_post_switches =
            std::max(maximum_upward_post_switches, post.switches);
        const Chain& previous = group[current_index - 1U];
        if (first_time < previous.start) {
          ++upward_first_before_previous_start;
        } else if (first_time <= previous.end) {
          ++upward_first_within_previous_comb;
        } else {
          ++upward_first_after_previous_end;
        }

        if (!has_pre_birth_hull) {
          ++upward_birth_hull_empty;
        } else if (blocker < pre_birth_maximum_entry) {
          ++upward_birth_record_violations;
        } else {
          const Value slack = blocker - pre_birth_maximum_entry;
          minimum_upward_birth_slack =
              std::min(minimum_upward_birth_slack, slack);
          maximum_upward_birth_slack =
              std::max(maximum_upward_birth_slack, slack);
        }
        if (has_post_birth_hull) {
          if (blocker < post_birth_maximum_entry) {
            ++upward_post_birth_record_violations;
          } else {
            const Value slack = blocker - post_birth_maximum_entry;
            minimum_upward_post_birth_slack =
                std::min(minimum_upward_post_birth_slack, slack);
            maximum_upward_post_birth_slack =
                std::max(maximum_upward_post_birth_slack, slack);
          }
        }
        if (has_birth_straddle) {
          ++upward_birth_straddles;
          if (blocker < straddling_maximum_entry) {
            ++upward_birth_straddle_violations;
          } else {
            const Value slack = blocker - straddling_maximum_entry;
            minimum_upward_straddle_slack =
                std::min(minimum_upward_straddle_slack, slack);
            maximum_upward_straddle_slack =
                std::max(maximum_upward_straddle_slack, slack);
          }
        }
        upward_hull_rows.push_back(
            "    m=" + std::to_string(current.target) +
            " b=" + std::to_string(blocker) +
            " first=" + std::to_string(first_time) +
            " preMax=" +
            (has_pre_birth_hull ? std::to_string(pre_birth_maximum_entry)
                                : std::string("none")) +
            " preSlack=" +
            (has_pre_birth_hull && pre_birth_maximum_entry <= blocker
                 ? std::to_string(blocker - pre_birth_maximum_entry)
                 : std::string("NA")) +
            " straddleMax=" +
            (has_birth_straddle ? std::to_string(straddling_maximum_entry)
                                : std::string("none")) +
            " postMax=" +
            (has_post_birth_hull ? std::to_string(post_birth_maximum_entry)
                                 : std::string("none")) +
            " postSlack=" +
            (has_post_birth_hull && post_birth_maximum_entry <= blocker
                 ? std::to_string(blocker - post_birth_maximum_entry)
                 : std::string("NA")));
      }
    }
  }

  std::cout << "side words relative to terminal blocker (post-first):\n"
            << "  terminals=" << terminal_instances
            << " switches(0/1/2/3+)=" << post_switch_histogram[0] << '/'
            << post_switch_histogram[1] << '/' << post_switch_histogram[2]
            << '/' << post_switch_histogram[3]
            << " max=" << maximum_post_switches
            << " atBlocker=" << maximum_post_switch_blocker
            << " patterns(RLR/LRL)=" << post_rlr << '/' << post_lrl
            << '\n';
  std::cout << "  pre-first switches(0/1/2/3+)="
            << pre_switch_histogram[0] << '/' << pre_switch_histogram[1]
            << '/' << pre_switch_histogram[2] << '/'
            << pre_switch_histogram[3] << " max=" << maximum_pre_switches
            << " atBlocker=" << maximum_pre_switch_blocker
            << " RLR=" << pre_rlr
            << " straddlingIntervals=" << intervals_straddling_first
            << '\n';
  std::cout << "  upward terminals=" << upward_instances
            << " postFirstRLR=" << upward_post_rlr
            << " switches(0/1/2/3+)="
            << upward_post_switch_histogram[0] << '/'
            << upward_post_switch_histogram[1] << '/'
            << upward_post_switch_histogram[2] << '/'
            << upward_post_switch_histogram[3]
            << " max=" << maximum_upward_post_switches
            << " withPreFirstRight=" << upward_with_pre_first_right
            << " firstVsPrevious(beforeStart/within/afterEnd)="
            << upward_first_before_previous_start << '/'
            << upward_first_within_previous_comb << '/'
            << upward_first_after_previous_end << '\n';
  std::cout << "  upward hull split: birthEmpty="
            << upward_birth_hull_empty
            << " birthViolations=" << upward_birth_record_violations
            << " birthSlack(min/max)=";
  if (minimum_upward_birth_slack == std::numeric_limits<Value>::max()) {
    std::cout << "NA/NA";
  } else {
    std::cout << minimum_upward_birth_slack << '/'
              << maximum_upward_birth_slack;
  }
  std::cout << " straddles=" << upward_birth_straddles
            << " straddleViolations="
            << upward_birth_straddle_violations
            << " straddleSlack(min/max)=";
  if (minimum_upward_straddle_slack ==
      std::numeric_limits<Value>::max()) {
    std::cout << "NA/NA";
  } else {
    std::cout << minimum_upward_straddle_slack << '/'
              << maximum_upward_straddle_slack;
  }
  std::cout
            << " postBirthViolations="
            << upward_post_birth_record_violations
            << " postBirthSlack(min/max)=";
  if (minimum_upward_post_birth_slack ==
      std::numeric_limits<Value>::max()) {
    std::cout << "NA/NA";
  } else {
    std::cout << minimum_upward_post_birth_slack << '/'
              << maximum_upward_post_birth_slack;
  }
  std::cout << '\n';
  std::cout << "  upward hull rows:\n";
  for (const std::string& row : upward_hull_rows) {
    std::cout << row << '\n';
  }
}

void PrintSummary(Clock horizon, const Summary& summary, Value final_value,
                  Value mex, std::size_t seen_bytes) {
  std::cout << "horizon=" << horizon << " finalValue=" << final_value
            << " mex=" << mex << " seenMiB="
            << (seen_bytes / (1024U * 1024U)) << '\n';
  std::cout << "  chains historyTerminated=" << summary.history_terminated
            << " macroEdges=" << summary.macro_edges
            << " blocker(up/down/equal)=" << summary.up << '/'
            << summary.down << '/' << summary.equal << '\n';
  std::cout << "  intervalRecord(upRight/upGap/downLeft/downGap)="
            << summary.up_right_record << '/' << summary.up_gap_insertion
            << '/' << summary.down_left_record << '/'
            << summary.down_gap_insertion;
  if (summary.up_right_record != 0U) {
    std::cout << " upGap(min/max/mass)=" << summary.minimum_up_gap << '/'
              << summary.maximum_up_gap << '/' << summary.up_gap_mass;
  }
  std::cout << '\n';
}

void AnalyzeUpwardOrbitEnvelopes(
    Clock horizon, const std::vector<UpwardEdge>& edges,
    const std::unordered_map<Value, Origin>& origins) {
  constexpr Clock block_size = 100000U;
  struct Envelope {
    Clock first = 0U;
    Clock query_start = 0U;
    Clock query_end = 0U;
    Value prior_running_maximum = 0U;
    Value boundary_maximum = 0U;
    Value post_birth_maximum = 0U;
  };

  const std::size_t block_count =
      static_cast<std::size_t>(horizon / block_size) + 1U;
  std::vector<Value> block_maxima(block_count, 0U);
  std::vector<std::vector<std::size_t>> boundary_queries(block_count);
  std::vector<Envelope> envelopes;
  envelopes.reserve(edges.size());
  std::vector<std::pair<Clock, std::size_t>> first_events;
  first_events.reserve(edges.size());
  for (std::size_t index = 0U; index < edges.size(); ++index) {
    const Clock first = origins.at(edges[index].next_blocker).first;
    const Clock query_start = static_cast<Clock>(first + 1U);
    const Clock query_end = static_cast<Clock>(edges[index].next_start - 1U);
    envelopes.push_back(
        Envelope{first, query_start, query_end, 0U, 0U, 0U});
    first_events.emplace_back(first, index);
    if (query_start <= query_end) {
      const std::size_t first_block = query_start / block_size;
      const std::size_t last_block = query_end / block_size;
      boundary_queries[first_block].push_back(index);
      if (last_block != first_block) {
        boundary_queries[last_block].push_back(index);
      }
    }
  }
  std::sort(first_events.begin(), first_events.end());

  DenseSeen seen;
  seen.Insert(0U);
  Value value = 0U;
  Value running_maximum = 0U;
  std::size_t first_event_index = 0U;
  for (std::uint64_t raw_clock = 1U; raw_clock <= horizon; ++raw_clock) {
    const Clock clock = static_cast<Clock>(raw_clock);
    while (first_event_index < first_events.size() &&
           first_events[first_event_index].first == clock) {
      envelopes[first_events[first_event_index].second]
          .prior_running_maximum = running_maximum;
      ++first_event_index;
    }
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool subtraction = positive && !seen.Contains(candidate);
    value = subtraction ? candidate : value + clock;
    seen.Insert(value);
    running_maximum = std::max(running_maximum, value);
    const std::size_t block = clock / block_size;
    block_maxima[block] = std::max(block_maxima[block], value);
    for (std::size_t query : boundary_queries[block]) {
      Envelope& envelope = envelopes[query];
      if (envelope.query_start <= clock && clock <= envelope.query_end) {
        envelope.boundary_maximum =
            std::max(envelope.boundary_maximum, value);
      }
    }
  }

  std::uint64_t birth_orbit_records = 0U;
  std::uint64_t birth_orbit_nonrecords = 0U;
  Value maximum_birth_deficit = 0U;
  std::uint64_t post_birth_exceeds = 0U;
  Value maximum_post_birth_excess = 0U;
  std::cout << "upward blocker orbit envelopes:\n";
  for (std::size_t index = 0U; index < edges.size(); ++index) {
    Envelope& envelope = envelopes[index];
    if (envelope.query_start <= envelope.query_end) {
      const std::size_t first_block = envelope.query_start / block_size;
      const std::size_t last_block = envelope.query_end / block_size;
      envelope.post_birth_maximum = envelope.boundary_maximum;
      for (std::size_t block = first_block + 1U; block < last_block;
           ++block) {
        envelope.post_birth_maximum =
            std::max(envelope.post_birth_maximum, block_maxima[block]);
      }
    }
    const UpwardEdge& edge = edges[index];
    const bool birth_record =
        envelope.prior_running_maximum < edge.next_blocker;
    if (birth_record) {
      ++birth_orbit_records;
    } else {
      ++birth_orbit_nonrecords;
      maximum_birth_deficit = std::max(
          maximum_birth_deficit,
          envelope.prior_running_maximum - edge.next_blocker);
    }
    const bool later_exceeds =
        edge.next_blocker < envelope.post_birth_maximum;
    if (later_exceeds) {
      ++post_birth_exceeds;
      maximum_post_birth_excess = std::max(
          maximum_post_birth_excess,
          envelope.post_birth_maximum - edge.next_blocker);
    }
    std::cout << "  m=" << edge.target << " b=" << edge.next_blocker
              << " first=" << envelope.first
              << " priorOrbitMax=" << envelope.prior_running_maximum
              << " birthRecord=" << (birth_record ? "yes" : "no")
              << " birthDeficit="
              << (birth_record
                      ? 0U
                      : envelope.prior_running_maximum - edge.next_blocker)
              << " postBirthMax=" << envelope.post_birth_maximum
              << " postBirthExcess="
              << (later_exceeds
                      ? envelope.post_birth_maximum - edge.next_blocker
                      : 0U)
              << '\n';
  }
  std::cout << "  summary birthRecord/nonRecord=" << birth_orbit_records
            << '/' << birth_orbit_nonrecords
            << " maxBirthDeficit=" << maximum_birth_deficit
            << " postBirthExceeds=" << post_birth_exceeds << '/'
            << edges.size()
            << " maxPostBirthExcess=" << maximum_post_birth_excess << '\n';
}

void Analyze(const std::vector<Clock>& requested_checkpoints) {
  std::vector<Clock> checkpoints = requested_checkpoints;
  std::sort(checkpoints.begin(), checkpoints.end());
  checkpoints.erase(std::unique(checkpoints.begin(), checkpoints.end()),
                    checkpoints.end());
  const Clock horizon = checkpoints.back();

  DenseSeen seen;
  seen.Insert(0U);
  Value value = 0U;
  Value mex = 1U;
  std::vector<Chain> chains;
  ActiveChain active;
  bool chain_active = false;
  std::size_t checkpoint_index = 0U;

  auto finish_chain = [&](Clock clock, bool target_terminated,
                          Value blocker) {
    chains.push_back(Chain{active.target, active.start, clock, active.entry,
                           blocker, target_terminated});
    chain_active = false;
  };

  for (std::uint64_t raw_clock = 1U; raw_clock <= horizon; ++raw_clock) {
    const Clock clock = static_cast<Clock>(raw_clock);
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool subtraction = positive && !seen.Contains(candidate);
    const Value old_mex = mex;
    const Value next_value = subtraction ? candidate : value + clock;

    if (chain_active) {
      if (active.phase == ActiveChain::Phase::expect_add) {
        if (subtraction) {
          throw std::runtime_error("target-comb protocol: expected addition");
        }
        active.phase = ActiveChain::Phase::expect_resolution;
      } else if (subtraction) {
        if (next_value + 1U != active.landing) {
          throw std::runtime_error(
              "target-comb protocol: nonconsecutive landing");
        }
        active.landing = next_value;
        active.phase = ActiveChain::Phase::expect_add;
      } else {
        finish_chain(clock, false, active.landing - 1U);
      }
    }

    value = next_value;
    seen.Insert(value);
    while (seen.Contains(mex)) {
      ++mex;
    }

    if (chain_active && mex != old_mex) {
      finish_chain(clock, true, old_mex);
    }

    if (!chain_active && subtraction && mex == old_mex && value > mex &&
        LowCandidateSide(value, static_cast<Clock>(clock + 1U), mex)) {
      active = ActiveChain{mex, clock, value, value,
                           ActiveChain::Phase::expect_add};
      chain_active = true;
    }

    if (checkpoint_index < checkpoints.size() &&
        clock == checkpoints[checkpoint_index]) {
      const Summary summary = Summarize(chains, clock);
      PrintSummary(clock, summary, value, mex, seen.Bytes());
      ++checkpoint_index;
    }
  }

  const Summary final_summary = Summarize(chains, horizon);
  const auto origins = ReplayOrigins(horizon, final_summary.upward_edges);
  std::uint64_t addition_origins = 0U;
  std::uint64_t subtraction_origins = 0U;
  std::uint64_t predecessor_below_previous_blocker = 0U;
  std::uint64_t predecessor_between_previous_and_hull = 0U;
  std::uint64_t predecessor_above_hull = 0U;
  std::uint64_t addition_equation_failures = 0U;
  std::cout << "upward edges at final horizon:\n";
  for (const UpwardEdge& edge : final_summary.upward_edges) {
    const Origin& origin = origins.at(edge.next_blocker);
    if (origin.subtraction) {
      ++subtraction_origins;
    } else {
      ++addition_origins;
      if (origin.predecessor + origin.first != edge.next_blocker) {
        ++addition_equation_failures;
      }
    }
    if (origin.predecessor <= edge.previous_blocker) {
      ++predecessor_below_previous_blocker;
    } else if (origin.predecessor <= edge.prior_upper) {
      ++predecessor_between_previous_and_hull;
    } else {
      ++predecessor_above_hull;
    }
    std::cout << "  m=" << edge.target << " clocks=["
              << edge.previous_end << ',' << edge.next_start << "] b="
              << edge.previous_blocker << " b'=" << edge.next_blocker
              << " priorUpper=" << edge.prior_upper
              << " recordGap="
              << (edge.prior_upper <= edge.next_blocker
                      ? edge.next_blocker - edge.prior_upper
                      : 0U)
              << " origin=" << (origin.subtraction ? "sub" : "add")
              << '@' << origin.first
              << " predecessor=" << origin.predecessor << '\n';
  }
  std::cout << "  origin(sub/add)=" << subtraction_origins << '/'
            << addition_origins
            << " predecessor(<=oldB/between/aboveHull)="
            << predecessor_below_previous_blocker << '/'
            << predecessor_between_previous_and_hull << '/'
            << predecessor_above_hull
            << " additionEquationFailures=" << addition_equation_failures
            << '\n';
  AnalyzeUpwardOrbitEnvelopes(horizon, final_summary.upward_edges, origins);
  AnalyzeSideWords(horizon, chains);
}

}  // namespace

int main(int argc, char** argv) {
  try {
    std::vector<Clock> checkpoints;
    for (int index = 1; index < argc; ++index) {
      checkpoints.push_back(ParseClock(argv[index]));
    }
    if (checkpoints.empty()) {
      checkpoints = {1000000U, 5000000U, 20000000U};
    }
    Analyze(checkpoints);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
