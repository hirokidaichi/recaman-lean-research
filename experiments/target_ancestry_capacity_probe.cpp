// Dense first-occurrence ancestry capacity audit for target-comb blockers.
//
// A first occurrence needs only (time, branch): if value v first appears at
// clock t, its parent is v-t for addition and v+t for subtraction. Packing
// these into 32 bits permits direct ancestry lookup without replay per layer.

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

struct TerminalComb {
  Value target = 0U;
  Clock epoch_start = 0U;
  Value pre_tail_max = 0U;
  Clock start = 0U;
  Clock end = 0U;
  Value entry = 0U;
  Value blocker = 0U;
};

struct ActiveComb {
  enum class Phase : std::uint8_t { expect_add, expect_resolution };
  Value target = 0U;
  Clock epoch_start = 0U;
  Value pre_tail_max = 0U;
  Clock start = 0U;
  Value entry = 0U;
  Value landing = 0U;
  Phase phase = Phase::expect_add;
};

struct MacroData {
  std::vector<TerminalComb> terminals;
  Value final_value = 0U;
  Value final_mex = 0U;
  Value maximum_value = 0U;
  std::size_t seen_bytes = 0U;
};

struct Origin { Clock first = 0U; Value parent = 0U; };
struct MemoResult { Value root = 0U; Clock distance = 0U; };
struct PathSummary { Value root = 0U; Clock length = 0U; };
struct Interval { Value lower = 0U; Value upper = 0U; };

// Exact stopping rule of FirstAt.preTail_anchorObstruction_or_normalProgress.
// The fixed anchor is inherited from PhaseSearchNode.anchorParent.  Merely
// comparing the final pre-tail root with the anchor would be wrong: an
// intermediate actual predecessor may already have crossed below it.
struct AnchorOutcome {
  bool residual = false;
  Value endpoint = 0U;
  Clock endpoint_first = 0U;
  Clock length = 0U;
};

struct AnchorWitness {
  bool present = false;
  Value target = 0U;
  Clock epoch_start = 0U;
  Clock macro_start = 0U;
  Clock macro_end = 0U;
  Value entry = 0U;
  Value blocker = 0U;
  Value anchor = 0U;
  Value endpoint = 0U;
  Clock endpoint_first = 0U;
  Clock length = 0U;
};

struct AnchorStats {
  Count candidates = 0U;
  Count residual = 0U;
  Count progress = 0U;
  Count zero_anchor_residual = 0U;
  Count max_ratio_ppm = 0U;
  Value max_excess = 0U;
  Clock max_residual_length = 0U;
  AnchorWitness max_ratio_witness;
};

struct RemountWitness {
  bool present = false;
  Value target = 0U;
  Value root = 0U;
  Clock source_start = 0U;
  Clock escape_start = 0U;
  Clock episode_distance = 0U;
};

struct RemountStats {
  Count sources = 0U;
  Count resolved = 0U;
  Count unresolved = 0U;
  Count unresolved_no_later = 0U;
  Count separator_checks = 0U;
  Count separator_violations = 0U;
  std::vector<Clock> waits;
  RemountWitness max_wait_witness;
};

struct BasinStats {
  Count paths = 0U;
  Count distinct_roots = 0U;
  Count root_above_pre_tail_max = 0U;
  Count current_entry_below_root = 0U;
  Count current_blocker_at_least_root = 0U;
  Count current_separator_violations = 0U;
  Count max_root_reuse = 0U;
  Value maximum_root = 0U;
  Count maximum_root_pre_tail_max_ratio_ppm = 0U;
  std::vector<Value> unresolved_distinct_root_values;
  RemountStats path_weighted;
  RemountStats distinct_root;
};

// Round 11: for one representative use of each (target, pre-epoch root),
// quantify the monotone fresh mass accumulated while the orbit stays on the
// blocker side of the root.  Every such terminal contributes the fresh,
// globally disjoint interval [blocker + 1, entry].
struct GrowthWitness {
  bool present = false;
  bool resolved = false;
  Value target = 0U;
  Value root = 0U;
  Clock source_start = 0U;
  Clock escape_start = 0U;
  Clock waiting_episodes = 0U;
  Count fresh_mass = 0U;
  Value maximum_entry = 0U;
  Value minimum_blocker = 0U;
  Value maximum_blocker = 0U;
  Count blocker_rises = 0U;
  Count blocker_falls = 0U;
  Count blocker_records = 0U;
  Count clock_gap = 0U;
};

struct GrowthStats {
  Count sources = 0U;
  Count resolved = 0U;
  Count unresolved = 0U;
  Count waiting_episodes = 0U;
  Count fresh_mass = 0U;
  Count active_clock_mass = 0U;
  Count duration_identity_violations = 0U;
  Count mass_episode_lower_bound_violations = 0U;
  Count fresh_hull_violations = 0U;
  Count clock_gap_violations = 0U;
  Count blocker_rises = 0U;
  Count blocker_falls = 0U;
  Count blocker_equals = 0U;
  Count blocker_records = 0U;
  Count blocker_rises_not_records = 0U;
  Count sequences_with_rise = 0U;
  Count sequences_with_fall = 0U;
  Count maximum_hull_density_ppm = 0U;
  Count maximum_clock_occupancy_ppm = 0U;
  GrowthWitness maximum_resolved_wait_witness;
  GrowthWitness maximum_unresolved_wait_witness;
};

struct GapWitness {
  bool present = false;
  Value target = 0U;
  Value root = 0U;
  Clock source_start = 0U;
  Clock rise_start = 0U;
  Value previous_entry_hull = 0U;
  Value blocker = 0U;
  Value entry = 0U;
  Value gap = 0U;
  Value fresh_mass = 0U;
  Count ratio_ppm = 0U;
};

struct SourcePaymentWitness {
  bool present = false;
  Value target = 0U;
  Value root = 0U;
  Clock source_start = 0U;
  Count waiting_transitions = 0U;
  Count fresh_mass = 0U;
  Count cumulative_gap = 0U;
  Count record_gain = 0U;
  Count ratio_ppm = 0U;
};

struct RecordPaymentStats {
  Count sources = 0U;
  Count waiting_transitions = 0U;
  Count record_rises = 0U;
  Count nonrecord_rises = 0U;
  Count falls = 0U;
  Count equals = 0U;
  Count record_below_entry_hull = 0U;
  Count descent_mass_exceeds_drop = 0U;
  Count cumulative_gap = 0U;
  Count record_fresh_mass = 0U;
  Count descent_drop = 0U;
  Count descent_fresh_mass = 0U;
  Count cumulative_record_gain = 0U;
  Count gap_exceeds_q_plus_root = 0U;
  Count gain_exceeds_q_plus_root = 0U;
  Count maximum_gap_over_q_ppm = 0U;
  Count maximum_source_gap_over_q_plus_root_ppm = 0U;
  Count maximum_source_gain_over_q_plus_root_ppm = 0U;
  GapWitness sharp_gap_witness;
  SourcePaymentWitness sharp_source_gap_witness;
};

struct GapHistoryEvent {
  Value target = 0U;
  Clock epoch_start = 0U;
  Clock start = 0U;
  Clock end = 0U;
  Value lower = 0U;
  Value upper = 0U;
};

struct GapHistoryCounts {
  Count mass = 0U;
  Count visited_by_start = 0U;
  Count visited_by_end = 0U;
  Count unvisited_by_end = 0U;
  Count visited_by_horizon = 0U;
  Count first_after_record = 0U;
  Count unvisited_by_horizon = 0U;
  Clock maximum_future_delay = 0U;
  Count first_pre_tail = 0U;
  Count first_tail_before_start = 0U;
  Count first_during_record_episode = 0U;
  Count first_subtraction = 0U;
  Count first_addition = 0U;
  Count first_history_terminal_comb = 0U;
  Count first_outside_history_terminal_comb = 0U;
};

struct GlobalStats {
  std::unordered_map<Value, Count> root_reuse;
  std::unordered_map<Value, Count> node_reuse;
  std::unordered_set<Value> ancestry_union;
  std::unordered_set<Value> edge_children;
  Count total_path_nodes = 0U;
  Count maximum_edge_reuse = 0U;
};

Clock ParseClock(const char* text) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed == 0U || parsed > 2000000000ULL)
    throw std::invalid_argument("horizon must be in 1..2,000,000,000");
  return static_cast<Clock>(parsed);
}

bool LowCandidateSide(Value value, Clock next_clock, Value target) {
  return value <= next_clock || value - next_clock < target;
}

MacroData GenerateMacroData(Clock horizon) {
  DenseSeen seen;
  seen.Insert(0U);
  Value value = 0U, mex = 1U, maximum_value = 0U;
  Clock epoch_start = 0U;
  Value epoch_pre_tail_max = 0U;
  ActiveComb active;
  bool comb_active = false;
  MacroData result;
  auto finish = [&](Clock clock, bool target_terminated, Value blocker) {
    if (!target_terminated) {
      result.terminals.push_back(TerminalComb{
          active.target, active.epoch_start, active.pre_tail_max,
          active.start, clock,
          active.entry, blocker});
    }
    comb_active = false;
  };

  for (std::uint64_t raw = 1U; raw <= horizon; ++raw) {
    const Clock clock = static_cast<Clock>(raw);
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
        finish(clock, false, active.landing - 1U);
      }
    }
    value = next_value;
    maximum_value = std::max(maximum_value, value);
    seen.Insert(value);
    while (seen.Contains(mex)) ++mex;
    if (comb_active && mex != old_mex) finish(clock, true, old_mex);
    if (mex != old_mex) {
      epoch_start = clock;
      epoch_pre_tail_max = maximum_value;
    }
    if (!comb_active && subtraction && mex == old_mex && value > mex &&
        LowCandidateSide(value, static_cast<Clock>(clock + 1U), mex)) {
      active = ActiveComb{mex, epoch_start, epoch_pre_tail_max,
                          clock, value, value,
                          ActiveComb::Phase::expect_add};
      comb_active = true;
    }
  }
  result.final_value = value;
  result.final_mex = mex;
  result.maximum_value = maximum_value;
  result.seen_bytes = seen.Bytes();
  return result;
}

std::vector<std::uint32_t> GenerateFirstMetadata(Clock horizon,
                                                 Value maximum_value) {
  std::vector<std::uint32_t> metadata(
      static_cast<std::size_t>(maximum_value + 1U), 0U);
  Value value = 0U;
  for (std::uint64_t raw = 1U; raw <= horizon; ++raw) {
    const Clock clock = static_cast<Clock>(raw);
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool seen = candidate == 0U || metadata[candidate] != 0U;
    const bool subtraction = positive && !seen;
    value = subtraction ? candidate : value + clock;
    std::uint32_t& code = metadata[value];
    if (value != 0U && code == 0U) {
      code = static_cast<std::uint32_t>(clock << 1U) |
             (subtraction ? 1U : 0U);
    }
  }
  return metadata;
}

Origin DecodeOrigin(Value value,
                    const std::vector<std::uint32_t>& metadata) {
  if (value == 0U) return Origin{0U, 0U};
  if (value >= metadata.size() || metadata[value] == 0U)
    throw std::runtime_error("missing ancestry metadata");
  const std::uint32_t code = metadata[value];
  const Clock first = code >> 1U;
  const bool subtraction = (code & 1U) != 0U;
  return Origin{first, subtraction ? value + first : value - first};
}

AnchorOutcome TraceWithFixedAnchor(
    Value start, Value anchor, Clock epoch_start,
    const std::vector<std::uint32_t>& metadata) {
  if (start < anchor)
    throw std::runtime_error("anchor exceeds ancestry start");
  Value current = start;
  Clock length = 0U;
  while (true) {
    const Origin origin = DecodeOrigin(current, metadata);
    if (origin.first <= epoch_start)
      return AnchorOutcome{true, current, origin.first, length};
    const Origin parent_origin = DecodeOrigin(origin.parent, metadata);
    length = static_cast<Clock>(length + 1U);
    if (origin.parent < anchor)
      return AnchorOutcome{
          false, origin.parent, parent_origin.first, length};
    current = origin.parent;
  }
}

void AddAnchorObservation(const TerminalComb& terminal, Value anchor,
                          const AnchorOutcome& outcome,
                          AnchorStats& stats) {
  ++stats.candidates;
  if (!outcome.residual) {
    ++stats.progress;
    return;
  }
  ++stats.residual;
  stats.max_residual_length =
      std::max(stats.max_residual_length, outcome.length);
  if (anchor == 0U) {
    ++stats.zero_anchor_residual;
    return;
  }
  const Count ratio_ppm = outcome.endpoint * 1000000U / anchor;
  const Value excess = outcome.endpoint - anchor;
  stats.max_excess = std::max(stats.max_excess, excess);
  if (!stats.max_ratio_witness.present ||
      ratio_ppm > stats.max_ratio_ppm) {
    stats.max_ratio_ppm = ratio_ppm;
    stats.max_ratio_witness = AnchorWitness{
        true, terminal.target, terminal.epoch_start, terminal.start,
        terminal.end, terminal.entry, terminal.blocker, anchor,
        outcome.endpoint, outcome.endpoint_first, outcome.length};
  }
}

MemoResult ResolveMemo(Value start, Clock epoch_start,
                       const std::vector<std::uint32_t>& metadata,
                       std::unordered_map<Value, MemoResult>& memo) {
  std::vector<Value> stack;
  Value current = start;
  while (memo.find(current) == memo.end()) {
    const Origin origin = DecodeOrigin(current, metadata);
    if (origin.first <= epoch_start) {
      memo.emplace(current, MemoResult{current, 0U});
      break;
    }
    stack.push_back(current);
    current = origin.parent;
  }
  MemoResult result = memo.at(current);
  for (auto it = stack.rbegin(); it != stack.rend(); ++it) {
    result.distance = static_cast<Clock>(result.distance + 1U);
    memo.emplace(*it, result);
  }
  return memo.at(start);
}

Clock Percentile(std::vector<Clock> values, std::size_t numerator) {
  if (values.empty()) return 0U;
  std::sort(values.begin(), values.end());
  const std::size_t index = std::min(
      values.size() - 1U, values.size() * numerator / 100U);
  return values[index];
}

std::vector<Interval> MergeFreshIntervals(
    const std::vector<TerminalComb>& terminals, Value& total_mass,
    Count& overlap_violations) {
  std::vector<Interval> intervals;
  total_mass = 0U;
  for (const TerminalComb& terminal : terminals) {
    intervals.push_back({terminal.blocker + 1U, terminal.entry});
    total_mass += terminal.entry - terminal.blocker;
  }
  std::sort(intervals.begin(), intervals.end(), [](Interval left, Interval right) {
    return left.lower < right.lower ||
           (left.lower == right.lower && left.upper < right.upper);
  });
  std::vector<Interval> merged;
  overlap_violations = 0U;
  for (Interval interval : intervals) {
    if (merged.empty() || merged.back().upper < interval.lower) {
      merged.push_back(interval);
    } else {
      ++overlap_violations;
      merged.back().upper = std::max(merged.back().upper, interval.upper);
    }
  }
  return merged;
}

bool InIntervals(Value value, const std::vector<Interval>& intervals) {
  const auto it = std::upper_bound(
      intervals.begin(), intervals.end(), value,
      [](Value needle, Interval interval) { return needle < interval.lower; });
  return it != intervals.begin() &&
         std::prev(it)->lower <= value && value <= std::prev(it)->upper;
}

void AnalyzeTarget(Value target, const std::vector<std::size_t>& indices,
                   const std::vector<TerminalComb>& terminals,
                   const std::vector<std::uint32_t>& metadata,
                   GlobalStats& global,
                   std::vector<PathSummary>& path_summaries) {
  const Clock epoch_start = terminals[indices.front()].epoch_start;
  std::unordered_map<Value, MemoResult> memo;
  std::unordered_map<Value, Count> loads;
  memo.reserve(indices.size() * 32U + 1U);
  loads.reserve(indices.size() * 32U + 1U);
  std::vector<Clock> lengths;
  for (std::size_t index : indices) {
    const MemoResult result = ResolveMemo(
        terminals[index].blocker, epoch_start, metadata, memo);
    path_summaries[index] = {result.root, result.distance};
    lengths.push_back(result.distance);
    ++loads[terminals[index].blocker];
  }

  std::vector<Value> nodes;
  nodes.reserve(memo.size());
  for (const auto& item : memo) {
    nodes.push_back(item.first);
    global.ancestry_union.insert(item.first);
  }
  std::sort(nodes.begin(), nodes.end(), [&](Value left, Value right) {
    return DecodeOrigin(left, metadata).first >
           DecodeOrigin(right, metadata).first;
  });

  std::unordered_map<Value, Count> roots;
  Count max_root = 0U, max_node = 0U, max_edge = 0U;
  for (Value node : nodes) {
    const Count use = loads[node];
    if (use == 0U) continue;
    global.node_reuse[node] += use;
    global.total_path_nodes += use;
    max_node = std::max(max_node, use);
    const Origin origin = DecodeOrigin(node, metadata);
    if (origin.first <= epoch_start) {
      roots[node] += use;
      global.root_reuse[node] += use;
      max_root = std::max(max_root, roots[node]);
    } else {
      loads[origin.parent] += use;
      global.edge_children.insert(node);
      global.maximum_edge_reuse = std::max(global.maximum_edge_reuse, use);
      max_edge = std::max(max_edge, use);
    }
  }
  std::cout << "  target=" << target << " epochStart=" << epoch_start
            << " paths=" << indices.size() << " roots=" << roots.size()
            << " maxRootReuse=" << max_root << " nodeUnion=" << memo.size()
            << " maxNodeReuse=" << max_node << " maxEdgeReuse=" << max_edge
            << " length(p50/p90/p99/max)=" << Percentile(lengths, 50U)
            << '/' << Percentile(lengths, 90U) << '/'
            << Percentile(lengths, 99U) << '/'
            << *std::max_element(lengths.begin(), lengths.end()) << '\n';
}

void PrintGlobal(const std::vector<TerminalComb>& terminals,
                 const std::vector<PathSummary>& paths,
                 const std::vector<std::uint32_t>& metadata,
                 GlobalStats& global) {
  Count max_root_use = 0U, max_node_use = 0U;
  Value max_root = 0U;
  for (const auto& [root, use] : global.root_reuse) {
    if (max_root_use < use) { max_root_use = use; max_root = root; }
  }
  for (const auto& item : global.node_reuse)
    max_node_use = std::max(max_node_use, item.second);
  std::vector<Clock> lengths;
  Count length_sum = 0U, zero = 0U;
  Clock max_length = 0U;
  for (PathSummary path : paths) {
    lengths.push_back(path.length);
    length_sum += path.length;
    max_length = std::max(max_length, path.length);
    if (path.length == 0U) ++zero;
  }

  Value fresh_mass = 0U;
  Count interval_overlaps = 0U;
  const std::vector<Interval> fresh =
      MergeFreshIntervals(terminals, fresh_mass, interval_overlaps);
  Count overlap_union = 0U, overlap_weighted = 0U;
  std::unordered_set<Clock> first_times;
  for (Value node : global.ancestry_union) {
    first_times.insert(DecodeOrigin(node, metadata).first);
    if (InIntervals(node, fresh)) {
      ++overlap_union;
      overlap_weighted += global.node_reuse[node];
    }
  }
  std::cout << "ancestry capacity global:\n"
            << "  paths=" << paths.size() << " preTailRoots="
            << global.root_reuse.size() << " maxRootReuse=" << max_root_use
            << " maxRoot=" << max_root << '\n'
            << "  ancestryNodes(total/union/firstTimeUnion)="
            << global.total_path_nodes << '/' << global.ancestry_union.size()
            << '/' << first_times.size() << " timeEdgeUnion="
            << global.edge_children.size() << " maxNodeReuse=" << max_node_use
            << " maxTimeEdgeReuse=" << global.maximum_edge_reuse << '\n'
            << "  pathLength zero=" << zero << " average="
            << length_sum / paths.size() << " p50=" << Percentile(lengths, 50U)
            << " p90=" << Percentile(lengths, 90U)
            << " p99=" << Percentile(lengths, 99U)
            << " max=" << max_length << '\n'
            << "  freshIntervalMass=" << fresh_mass
            << " mergedIntervals=" << fresh.size()
            << " intervalOverlapViolations=" << interval_overlaps
            << " ancestryFreshOverlap(union/weighted)=" << overlap_union
            << '/' << overlap_weighted << " overlapPpm="
            << overlap_union * 1000000U / global.ancestry_union.size() << '\n';
}

void PrintAnchorStats(const char* label, const AnchorStats& stats) {
  std::cout << "  " << label << " candidates=" << stats.candidates
            << " residual=" << stats.residual
            << " progress=" << stats.progress << " residualPpm="
            << (stats.candidates == 0U
                    ? 0U
                    : stats.residual * 1000000U / stats.candidates)
            << " maxRootAnchorRatioPpm=" << stats.max_ratio_ppm
            << " maxRootMinusAnchor=" << stats.max_excess
            << " maxResidualPathLength=" << stats.max_residual_length
            << " zeroAnchorResidual=" << stats.zero_anchor_residual << '\n';
  if (stats.max_ratio_witness.present) {
    const AnchorWitness& w = stats.max_ratio_witness;
    std::cout << "    max-ratio witness target=" << w.target
              << " epochStart=" << w.epoch_start
              << " macro=" << w.macro_start << ".." << w.macro_end
              << " entry=" << w.entry << " blocker=" << w.blocker
              << " anchor=" << w.anchor << " root=" << w.endpoint
              << " rootFirst=" << w.endpoint_first
              << " pathLength=" << w.length << '\n';
  }
}

void AuditPreTailMaximum(
    const std::vector<TerminalComb>& terminals,
    const std::unordered_map<Value, std::vector<std::size_t>>& groups) {
  Count blockers_above = 0U, blockers_at_or_below = 0U;
  Count upward_above = 0U, upward_at_or_below = 0U;
  Count entries_above = 0U, entries_at_or_below = 0U;
  Count targets_ever_above = 0U, post_crossing_recurrences = 0U;
  Count global_max_ratio_ppm = 0U;
  Value ratio_target = 0U, ratio_max = 0U, ratio_blocker = 0U;
  Clock ratio_start = 0U;
  std::cout << "pre-tail maximum audit by target:\n";
  for (const auto& [target, indices] : groups) {
    const Value pre_tail_max = terminals[indices.front()].pre_tail_max;
    bool crossed = false;
    Clock first_crossing_start = 0U;
    Value first_crossing_blocker = 0U;
    Count local_above = 0U, local_below = 0U, local_recurrences = 0U;
    Count local_upward = 0U, local_upward_above = 0U;
    Count local_max_ratio_ppm = 0U;
    for (std::size_t position = 0U; position < indices.size(); ++position) {
      const TerminalComb& terminal = terminals[indices[position]];
      if (terminal.pre_tail_max != pre_tail_max)
        throw std::runtime_error("target group changed epoch pre-tail maximum");
      if (terminal.entry > pre_tail_max) {
        ++entries_above;
      } else {
        ++entries_at_or_below;
      }
      const bool above = terminal.blocker > pre_tail_max;
      if (pre_tail_max != 0U) {
        const Count ratio_ppm =
            terminal.blocker * 1000000U / pre_tail_max;
        local_max_ratio_ppm = std::max(local_max_ratio_ppm, ratio_ppm);
        if (ratio_ppm > global_max_ratio_ppm) {
          global_max_ratio_ppm = ratio_ppm;
          ratio_target = target;
          ratio_max = pre_tail_max;
          ratio_blocker = terminal.blocker;
          ratio_start = terminal.start;
        }
      }
      if (above) {
        ++blockers_above;
        ++local_above;
        if (!crossed) {
          crossed = true;
          first_crossing_start = terminal.start;
          first_crossing_blocker = terminal.blocker;
        }
      } else {
        ++blockers_at_or_below;
        ++local_below;
        if (crossed) {
          ++local_recurrences;
          ++post_crossing_recurrences;
        }
      }
      if (position != 0U) {
        const TerminalComb& previous = terminals[indices[position - 1U]];
        if (previous.blocker < terminal.blocker) {
          ++local_upward;
          if (above) {
            ++upward_above;
            ++local_upward_above;
          } else {
            ++upward_at_or_below;
          }
        }
      }
    }
    if (crossed) ++targets_ever_above;
    std::cout << "  target=" << target << " epochStart="
              << terminals[indices.front()].epoch_start
              << " preTailMax=" << pre_tail_max
              << " blockers(above/atOrBelow)=" << local_above << '/'
              << local_below << " upward(above/total)="
              << local_upward_above << '/' << local_upward
              << " maxBlockerMRatioPpm=" << local_max_ratio_ppm
              << " firstAboveStart=" << first_crossing_start
              << " firstAboveBlocker=" << first_crossing_blocker
              << " laterAtOrBelow=" << local_recurrences << '\n';
  }
  std::cout << "pre-tail maximum global:\n"
            << "  blockers(above/atOrBelow)=" << blockers_above << '/'
            << blockers_at_or_below << " upward(above/atOrBelow)="
            << upward_above << '/' << upward_at_or_below << '\n'
            << "  entries(above/atOrBelow)=" << entries_above << '/'
            << entries_at_or_below << " targetsEverAbove="
            << targets_ever_above << " laterAtOrBelow="
            << post_crossing_recurrences
            << " maxBlockerMRatioPpm=" << global_max_ratio_ppm << '\n'
            << "  max-ratio witness target=" << ratio_target
            << " start=" << ratio_start << " blocker=" << ratio_blocker
            << " preTailMax=" << ratio_max << '\n';
}

void AuditTerminalAnchors(
    const std::vector<TerminalComb>& terminals,
    const std::unordered_map<Value, std::vector<std::size_t>>& groups,
    const std::vector<std::uint32_t>& metadata) {
  AnchorStats blocker_self;
  AnchorStats previous_blocker_upward;
  Count blocker_not_above_target = 0U;
  Count previous_pairs = 0U, downward_pairs = 0U, equal_pairs = 0U;
  Count entry_anchor_inapplicable = 0U;
  for (const TerminalComb& terminal : terminals) {
    if (terminal.target >= terminal.blocker) {
      ++blocker_not_above_target;
    } else {
      AddAnchorObservation(
          terminal, terminal.blocker,
          TraceWithFixedAnchor(terminal.blocker, terminal.blocker,
                               terminal.epoch_start, metadata),
          blocker_self);
    }
    if (terminal.entry > terminal.blocker) ++entry_anchor_inapplicable;
  }
  std::cout << "fixed-anchor ancestry audit:\n"
            << "  theorem anchor=PhaseSearchNode.anchorParent; terminal macro"
               " has no canonical active-anchor field\n"
            << "  entry candidate inapplicable=" << entry_anchor_inapplicable
            << '/' << terminals.size()
            << " (blocker<entry violates anchor<=value)\n"
            << "  blockerNotAboveTarget=" << blocker_not_above_target << '\n';
  for (const auto& [target, indices] : groups) {
    AnchorStats local_self;
    AnchorStats local_previous;
    for (std::size_t index : indices) {
      const TerminalComb& terminal = terminals[index];
      if (terminal.target < terminal.blocker) {
        const AnchorOutcome outcome = TraceWithFixedAnchor(
            terminal.blocker, terminal.blocker, terminal.epoch_start,
            metadata);
        AddAnchorObservation(
            terminal, terminal.blocker, outcome, local_self);
      }
    }
    for (std::size_t position = 1U; position < indices.size(); ++position) {
      ++previous_pairs;
      const TerminalComb& previous = terminals[indices[position - 1U]];
      const TerminalComb& current = terminals[indices[position]];
      if (current.blocker < previous.blocker) {
        ++downward_pairs;
        continue;
      }
      if (current.blocker == previous.blocker) {
        ++equal_pairs;
        continue;
      }
      if (current.target >= current.blocker)
        throw std::runtime_error("upward terminal blocker is not above target");
      const AnchorOutcome outcome = TraceWithFixedAnchor(
          current.blocker, previous.blocker, current.epoch_start, metadata);
      AddAnchorObservation(current, previous.blocker, outcome,
                           previous_blocker_upward);
      AddAnchorObservation(current, previous.blocker, outcome,
                           local_previous);
    }
    std::cout << "  anchor target=" << target
              << " currentResidual=" << local_self.residual << '/'
              << local_self.candidates << " upwardPreviousResidual="
              << local_previous.residual << '/' << local_previous.candidates
              << '\n';
  }
  PrintAnchorStats("current-blocker (maximal admissible proxy)", blocker_self);
  std::cout << "  chronological same-target pairs=" << previous_pairs
            << " downwardExcluded=" << downward_pairs
            << " equalExcluded=" << equal_pairs << '\n';
  PrintAnchorStats("previous-blocker strict-upward proxy",
                   previous_blocker_upward);
}

bool AddRemountSource(
    Value target, Value root, std::size_t position,
    const std::vector<std::size_t>& indices,
    const std::vector<TerminalComb>& terminals, RemountStats& stats) {
  ++stats.sources;
  const TerminalComb& source = terminals[indices[position]];
  for (std::size_t later = position + 1U; later < indices.size(); ++later) {
    const TerminalComb& candidate = terminals[indices[later]];
    if (candidate.entry < root) {
      ++stats.resolved;
      const Clock distance = static_cast<Clock>(later - position);
      stats.waits.push_back(distance);
      if (!stats.max_wait_witness.present ||
          stats.max_wait_witness.episode_distance < distance) {
        stats.max_wait_witness = RemountWitness{
            true, target, root, source.start, candidate.start, distance};
      }
      return true;
    }
    ++stats.separator_checks;
    if (candidate.blocker < root) ++stats.separator_violations;
  }
  ++stats.unresolved;
  if (position + 1U == indices.size()) ++stats.unresolved_no_later;
  return false;
}

void MergeRemount(RemountStats& destination, const RemountStats& source) {
  destination.sources += source.sources;
  destination.resolved += source.resolved;
  destination.unresolved += source.unresolved;
  destination.unresolved_no_later += source.unresolved_no_later;
  destination.separator_checks += source.separator_checks;
  destination.separator_violations += source.separator_violations;
  destination.waits.insert(destination.waits.end(), source.waits.begin(),
                           source.waits.end());
  if (source.max_wait_witness.present &&
      (!destination.max_wait_witness.present ||
       destination.max_wait_witness.episode_distance <
           source.max_wait_witness.episode_distance)) {
    destination.max_wait_witness = source.max_wait_witness;
  }
}

void MergeBasin(BasinStats& destination, const BasinStats& source) {
  destination.paths += source.paths;
  destination.distinct_roots += source.distinct_roots;
  destination.root_above_pre_tail_max += source.root_above_pre_tail_max;
  destination.current_entry_below_root += source.current_entry_below_root;
  destination.current_blocker_at_least_root +=
      source.current_blocker_at_least_root;
  destination.current_separator_violations +=
      source.current_separator_violations;
  destination.max_root_reuse =
      std::max(destination.max_root_reuse, source.max_root_reuse);
  destination.maximum_root =
      std::max(destination.maximum_root, source.maximum_root);
  destination.maximum_root_pre_tail_max_ratio_ppm = std::max(
      destination.maximum_root_pre_tail_max_ratio_ppm,
      source.maximum_root_pre_tail_max_ratio_ppm);
  destination.unresolved_distinct_root_values.insert(
      destination.unresolved_distinct_root_values.end(),
      source.unresolved_distinct_root_values.begin(),
      source.unresolved_distinct_root_values.end());
  MergeRemount(destination.path_weighted, source.path_weighted);
  MergeRemount(destination.distinct_root, source.distinct_root);
}

void PrintRemountStats(const char* label, const RemountStats& stats) {
  std::cout << "    " << label << " sources=" << stats.sources
            << " resolved=" << stats.resolved
            << " unresolved=" << stats.unresolved
            << " unresolvedPpm="
            << (stats.sources == 0U
                    ? 0U
                    : stats.unresolved * 1000000U / stats.sources)
            << " unresolvedNoLater=" << stats.unresolved_no_later
            << " waitDistance(p50/p90/p99/max)="
            << Percentile(stats.waits, 50U) << '/'
            << Percentile(stats.waits, 90U) << '/'
            << Percentile(stats.waits, 99U) << '/'
            << (stats.max_wait_witness.present
                    ? stats.max_wait_witness.episode_distance
                    : 0U)
            << " separatorChecks=" << stats.separator_checks
            << " separatorViolations=" << stats.separator_violations << '\n';
  if (stats.max_wait_witness.present) {
    const RemountWitness& witness = stats.max_wait_witness;
    std::cout << "      max-wait witness target=" << witness.target
              << " root=" << witness.root
              << " sourceStart=" << witness.source_start
              << " escapeStart=" << witness.escape_start
              << " episodeDistance=" << witness.episode_distance << '\n';
  }
}

BasinStats AnalyzeBasinTarget(
    Value target, const std::vector<std::size_t>& indices,
    const std::vector<TerminalComb>& terminals,
    const std::vector<PathSummary>& paths) {
  BasinStats stats;
  stats.paths = indices.size();
  struct RootUse { std::size_t first_position = 0U; Count reuse = 0U; };
  std::unordered_map<Value, RootUse> roots;
  roots.reserve(indices.size() * 2U + 1U);
  for (std::size_t position = 0U; position < indices.size(); ++position) {
    const std::size_t index = indices[position];
    const TerminalComb& terminal = terminals[index];
    const Value root = paths[index].root;
    stats.maximum_root = std::max(stats.maximum_root, root);
    if (terminal.pre_tail_max == 0U) {
      if (root != 0U) ++stats.root_above_pre_tail_max;
    } else {
      if (terminal.pre_tail_max < root) ++stats.root_above_pre_tail_max;
      stats.maximum_root_pre_tail_max_ratio_ppm = std::max(
          stats.maximum_root_pre_tail_max_ratio_ppm,
          root * 1000000U / terminal.pre_tail_max);
    }
    if (terminal.entry < root) {
      ++stats.current_entry_below_root;
    } else if (root <= terminal.blocker) {
      ++stats.current_blocker_at_least_root;
    } else {
      ++stats.current_separator_violations;
    }
    auto [it, inserted] = roots.emplace(root, RootUse{position, 0U});
    (void)inserted;
    ++it->second.reuse;
    stats.max_root_reuse =
        std::max(stats.max_root_reuse, it->second.reuse);
    AddRemountSource(target, root, position, indices, terminals,
                     stats.path_weighted);
  }
  stats.distinct_roots = roots.size();
  for (const auto& [root, use] : roots) {
    if (!AddRemountSource(target, root, use.first_position, indices,
                          terminals, stats.distinct_root)) {
      stats.unresolved_distinct_root_values.push_back(root);
    }
  }
  return stats;
}

void AuditFiniteBasinRemount(
    const std::vector<TerminalComb>& terminals,
    const std::unordered_map<Value, std::vector<std::size_t>>& groups,
    const std::vector<PathSummary>& paths) {
  BasinStats global;
  std::cout << "finite-basin remount by target:\n";
  for (const auto& [target, indices] : groups) {
    const BasinStats stats =
        AnalyzeBasinTarget(target, indices, terminals, paths);
    MergeBasin(global, stats);
    std::cout << "  target=" << target << " paths=" << stats.paths
              << " distinctRoots=" << stats.distinct_roots
              << " maxRootReuse=" << stats.max_root_reuse
              << " maxRoot=" << stats.maximum_root
              << " maxRootPreTailMaxRatioPpm="
              << stats.maximum_root_pre_tail_max_ratio_ppm
              << " rootAbovePreTailMax="
              << stats.root_above_pre_tail_max
              << " current(entryBelow/blockerAtLeast/violation)="
              << stats.current_entry_below_root << '/'
              << stats.current_blocker_at_least_root << '/'
              << stats.current_separator_violations << '\n';
    PrintRemountStats("path-weighted", stats.path_weighted);
    PrintRemountStats("distinct-root(first use)", stats.distinct_root);
    if (!stats.unresolved_distinct_root_values.empty()) {
      std::vector<Value> unresolved = stats.unresolved_distinct_root_values;
      std::sort(unresolved.begin(), unresolved.end());
      std::cout << "    unresolved distinct roots=";
      for (Value root : unresolved) std::cout << ' ' << root;
      std::cout << '\n';
    }
  }
  std::cout << "finite-basin remount global:\n"
            << "  paths=" << global.paths
            << " distinctTargetRoots=" << global.distinct_roots
            << " maxRootReuse=" << global.max_root_reuse
            << " maxRoot=" << global.maximum_root
            << " maxRootPreTailMaxRatioPpm="
            << global.maximum_root_pre_tail_max_ratio_ppm
            << " rootAbovePreTailMax=" << global.root_above_pre_tail_max
            << " current(entryBelow/blockerAtLeast/violation)="
            << global.current_entry_below_root << '/'
            << global.current_blocker_at_least_root << '/'
            << global.current_separator_violations << '\n';
  PrintRemountStats("path-weighted", global.path_weighted);
  PrintRemountStats("distinct-root(first use)", global.distinct_root);
}

void AuditTerminalBlockerRemount(
    const std::vector<TerminalComb>& terminals,
    const std::unordered_map<Value, std::vector<std::size_t>>& groups) {
  RemountStats global;
  std::cout << "terminal-blocker nonuniform no-escape audit:\n";
  for (const auto& [target, indices] : groups) {
    RemountStats local;
    for (std::size_t position = 0U; position < indices.size(); ++position) {
      const TerminalComb& source = terminals[indices[position]];
      if (source.blocker <= target) continue;
      AddRemountSource(target, source.blocker, position, indices, terminals,
                       local);
    }
    PrintRemountStats(
        (std::string("terminal anchor target=") +
         std::to_string(target)).c_str(),
        local);
    MergeRemount(global, local);
  }
  PrintRemountStats("terminal anchor global", global);
}

GrowthWitness AddGrowthSource(
    Value target, Value root, std::size_t position,
    const std::vector<std::size_t>& indices,
    const std::vector<TerminalComb>& terminals, GrowthStats& stats) {
  ++stats.sources;
  const TerminalComb& source = terminals[indices[position]];
  GrowthWitness witness;
  witness.present = true;
  witness.target = target;
  witness.root = root;
  witness.source_start = source.start;
  witness.maximum_entry = root;
  witness.minimum_blocker = std::numeric_limits<Value>::max();
  Value previous_blocker = 0U;
  Value running_blocker_max = 0U;
  bool have_previous_blocker = false;

  for (std::size_t later = position + 1U; later < indices.size(); ++later) {
    const TerminalComb& candidate = terminals[indices[later]];
    if (candidate.entry < root) {
      witness.resolved = true;
      witness.escape_start = candidate.start;
      witness.clock_gap =
          static_cast<Count>(candidate.start) - source.start;
      ++stats.resolved;
      break;
    }

    ++witness.waiting_episodes;
    const Value interval_mass = candidate.entry - candidate.blocker;
    witness.fresh_mass += interval_mass;
    witness.maximum_entry =
        std::max(witness.maximum_entry, candidate.entry);
    witness.minimum_blocker =
        std::min(witness.minimum_blocker, candidate.blocker);
    witness.maximum_blocker =
        std::max(witness.maximum_blocker, candidate.blocker);
    if (candidate.end - candidate.start != 2U * interval_mass)
      ++stats.duration_identity_violations;
    if (witness.fresh_mass < witness.waiting_episodes)
      ++stats.mass_episode_lower_bound_violations;
    if (witness.fresh_mass > witness.maximum_entry - root)
      ++stats.fresh_hull_violations;

    if (have_previous_blocker) {
      if (previous_blocker < candidate.blocker) {
        ++witness.blocker_rises;
        ++stats.blocker_rises;
        if (candidate.blocker <= running_blocker_max)
          ++stats.blocker_rises_not_records;
      } else if (candidate.blocker < previous_blocker) {
        ++witness.blocker_falls;
        ++stats.blocker_falls;
      } else {
        ++stats.blocker_equals;
      }
    }
    if (!have_previous_blocker || running_blocker_max < candidate.blocker) {
      ++witness.blocker_records;
      ++stats.blocker_records;
      running_blocker_max = candidate.blocker;
    }
    previous_blocker = candidate.blocker;
    have_previous_blocker = true;
  }
  if (!witness.resolved) ++stats.unresolved;
  if (witness.minimum_blocker == std::numeric_limits<Value>::max())
    witness.minimum_blocker = 0U;
  stats.waiting_episodes += witness.waiting_episodes;
  stats.fresh_mass += witness.fresh_mass;
  stats.active_clock_mass += 2U * witness.fresh_mass;
  if (witness.blocker_rises != 0U) ++stats.sequences_with_rise;
  if (witness.blocker_falls != 0U) ++stats.sequences_with_fall;

  const Value hull = witness.maximum_entry - root;
  if (hull != 0U) {
    stats.maximum_hull_density_ppm = std::max(
        stats.maximum_hull_density_ppm,
        witness.fresh_mass * 1000000U / hull);
  }
  if (witness.resolved && witness.clock_gap != 0U) {
    const Count active_clock = 2U * witness.fresh_mass;
    if (witness.clock_gap < active_clock) ++stats.clock_gap_violations;
    stats.maximum_clock_occupancy_ppm = std::max(
        stats.maximum_clock_occupancy_ppm,
        active_clock * 1000000U / witness.clock_gap);
  }
  GrowthWitness& maximum = witness.resolved
      ? stats.maximum_resolved_wait_witness
      : stats.maximum_unresolved_wait_witness;
  if (!maximum.present ||
      maximum.waiting_episodes < witness.waiting_episodes) {
    maximum = witness;
  }
  return witness;
}

void MergeGrowth(GrowthStats& destination, const GrowthStats& source) {
  destination.sources += source.sources;
  destination.resolved += source.resolved;
  destination.unresolved += source.unresolved;
  destination.waiting_episodes += source.waiting_episodes;
  destination.fresh_mass += source.fresh_mass;
  destination.active_clock_mass += source.active_clock_mass;
  destination.duration_identity_violations +=
      source.duration_identity_violations;
  destination.mass_episode_lower_bound_violations +=
      source.mass_episode_lower_bound_violations;
  destination.fresh_hull_violations += source.fresh_hull_violations;
  destination.clock_gap_violations += source.clock_gap_violations;
  destination.blocker_rises += source.blocker_rises;
  destination.blocker_falls += source.blocker_falls;
  destination.blocker_equals += source.blocker_equals;
  destination.blocker_records += source.blocker_records;
  destination.blocker_rises_not_records +=
      source.blocker_rises_not_records;
  destination.sequences_with_rise += source.sequences_with_rise;
  destination.sequences_with_fall += source.sequences_with_fall;
  destination.maximum_hull_density_ppm = std::max(
      destination.maximum_hull_density_ppm,
      source.maximum_hull_density_ppm);
  destination.maximum_clock_occupancy_ppm = std::max(
      destination.maximum_clock_occupancy_ppm,
      source.maximum_clock_occupancy_ppm);
  const auto merge_witness = [](GrowthWitness& destination_witness,
                                const GrowthWitness& source_witness) {
    if (source_witness.present &&
        (!destination_witness.present ||
         destination_witness.waiting_episodes <
             source_witness.waiting_episodes))
      destination_witness = source_witness;
  };
  merge_witness(destination.maximum_resolved_wait_witness,
                source.maximum_resolved_wait_witness);
  merge_witness(destination.maximum_unresolved_wait_witness,
                source.maximum_unresolved_wait_witness);
}

void PrintGrowthStats(const char* label, const GrowthStats& stats) {
  std::cout << "  " << label << " sources=" << stats.sources
            << " resolved/unresolved=" << stats.resolved << '/'
            << stats.unresolved
            << " waitingEpisodes=" << stats.waiting_episodes
            << " freshMass=" << stats.fresh_mass
            << " activeClockMass=" << stats.active_clock_mass << '\n'
            << "    exactChecks duration/mass>=episodes/hull/clock violations="
            << stats.duration_identity_violations << '/'
            << stats.mass_episode_lower_bound_violations << '/'
            << stats.fresh_hull_violations << '/'
            << stats.clock_gap_violations
            << " maxHullDensityPpm=" << stats.maximum_hull_density_ppm
            << " maxClockOccupancyPpm="
            << stats.maximum_clock_occupancy_ppm << '\n'
            << "    blocker rises/falls/equals/records="
            << stats.blocker_rises << '/' << stats.blocker_falls << '/'
            << stats.blocker_equals << '/' << stats.blocker_records
            << " risesNotRecords=" << stats.blocker_rises_not_records
            << " sequencesWithRise/Fall=" << stats.sequences_with_rise
            << '/' << stats.sequences_with_fall << '\n';
  const auto print_witness = [](const char* kind,
                                const GrowthWitness& witness) {
    if (!witness.present) return;
    const Value hull = witness.maximum_entry - witness.root;
    std::cout << "    max-" << kind << " growth witness target="
              << witness.target
              << " root=" << witness.root
              << " sourceStart=" << witness.source_start
              << " escapeStart=" << witness.escape_start
              << " resolved=" << witness.resolved
              << " waitingEpisodes=" << witness.waiting_episodes
              << " freshMass=" << witness.fresh_mass
              << " maxEntry=" << witness.maximum_entry
              << " hull=" << hull
              << " hullDensityPpm="
              << (hull == 0U
                      ? 0U
                      : witness.fresh_mass * 1000000U / hull)
              << " min/maxBlocker=" << witness.minimum_blocker << '/'
              << witness.maximum_blocker
              << " blockerRises/Falls/Records=" << witness.blocker_rises
              << '/' << witness.blocker_falls << '/'
              << witness.blocker_records
              << " clockGap=" << witness.clock_gap
              << " clockOccupancyPpm="
              << (witness.clock_gap == 0U
                      ? 0U
                      : 2U * witness.fresh_mass * 1000000U /
                            witness.clock_gap)
              << '\n';
  };
  print_witness("resolved-wait", stats.maximum_resolved_wait_witness);
  print_witness("unresolved-wait", stats.maximum_unresolved_wait_witness);
}

void AuditRemountGrowth(
    const std::vector<TerminalComb>& terminals,
    const std::unordered_map<Value, std::vector<std::size_t>>& groups,
    const std::vector<PathSummary>& paths) {
  GrowthStats global;
  std::cout << "fixed-root remount fresh-mass audit:\n";
  for (const auto& [target, indices] : groups) {
    struct RootFirstUse { std::size_t position = 0U; };
    std::unordered_map<Value, RootFirstUse> roots;
    roots.reserve(indices.size() * 2U + 1U);
    for (std::size_t position = 0U; position < indices.size(); ++position) {
      const Value root = paths[indices[position]].root;
      roots.emplace(root, RootFirstUse{position});
    }
    GrowthStats local;
    for (const auto& [root, use] : roots)
      AddGrowthSource(target, root, use.position, indices, terminals, local);
    PrintGrowthStats((std::string("target=") + std::to_string(target)).c_str(),
                     local);
    MergeGrowth(global, local);
  }
  PrintGrowthStats("global distinct-root(first use)", global);
}

void AddRecordPaymentSource(
    Value target, Value root, std::size_t position,
    const std::vector<std::size_t>& indices,
    const std::vector<TerminalComb>& terminals, RecordPaymentStats& stats) {
  ++stats.sources;
  const TerminalComb& source = terminals[indices[position]];
  Value entry_hull = 0U;
  Value blocker_record = 0U;
  for (std::size_t prefix = 0U; prefix <= position; ++prefix) {
    const TerminalComb& terminal = terminals[indices[prefix]];
    entry_hull = std::max(entry_hull, terminal.entry);
    blocker_record = std::max(blocker_record, terminal.blocker);
  }
  const Value initial_blocker_record = blocker_record;
  Value previous_blocker = source.blocker;
  Count source_q = 0U;
  Count source_gap = 0U;
  Count source_waiting = 0U;

  for (std::size_t later = position + 1U; later < indices.size(); ++later) {
    const TerminalComb& candidate = terminals[indices[later]];
    if (candidate.entry < root) break;
    ++stats.waiting_transitions;
    ++source_waiting;
    const Value q = candidate.entry - candidate.blocker;
    source_q += q;
    if (previous_blocker < candidate.blocker) {
      if (candidate.blocker <= blocker_record) {
        ++stats.nonrecord_rises;
      } else {
        ++stats.record_rises;
        if (candidate.blocker < entry_hull) {
          ++stats.record_below_entry_hull;
        } else {
          const Value gap = candidate.blocker - entry_hull;
          source_gap += gap;
          stats.cumulative_gap += gap;
          stats.record_fresh_mass += q;
          const Count ratio_ppm =
              q == 0U ? 0U : gap * 1000000U / q;
          if (!stats.sharp_gap_witness.present ||
              stats.maximum_gap_over_q_ppm < ratio_ppm) {
            stats.maximum_gap_over_q_ppm = ratio_ppm;
            stats.sharp_gap_witness = GapWitness{
                true, target, root, source.start, candidate.start,
                entry_hull, candidate.blocker, candidate.entry, gap, q,
                ratio_ppm};
          }
        }
      }
    } else if (candidate.blocker < previous_blocker) {
      ++stats.falls;
      const Value drop = previous_blocker - candidate.blocker;
      stats.descent_drop += drop;
      stats.descent_fresh_mass += q;
      if (drop < q) ++stats.descent_mass_exceeds_drop;
    } else {
      ++stats.equals;
    }
    entry_hull = std::max(entry_hull, candidate.entry);
    blocker_record = std::max(blocker_record, candidate.blocker);
    previous_blocker = candidate.blocker;
  }

  const Value record_gain = blocker_record - initial_blocker_record;
  stats.cumulative_record_gain += record_gain;
  const Count denominator = source_q + root;
  if (denominator != 0U) {
    const Count gap_ratio = source_gap * 1000000U / denominator;
    const Count gain_ratio = record_gain * 1000000U / denominator;
    if (!stats.sharp_source_gap_witness.present ||
        stats.maximum_source_gap_over_q_plus_root_ppm < gap_ratio) {
      stats.maximum_source_gap_over_q_plus_root_ppm = gap_ratio;
      stats.sharp_source_gap_witness = SourcePaymentWitness{
          true, target, root, source.start, source_waiting, source_q,
          source_gap, record_gain, gap_ratio};
    }
    stats.maximum_source_gain_over_q_plus_root_ppm = std::max(
        stats.maximum_source_gain_over_q_plus_root_ppm, gain_ratio);
  }
  if (source_q + root < source_gap) ++stats.gap_exceeds_q_plus_root;
  if (source_q + root < record_gain) ++stats.gain_exceeds_q_plus_root;
}

void MergeRecordPayment(RecordPaymentStats& destination,
                        const RecordPaymentStats& source) {
  destination.sources += source.sources;
  destination.waiting_transitions += source.waiting_transitions;
  destination.record_rises += source.record_rises;
  destination.nonrecord_rises += source.nonrecord_rises;
  destination.falls += source.falls;
  destination.equals += source.equals;
  destination.record_below_entry_hull += source.record_below_entry_hull;
  destination.descent_mass_exceeds_drop +=
      source.descent_mass_exceeds_drop;
  destination.cumulative_gap += source.cumulative_gap;
  destination.record_fresh_mass += source.record_fresh_mass;
  destination.descent_drop += source.descent_drop;
  destination.descent_fresh_mass += source.descent_fresh_mass;
  destination.cumulative_record_gain += source.cumulative_record_gain;
  destination.gap_exceeds_q_plus_root += source.gap_exceeds_q_plus_root;
  destination.gain_exceeds_q_plus_root += source.gain_exceeds_q_plus_root;
  destination.maximum_gap_over_q_ppm = std::max(
      destination.maximum_gap_over_q_ppm, source.maximum_gap_over_q_ppm);
  destination.maximum_source_gap_over_q_plus_root_ppm = std::max(
      destination.maximum_source_gap_over_q_plus_root_ppm,
      source.maximum_source_gap_over_q_plus_root_ppm);
  destination.maximum_source_gain_over_q_plus_root_ppm = std::max(
      destination.maximum_source_gain_over_q_plus_root_ppm,
      source.maximum_source_gain_over_q_plus_root_ppm);
  if (source.sharp_gap_witness.present &&
      (!destination.sharp_gap_witness.present ||
       destination.sharp_gap_witness.ratio_ppm <
           source.sharp_gap_witness.ratio_ppm)) {
    destination.sharp_gap_witness = source.sharp_gap_witness;
  }
  if (source.sharp_source_gap_witness.present &&
      (!destination.sharp_source_gap_witness.present ||
       destination.sharp_source_gap_witness.ratio_ppm <
           source.sharp_source_gap_witness.ratio_ppm)) {
    destination.sharp_source_gap_witness =
        source.sharp_source_gap_witness;
  }
}

void PrintRecordPayment(const char* label,
                        const RecordPaymentStats& stats) {
  std::cout << "  " << label << " sources=" << stats.sources
            << " transitions=" << stats.waiting_transitions
            << " record/nonrecordRise/fall/equal=" << stats.record_rises
            << '/' << stats.nonrecord_rises << '/' << stats.falls << '/'
            << stats.equals << '\n'
            << "    exact violations recordBelowEntryHull/descentQ>drop="
            << stats.record_below_entry_hull << '/'
            << stats.descent_mass_exceeds_drop
            << " gap/Q+root counterexamples="
            << stats.gap_exceeds_q_plus_root
            << " gain/Q+root counterexamples="
            << stats.gain_exceeds_q_plus_root << '\n'
            << "    gap/recordQ=" << stats.cumulative_gap << '/'
            << stats.record_fresh_mass
            << " descentDrop/descentQ=" << stats.descent_drop << '/'
            << stats.descent_fresh_mass
            << " cumulativeRecordGain=" << stats.cumulative_record_gain
            << '\n'
            << "    maxPpm gap/q=" << stats.maximum_gap_over_q_ppm
            << " sourceGap/(Q+root)="
            << stats.maximum_source_gap_over_q_plus_root_ppm
            << " sourceGain/(Q+root)="
            << stats.maximum_source_gain_over_q_plus_root_ppm << '\n';
  if (stats.sharp_gap_witness.present) {
    const GapWitness& witness = stats.sharp_gap_witness;
    std::cout << "    sharp-gap witness target=" << witness.target
              << " root=" << witness.root
              << " sourceStart=" << witness.source_start
              << " riseStart=" << witness.rise_start
              << " oldEntryHull=" << witness.previous_entry_hull
              << " blocker/entry=" << witness.blocker << '/'
              << witness.entry << " gap/q=" << witness.gap << '/'
              << witness.fresh_mass
              << " ratioPpm=" << witness.ratio_ppm << '\n';
  }
  if (stats.sharp_source_gap_witness.present) {
    const SourcePaymentWitness& witness =
        stats.sharp_source_gap_witness;
    std::cout << "    sharp-source-gap witness target=" << witness.target
              << " root=" << witness.root
              << " sourceStart=" << witness.source_start
              << " waiting=" << witness.waiting_transitions
              << " Q/gap/gain=" << witness.fresh_mass << '/'
              << witness.cumulative_gap << '/' << witness.record_gain
              << " gapOverQPlusRootPpm=" << witness.ratio_ppm << '\n';
  }
}

void AuditRecordGapPayment(
    const std::vector<TerminalComb>& terminals,
    const std::unordered_map<Value, std::vector<std::size_t>>& groups,
    const std::vector<PathSummary>& paths) {
  RecordPaymentStats global;
  std::cout << "fixed-root record-gap/descent-payment audit:\n";
  for (const auto& [target, indices] : groups) {
    std::unordered_map<Value, std::size_t> roots;
    roots.reserve(indices.size() * 2U + 1U);
    for (std::size_t position = 0U; position < indices.size(); ++position)
      roots.emplace(paths[indices[position]].root, position);
    RecordPaymentStats local;
    for (const auto& [root, position] : roots)
      AddRecordPaymentSource(target, root, position, indices, terminals,
                             local);
    PrintRecordPayment(
        (std::string("target=") + std::to_string(target)).c_str(), local);
    MergeRecordPayment(global, local);
  }
  PrintRecordPayment("global distinct-root(first use)", global);
}

GapHistoryCounts CountGapHistory(
    const GapHistoryEvent& event,
    const std::vector<std::uint32_t>& metadata,
    const std::vector<Interval>& history_fresh_intervals) {
  GapHistoryCounts counts;
  counts.mass = event.upper - event.lower + 1U;
  for (Value value = event.lower; value <= event.upper; ++value) {
    const std::uint32_t code = metadata[value];
    const Clock first = code >> 1U;
    if (code == 0U) {
      ++counts.unvisited_by_end;
      ++counts.unvisited_by_horizon;
      continue;
    }
    ++counts.visited_by_horizon;
    if (event.end < first) {
      ++counts.unvisited_by_end;
      ++counts.first_after_record;
      counts.maximum_future_delay =
          std::max(counts.maximum_future_delay, first - event.end);
      continue;
    }
    ++counts.visited_by_end;
    if (first <= event.start) ++counts.visited_by_start;
    if (first <= event.epoch_start) {
      ++counts.first_pre_tail;
    } else if (first <= event.start) {
      ++counts.first_tail_before_start;
    } else {
      ++counts.first_during_record_episode;
    }
    if ((code & 1U) != 0U) {
      ++counts.first_subtraction;
    } else {
      ++counts.first_addition;
    }
    if (InIntervals(value, history_fresh_intervals)) {
      ++counts.first_history_terminal_comb;
    } else {
      ++counts.first_outside_history_terminal_comb;
    }
  }
  return counts;
}

void MergeGapHistory(GapHistoryCounts& destination,
                     const GapHistoryCounts& source) {
  destination.mass += source.mass;
  destination.visited_by_start += source.visited_by_start;
  destination.visited_by_end += source.visited_by_end;
  destination.unvisited_by_end += source.unvisited_by_end;
  destination.visited_by_horizon += source.visited_by_horizon;
  destination.first_after_record += source.first_after_record;
  destination.unvisited_by_horizon += source.unvisited_by_horizon;
  destination.maximum_future_delay = std::max(
      destination.maximum_future_delay, source.maximum_future_delay);
  destination.first_pre_tail += source.first_pre_tail;
  destination.first_tail_before_start += source.first_tail_before_start;
  destination.first_during_record_episode +=
      source.first_during_record_episode;
  destination.first_subtraction += source.first_subtraction;
  destination.first_addition += source.first_addition;
  destination.first_history_terminal_comb +=
      source.first_history_terminal_comb;
  destination.first_outside_history_terminal_comb +=
      source.first_outside_history_terminal_comb;
}

void PrintGapHistory(const GapHistoryEvent& event,
                     const GapHistoryCounts& counts) {
  std::cout << "  target=" << event.target << " epochStart="
            << event.epoch_start << " record=" << event.start << ".."
            << event.end << " gap=[" << event.lower << ',' << event.upper
            << "] mass=" << counts.mass
            << " visited(start/end)/unvisitedEnd="
            << counts.visited_by_start << '/' << counts.visited_by_end << '/'
            << counts.unvisited_by_end
            << " visitedEndPpm="
            << counts.visited_by_end * 1000000U / counts.mass
            << " visited(horizon/afterRecord)/unvisitedHorizon="
            << counts.visited_by_horizon << '/'
            << counts.first_after_record << '/'
            << counts.unvisited_by_horizon
            << " futureCoveragePpm="
            << (counts.unvisited_by_end == 0U
                    ? 0U
                    : counts.first_after_record * 1000000U /
                        counts.unvisited_by_end)
            << " maxFutureDelay=" << counts.maximum_future_delay << '\n'
            << "    first preTail/tailBefore/during="
            << counts.first_pre_tail << '/'
            << counts.first_tail_before_start << '/'
            << counts.first_during_record_episode
            << " branch sub/add=" << counts.first_subtraction << '/'
            << counts.first_addition
            << " historyTerminalComb/outside="
            << counts.first_history_terminal_comb << '/'
            << counts.first_outside_history_terminal_comb << '\n';
}

void PrintGapCohort(const char* label, Count events,
                    const GapHistoryCounts& counts) {
  std::cout << "  " << label << " events=" << events
            << " mass=" << counts.mass
            << " visitedByRecord=" << counts.visited_by_end
            << " firstAfterRecord=" << counts.first_after_record
            << " stillUnvisited=" << counts.unvisited_by_horizon
            << " futureCoveragePpm="
            << (counts.unvisited_by_end == 0U
                    ? 0U
                    : counts.first_after_record * 1000000U /
                        counts.unvisited_by_end)
            << " maxFutureDelay=" << counts.maximum_future_delay << '\n';
}

void AuditRecordGapHistory(
    const std::vector<TerminalComb>& terminals,
    const std::unordered_map<Value, std::vector<std::size_t>>& groups,
    const std::vector<std::uint32_t>& metadata) {
  std::vector<GapHistoryEvent> events;
  Count nonrecord_rises = 0U, record_below_entry_hull = 0U;
  for (const auto& [target, indices] : groups) {
    if (indices.empty()) continue;
    Value entry_hull = terminals[indices.front()].entry;
    Value blocker_record = terminals[indices.front()].blocker;
    for (std::size_t position = 1U; position < indices.size(); ++position) {
      const TerminalComb& previous = terminals[indices[position - 1U]];
      const TerminalComb& current = terminals[indices[position]];
      if (previous.blocker < current.blocker) {
        if (current.blocker <= blocker_record) {
          ++nonrecord_rises;
        } else if (current.blocker < entry_hull) {
          ++record_below_entry_hull;
        } else if (entry_hull < current.blocker) {
          events.push_back(GapHistoryEvent{
              target, current.epoch_start, current.start, current.end,
              entry_hull + 1U, current.blocker});
        }
      }
      entry_hull = std::max(entry_hull, current.entry);
      blocker_record = std::max(blocker_record, current.blocker);
    }
  }

  Value history_mass = 0U;
  Count history_overlap = 0U;
  const std::vector<Interval> history_fresh_intervals =
      MergeFreshIntervals(terminals, history_mass, history_overlap);
  std::cout << "record-gap global-history audit events=" << events.size()
            << " nonrecordRises=" << nonrecord_rises
            << " recordBelowEntryHull=" << record_below_entry_hull
            << " historyFreshMass=" << history_mass
            << " historyFreshOverlap=" << history_overlap << '\n';
  GapHistoryCounts weighted;
  GapHistoryCounts cohort_200k, cohort_2m;
  Count cohort_200k_events = 0U, cohort_2m_events = 0U;
  for (const GapHistoryEvent& event : events) {
    const GapHistoryCounts counts =
        CountGapHistory(event, metadata, history_fresh_intervals);
    MergeGapHistory(weighted, counts);
    if (event.end <= 200000U) {
      ++cohort_200k_events;
      MergeGapHistory(cohort_200k, counts);
    }
    if (event.end <= 2000000U) {
      ++cohort_2m_events;
      MergeGapHistory(cohort_2m, counts);
    }
    PrintGapHistory(event, counts);
  }
  PrintGapCohort("record-gap cohort<=200k", cohort_200k_events,
                 cohort_200k);
  PrintGapCohort("record-gap cohort<=2M", cohort_2m_events, cohort_2m);

  std::vector<Interval> gap_intervals;
  gap_intervals.reserve(events.size());
  for (const GapHistoryEvent& event : events)
    gap_intervals.push_back(Interval{event.lower, event.upper});
  std::sort(gap_intervals.begin(), gap_intervals.end(),
            [](Interval left, Interval right) {
              return left.lower < right.lower ||
                  (left.lower == right.lower && left.upper < right.upper);
            });
  std::vector<Interval> gap_union;
  Count gap_overlap_events = 0U;
  for (const Interval interval : gap_intervals) {
    if (gap_union.empty() || gap_union.back().upper + 1U < interval.lower) {
      gap_union.push_back(interval);
    } else {
      if (interval.lower <= gap_union.back().upper) ++gap_overlap_events;
      gap_union.back().upper =
          std::max(gap_union.back().upper, interval.upper);
    }
  }

  Count union_mass = 0U, distinct_visited_resources = 0U;
  Count distinct_subtraction = 0U, distinct_addition = 0U;
  Count distinct_history_comb = 0U, distinct_outside_comb = 0U;
  Count maximum_witness_reuse = 0U;
  for (const Interval interval : gap_union)
    union_mass += interval.upper - interval.lower + 1U;
  if (gap_overlap_events == 0U) {
    distinct_visited_resources = weighted.visited_by_end;
    distinct_subtraction = weighted.first_subtraction;
    distinct_addition = weighted.first_addition;
    distinct_history_comb = weighted.first_history_terminal_comb;
    distinct_outside_comb = weighted.first_outside_history_terminal_comb;
    maximum_witness_reuse = distinct_visited_resources == 0U ? 0U : 1U;
  } else {
    for (const Interval interval : gap_union) {
      for (Value value = interval.lower; value <= interval.upper; ++value) {
        const std::uint32_t code = metadata[value];
        if (code == 0U) continue;
        const Clock first = code >> 1U;
        Count reuse = 0U;
        for (const GapHistoryEvent& event : events) {
          if (event.lower <= value && value <= event.upper &&
              first <= event.end)
            ++reuse;
        }
        if (reuse == 0U) continue;
        ++distinct_visited_resources;
        maximum_witness_reuse = std::max(maximum_witness_reuse, reuse);
        if ((code & 1U) != 0U)
          ++distinct_subtraction;
        else
          ++distinct_addition;
        if (InIntervals(value, history_fresh_intervals))
          ++distinct_history_comb;
        else
          ++distinct_outside_comb;
      }
    }
  }
  std::cout << "record-gap history global weightedMass=" << weighted.mass
            << " visited(start/end)/unvisitedEnd="
            << weighted.visited_by_start << '/' << weighted.visited_by_end
            << '/' << weighted.unvisited_by_end
            << " visitedEndPpm="
            << (weighted.mass == 0U
                    ? 0U
                    : weighted.visited_by_end * 1000000U / weighted.mass)
            << " visited(horizon/afterRecord)/unvisitedHorizon="
            << weighted.visited_by_horizon << '/'
            << weighted.first_after_record << '/'
            << weighted.unvisited_by_horizon
            << " futureCoveragePpm="
            << (weighted.unvisited_by_end == 0U
                    ? 0U
                    : weighted.first_after_record * 1000000U /
                        weighted.unvisited_by_end)
            << " maxFutureDelay=" << weighted.maximum_future_delay
            << '\n'
            << "  weighted first preTail/tailBefore/during="
            << weighted.first_pre_tail << '/'
            << weighted.first_tail_before_start << '/'
            << weighted.first_during_record_episode
            << " branch sub/add=" << weighted.first_subtraction << '/'
            << weighted.first_addition
            << " historyTerminalComb/outside="
            << weighted.first_history_terminal_comb << '/'
            << weighted.first_outside_history_terminal_comb << '\n'
            << "  distinct unionMass=" << union_mass
            << " overlapEvents=" << gap_overlap_events
            << " visitedResources=" << distinct_visited_resources
            << " resourceCoveragePpm="
            << (union_mass == 0U
                    ? 0U
                    : distinct_visited_resources * 1000000U / union_mass)
            << " witnessReuseMax=" << maximum_witness_reuse
            << " branch sub/add=" << distinct_subtraction << '/'
            << distinct_addition
            << " historyTerminalComb/outside=" << distinct_history_comb
            << '/' << distinct_outside_comb << '\n';
}

void Analyze(Clock horizon) {
  const MacroData macro = GenerateMacroData(horizon);
  std::cout << "target-ancestry horizon=" << horizon
            << " finalValue=" << macro.final_value << " mex=" << macro.final_mex
            << " terminals=" << macro.terminals.size()
            << " maxValue=" << macro.maximum_value
            << " seenMiB=" << macro.seen_bytes / (1024U * 1024U) << '\n'
            << "  firstMetadataMiB="
            << (macro.maximum_value + 1U) * sizeof(std::uint32_t) /
                   (1024ULL * 1024ULL) << '\n';
  const std::vector<std::uint32_t> metadata =
      GenerateFirstMetadata(horizon, macro.maximum_value);
  std::unordered_map<Value, std::vector<std::size_t>> groups;
  for (std::size_t i = 0U; i < macro.terminals.size(); ++i)
    groups[macro.terminals[i].target].push_back(i);
  GlobalStats global;
  global.node_reuse.reserve(macro.terminals.size() * 64U + 1U);
  global.ancestry_union.reserve(macro.terminals.size() * 64U + 1U);
  global.edge_children.reserve(macro.terminals.size() * 64U + 1U);
  std::vector<PathSummary> paths(macro.terminals.size());
  std::cout << "ancestry capacity by target:\n";
  for (const auto& [target, indices] : groups)
    AnalyzeTarget(target, indices, macro.terminals, metadata, global, paths);
  PrintGlobal(macro.terminals, paths, metadata, global);
  AuditPreTailMaximum(macro.terminals, groups);
  AuditTerminalAnchors(macro.terminals, groups, metadata);
  AuditFiniteBasinRemount(macro.terminals, groups, paths);
  AuditTerminalBlockerRemount(macro.terminals, groups);
  AuditRemountGrowth(macro.terminals, groups, paths);
  AuditRecordGapPayment(macro.terminals, groups, paths);
  AuditRecordGapHistory(macro.terminals, groups, metadata);
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
