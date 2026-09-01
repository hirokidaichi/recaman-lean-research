// Maximal target-comb extraction audit on the exact standard prefix.
//
// Maximal episodes are selected greedily: a fresh subtraction landing on the
// low-candidate side starts an episode only when no episode is active.  The
// low rail of one history-terminated episode has L clocks and its CombRun has
// L-1 successful CombStep clocks; the final low clock is the terminal gate.

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

enum class Arrival : std::uint8_t {
  none = 0U,
  initial = 1U,
  subtraction_fresh = 2U,
  addition_fresh = 3U,
  addition_repeat = 4U
};

enum class EpisodeKind : std::uint8_t {
  history_terminal,
  target_terminal,
  horizon_censored
};

struct Epoch {
  Value target = 0U;
  Clock start = 0U;
  Clock finish = 0U;
};

struct Episode {
  Value target = 0U;
  Clock epoch_start = 0U;
  std::uint16_t epoch_index = 0U;
  Clock start = 0U;
  Clock end = 0U;
  Value entry = 0U;
  Value blocker = 0U;
  Clock rails = 0U;
  EpisodeKind kind = EpisodeKind::history_terminal;
};

struct ActiveComb {
  enum class Phase : std::uint8_t { expect_add, expect_resolution };
  Value target = 0U;
  Clock epoch_start = 0U;
  std::uint16_t epoch_index = 0U;
  Clock start = 0U;
  Value entry = 0U;
  Value landing = 0U;
  Clock rails = 0U;
  Phase phase = Phase::expect_add;
};

struct NonfreshLow {
  Value target = 0U;
  Value value = 0U;
  Clock epoch_start = 0U;
  Clock time = 0U;
};

struct OriginInfo {
  Clock first = 0U;
  Value parent = 0U;
  Value mex_at_first = 0U;
  bool subtraction = false;
};

struct RunData {
  std::vector<Epoch> epochs;
  std::vector<Episode> episodes;
  std::vector<NonfreshLow> nonfresh_lows;
  std::vector<std::uint8_t> low_flags;
  std::vector<std::uint16_t> low_epoch_index;
  Value final_value = 0U;
  Value final_mex = 0U;
  Value maximum_value = 0U;
  std::size_t seen_bytes = 0U;
};

struct CoverageCounts {
  Count low = 0U;
  Count history_rail = 0U;
  Count any_rail = 0U;
  Count comb_step = 0U;
  Count terminal_gate = 0U;
  Count history_orphan = 0U;
  Count any_orphan = 0U;
  Count rail_overlap = 0U;
  Count step_overlap = 0U;
  Count initial = 0U;
  Count sub_fresh = 0U;
  Count add_fresh = 0U;
  Count add_repeat = 0U;
  Count above_target = 0U;
  Count above_sub_orphan = 0U;
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

bool LowCandidate(Value value, Clock next_clock, Value target) {
  return Candidate(value, next_clock) < target;
}

std::uint8_t EncodeLow(Arrival arrival, bool above_target) {
  return static_cast<std::uint8_t>(arrival) |
      (above_target ? static_cast<std::uint8_t>(0x08U) : 0U);
}

Arrival DecodeArrival(std::uint8_t flags) {
  return static_cast<Arrival>(flags & 0x07U);
}

bool DecodeAbove(std::uint8_t flags) {
  return (flags & 0x08U) != 0U;
}

RunData Generate(Clock horizon) {
  RunData result;
  result.low_flags.resize(horizon, 0U);
  result.low_epoch_index.resize(horizon, 0U);
  DenseSeen seen;
  seen.Insert(0U);
  Value value = 0U, mex = 1U, maximum_value = 0U;
  Clock epoch_start = 0U;
  std::uint16_t epoch_index = 0U;
  Arrival arrival = Arrival::initial;
  ActiveComb active;
  bool comb_active = false;

  auto finish_comb = [&](Clock clock, EpisodeKind kind, Value blocker) {
    result.episodes.push_back(Episode{
        active.target, active.epoch_start, active.epoch_index,
        active.start, clock,
        active.entry, blocker, active.rails, kind});
    comb_active = false;
  };

  for (std::uint64_t raw = 1U; raw <= horizon; ++raw) {
    const Clock clock = static_cast<Clock>(raw);
    const Clock state_time = static_cast<Clock>(clock - 1U);
    if (LowCandidate(value, clock, mex)) {
      result.low_flags[state_time] = EncodeLow(arrival, value > mex);
      result.low_epoch_index[state_time] =
          static_cast<std::uint16_t>(epoch_index + 1U);
      if (arrival == Arrival::addition_repeat) {
        result.nonfresh_lows.push_back(
            NonfreshLow{mex, value, epoch_start, state_time});
      }
    }

    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool subtraction = positive && !seen.Contains(candidate);
    const Value old_value = value;
    const Value old_mex = mex;
    const Value next_value = subtraction ? candidate : value + clock;
    const bool next_fresh = !seen.Contains(next_value);

    if (comb_active) {
      if (active.phase == ActiveComb::Phase::expect_add) {
        if (subtraction) throw std::runtime_error("comb expected addition");
        active.phase = ActiveComb::Phase::expect_resolution;
      } else if (subtraction) {
        if (next_value + 1U != active.landing)
          throw std::runtime_error("nonconsecutive comb landing");
        active.landing = next_value;
        active.rails = static_cast<Clock>(active.rails + 1U);
        active.phase = ActiveComb::Phase::expect_add;
      } else {
        finish_comb(clock, EpisodeKind::history_terminal,
                    active.landing - 1U);
      }
    }

    value = next_value;
    maximum_value = std::max(maximum_value, value);
    seen.Insert(value);
    while (seen.Contains(mex)) ++mex;

    if (comb_active && mex != old_mex)
      finish_comb(clock, EpisodeKind::target_terminal, old_mex);

    if (mex != old_mex) {
      result.epochs.push_back(Epoch{
          old_mex, epoch_start, static_cast<Clock>(clock - 1U)});
      epoch_start = clock;
      if (epoch_index == std::numeric_limits<std::uint16_t>::max() - 1U)
        throw std::runtime_error("too many mex epochs for coverage index");
      epoch_index = static_cast<std::uint16_t>(epoch_index + 1U);
    }

    arrival = subtraction
        ? Arrival::subtraction_fresh
        : (next_fresh ? Arrival::addition_fresh : Arrival::addition_repeat);

    if (!comb_active && subtraction && mex == old_mex && value > mex &&
        LowCandidate(value, static_cast<Clock>(clock + 1U), mex)) {
      active = ActiveComb{mex, epoch_start, epoch_index,
                          clock, value, value, 1U,
                          ActiveComb::Phase::expect_add};
      comb_active = true;
    }
    (void)old_value;
  }

  if (comb_active) {
    finish_comb(horizon, EpisodeKind::horizon_censored,
                active.landing == 0U ? 0U : active.landing - 1U);
  }
  result.epochs.push_back(Epoch{
      mex, epoch_start, static_cast<Clock>(horizon - 1U)});
  result.final_value = value;
  result.final_mex = mex;
  result.maximum_value = maximum_value;
  result.seen_bytes = seen.Bytes();
  return result;
}

std::unordered_map<Value, OriginInfo> CollectOrigins(
    Clock horizon, const std::vector<NonfreshLow>& events) {
  std::unordered_set<Value> requested;
  requested.reserve(events.size() * 2U + 1U);
  for (const NonfreshLow& event : events) requested.insert(event.value);
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
    throw std::runtime_error("not all nonfresh origins were recovered");
  return origins;
}

Clock Percentile(std::vector<Clock> values, std::size_t percentile) {
  if (values.empty()) return 0U;
  std::sort(values.begin(), values.end());
  const std::size_t index = std::min(
      values.size() - 1U, values.size() * percentile / 100U);
  return values[index];
}

const char* KindName(EpisodeKind kind) {
  switch (kind) {
    case EpisodeKind::history_terminal: return "history";
    case EpisodeKind::target_terminal: return "target";
    case EpisodeKind::horizon_censored: return "censor";
  }
  return "unknown";
}

void PrintCoverage(Clock horizon, const RunData& data) {
  std::vector<std::uint8_t> rail_coverage(horizon, 0U);
  std::vector<std::uint8_t> history_coverage(horizon, 0U);
  std::vector<std::uint8_t> step_coverage(horizon, 0U);
  std::vector<Clock> history_lengths;
  Count invalid_rails = 0U, out_of_range_rails = 0U;
  Count history_rail_mass = 0U, history_step_mass = 0U;
  Count suffix_episode_count = 0U, suffix_triangular_mass = 0U;
  Clock max_suffix_multiplicity = 0U;

  for (const Episode& episode : data.episodes) {
    if (episode.kind == EpisodeKind::history_terminal) {
      history_lengths.push_back(episode.rails);
      history_rail_mass += episode.rails;
      history_step_mass += episode.rails - 1U;
      suffix_episode_count += episode.rails;
      suffix_triangular_mass +=
          static_cast<Count>(episode.rails) * (episode.rails + 1U) / 2U;
      max_suffix_multiplicity =
          std::max(max_suffix_multiplicity, episode.rails);
    }
    for (Clock index = 0U; index < episode.rails; ++index) {
      const std::uint64_t raw_time =
          static_cast<std::uint64_t>(episode.start) + 2ULL * index;
      if (raw_time >= horizon) {
        ++out_of_range_rails;
        continue;
      }
      const Clock time = static_cast<Clock>(raw_time);
      if (data.low_flags[time] == 0U ||
          data.low_epoch_index[time] != episode.epoch_index + 1U) {
        ++invalid_rails;
        continue;
      }
      ++rail_coverage[time];
      if (episode.kind == EpisodeKind::history_terminal)
        ++history_coverage[time];
      if (index + 1U < episode.rails) ++step_coverage[time];
    }
  }

  std::cout << "maximal comb coverage by epoch:\n";
  CoverageCounts global;
  for (const Epoch& epoch : data.epochs) {
    CoverageCounts local;
    if (epoch.finish < epoch.start) continue;
    for (std::uint64_t raw = epoch.start; raw <= epoch.finish; ++raw) {
      const Clock time = static_cast<Clock>(raw);
      const std::uint8_t flags = data.low_flags[time];
      if (flags == 0U) continue;
      ++local.low;
      ++global.low;
      const Arrival arrival = DecodeArrival(flags);
      for (CoverageCounts* counts : {&local, &global}) {
        if (history_coverage[time] != 0U) ++counts->history_rail;
        if (rail_coverage[time] != 0U) ++counts->any_rail;
        if (step_coverage[time] != 0U) ++counts->comb_step;
        if (history_coverage[time] != 0U &&
            step_coverage[time] == 0U) ++counts->terminal_gate;
        if (history_coverage[time] == 0U) ++counts->history_orphan;
        if (rail_coverage[time] == 0U) ++counts->any_orphan;
        if (rail_coverage[time] > 1U) ++counts->rail_overlap;
        if (step_coverage[time] > 1U) ++counts->step_overlap;
        if (DecodeAbove(flags)) ++counts->above_target;
        if (rail_coverage[time] == 0U && DecodeAbove(flags) &&
            arrival == Arrival::subtraction_fresh)
          ++counts->above_sub_orphan;
        switch (arrival) {
          case Arrival::initial: ++counts->initial; break;
          case Arrival::subtraction_fresh: ++counts->sub_fresh; break;
          case Arrival::addition_fresh: ++counts->add_fresh; break;
          case Arrival::addition_repeat: ++counts->add_repeat; break;
          case Arrival::none: break;
        }
      }
    }
    std::cout << "  target=" << epoch.target << " states="
              << (static_cast<Count>(epoch.finish) - epoch.start + 1U)
              << " low=" << local.low << " railCovered(history/any)="
              << local.history_rail << '/' << local.any_rail
              << " combStep=" << local.comb_step
              << " terminalGate=" << local.terminal_gate
              << " orphan(history/any)=" << local.history_orphan << '/'
              << local.any_orphan << " arrival(init/sub/addFresh/addRepeat)="
              << local.initial << '/' << local.sub_fresh << '/'
              << local.add_fresh << '/' << local.add_repeat
              << " aboveSubOrphan=" << local.above_sub_orphan << '\n';
  }

  std::cout << "maximal comb coverage global:\n"
            << "  low=" << global.low << " railCovered(history/any)="
            << global.history_rail << '/' << global.any_rail
            << " combStep=" << global.comb_step
            << " terminalGate=" << global.terminal_gate
            << " orphan(history/any)=" << global.history_orphan << '/'
            << global.any_orphan << " overlap(rail/step)="
            << global.rail_overlap << '/' << global.step_overlap << '\n'
            << "  arrival(init/sub/addFresh/addRepeat)=" << global.initial
            << '/' << global.sub_fresh << '/' << global.add_fresh << '/'
            << global.add_repeat << " aboveTarget=" << global.above_target
            << " aboveSubOrphan=" << global.above_sub_orphan << '\n'
            << "  invalidRails=" << invalid_rails
            << " outOfRangeRails=" << out_of_range_rails << '\n'
            << "history episode lengths:\n"
            << "  episodes=" << history_lengths.size()
            << " railsTotal=" << history_rail_mass
            << " combStepsTotal=" << history_step_mass
            << " rails(p50/p90/p99/max)="
            << Percentile(history_lengths, 50U) << '/'
            << Percentile(history_lengths, 90U) << '/'
            << Percentile(history_lengths, 99U) << '/'
            << (history_lengths.empty()
                    ? 0U
                    : *std::max_element(history_lengths.begin(),
                                        history_lengths.end()))
            << '\n'
            << "all-suffix overlap model:\n"
            << "  suffixEpisodes=" << suffix_episode_count
            << " unionRails=" << history_rail_mass
            << " triangularCoverageMass=" << suffix_triangular_mass
            << " duplicateMass="
            << suffix_triangular_mass - history_rail_mass
            << " maxMultiplicity=" << max_suffix_multiplicity << '\n';
}

void PrintNonfreshOrigins(
    const RunData& data,
    const std::unordered_map<Value, OriginInfo>& origins) {
  Count orphan = 0U, first_pre_epoch = 0U;
  Count first_add = 0U, first_sub = 0U;
  Count first_candidate_low = 0U, first_candidate_equal = 0U;
  Count first_candidate_high = 0U, parent_above_target = 0U;
  std::vector<Clock> lags;
  Clock max_lag = 0U;
  NonfreshLow witness;
  OriginInfo witness_origin;
  for (const NonfreshLow& event : data.nonfresh_lows) {
    const OriginInfo origin = origins.at(event.value);
    ++orphan;
    if (origin.first <= event.epoch_start) ++first_pre_epoch;
    if (origin.subtraction) {
      ++first_sub;
    } else {
      ++first_add;
    }
    const Value first_candidate =
        Candidate(event.value, static_cast<Clock>(origin.first + 1U));
    if (first_candidate < event.target) {
      ++first_candidate_low;
    } else if (event.target < first_candidate) {
      ++first_candidate_high;
    } else {
      ++first_candidate_equal;
    }
    if (event.target < origin.parent) ++parent_above_target;
    const Clock lag = static_cast<Clock>(event.time - origin.first);
    lags.push_back(lag);
    if (lag > max_lag) {
      max_lag = lag;
      witness = event;
      witness_origin = origin;
    }
  }
  std::cout << "nonfresh low-entry backward origins:\n"
            << "  events=" << orphan << " firstPreEpoch="
            << first_pre_epoch << " firstOrigin(add/sub)=" << first_add
            << '/' << first_sub << " firstCandidate(low/equal/high)="
            << first_candidate_low << '/' << first_candidate_equal << '/'
            << first_candidate_high << " firstParentAboveTarget="
            << parent_above_target << '\n'
            << "  lag(p50/p90/p99/max)=" << Percentile(lags, 50U) << '/'
            << Percentile(lags, 90U) << '/' << Percentile(lags, 99U) << '/'
            << max_lag << '\n';
  if (!lags.empty()) {
    std::cout << "  max-lag witness target=" << witness.target
              << " epochStart=" << witness.epoch_start
              << " lowTime=" << witness.time << " entry=" << witness.value
              << " firstTime=" << witness_origin.first
              << " firstOrigin="
              << (witness_origin.subtraction ? "sub" : "add")
              << " firstParent=" << witness_origin.parent
              << " mexAtFirst=" << witness_origin.mex_at_first << '\n';
  }
  if (data.nonfresh_lows.size() <= 32U) {
    for (const NonfreshLow& event : data.nonfresh_lows) {
      const OriginInfo origin = origins.at(event.value);
      std::cout << "  event target=" << event.target
                << " epochStart=" << event.epoch_start
                << " lowTime=" << event.time << " entry=" << event.value
                << " firstTime=" << origin.first << " firstOrigin="
                << (origin.subtraction ? "sub" : "add")
                << " firstParent=" << origin.parent
                << " mexAtFirst=" << origin.mex_at_first << '\n';
    }
  }
}

void PrintEpisodes(const RunData& data) {
  Count history = 0U, target = 0U, censor = 0U;
  for (const Episode& episode : data.episodes) {
    switch (episode.kind) {
      case EpisodeKind::history_terminal: ++history; break;
      case EpisodeKind::target_terminal: ++target; break;
      case EpisodeKind::horizon_censored: ++censor; break;
    }
  }
  std::cout << "episodes(history/target/censor)=" << history << '/'
            << target << '/' << censor << '\n';
  for (const Episode& episode : data.episodes) {
    if (episode.kind != EpisodeKind::history_terminal) {
      std::cout << "  exceptional kind=" << KindName(episode.kind)
                << " target=" << episode.target << " start="
                << episode.start << " end=" << episode.end
                << " entry=" << episode.entry << " rails="
                << episode.rails << '\n';
    }
  }
}

void Analyze(Clock horizon) {
  const RunData data = Generate(horizon);
  std::cout << "target-comb-extraction horizon=" << horizon
            << " finalValue=" << data.final_value
            << " mex=" << data.final_mex
            << " epochs=" << data.epochs.size()
            << " episodes=" << data.episodes.size()
            << " maxValue=" << data.maximum_value
            << " seenMiB=" << data.seen_bytes / (1024U * 1024U) << '\n';
  PrintEpisodes(data);
  PrintCoverage(horizon, data);
  const std::unordered_map<Value, OriginInfo> origins =
      CollectOrigins(horizon, data.nonfresh_lows);
  PrintNonfreshOrigins(data, origins);
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
