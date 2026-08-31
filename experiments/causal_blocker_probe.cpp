// Exploratory probe for causal strengthening of the tail Hall observation.
//
// This deliberately reuses the audited orbit/job generator.  It tests whether
// the aggregate C=3 capacity can be explained by any of three simpler local
// ownership rules before we invest in a formal statement.
#define main blocker_interval_hall_embedded_main
#include "blocker_interval_hall.cpp"
#undef main

#include <array>
#include <map>
#include <optional>

namespace {

struct OwnershipFailure {
  Mass overload = 0;
  Clock subtraction = 0U;
  Mass load = 0;
  std::size_t jobs = 0U;
};

struct LagWitness {
  Clock lag = 0U;
  Job job{};
  Clock last_subtraction = 0U;
  Mass individual_slack = 0;
};

struct RunWitness {
  Clock length = 0U;
  Clock start = 0U;
  Clock end = 0U;
};

struct SaturationSourceStats {
  Clock uses = 0U;
  Clock fresh_uses = 0U;
  Clock revisit_uses = 0U;
  Clock first_time = 0U;
  Clock last_time = 0U;
};

struct SaturationWitness {
  Clock count = 0U;
  Value source_value = 0U;
  Clock source_time = 0U;
  Clock predecessor_time = 0U;
};

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

bool IsSubtraction(const OrbitData& orbit, Clock clock) {
  return clock > 0U && orbit.sub_count[clock] != orbit.sub_count[clock - 1U];
}

std::optional<Clock> FirstSubtraction(const OrbitData& orbit, const Job& job) {
  for (Clock clock = job.release; clock <= job.deadline; ++clock) {
    if (IsSubtraction(orbit, clock)) {
      return clock;
    }
  }
  return std::nullopt;
}

std::optional<Clock> LastSubtraction(const OrbitData& orbit, const Job& job) {
  for (Clock clock = job.deadline;; --clock) {
    if (IsSubtraction(orbit, clock)) {
      return clock;
    }
    if (clock == job.release) {
      break;
    }
  }
  return std::nullopt;
}

OwnershipFailure MeasureOwnership(
    const std::vector<Job>& jobs,
    const std::vector<std::optional<Clock>>& owners) {
  std::map<Clock, std::pair<Mass, std::size_t>> loads;
  for (std::size_t index = 0U; index < jobs.size(); ++index) {
    if (!owners[index].has_value()) {
      continue;
    }
    auto& [load, count] = loads[*owners[index]];
    load += jobs[index].demand;
    ++count;
  }

  OwnershipFailure worst;
  for (const auto& [clock, load_and_count] : loads) {
    const auto [load, count] = load_and_count;
    const Mass overload = load - (static_cast<Mass>(clock) + 3);
    if (overload > worst.overload) {
      worst = OwnershipFailure{overload, clock, load, count};
    }
  }
  return worst;
}

void Analyze(Clock horizon, Clock cutoff) {
  const OrbitData orbit = GenerateOrbit(horizon);
  const std::vector<Job> all_jobs = JobsThrough(orbit.jobs, horizon);
  std::vector<Job> jobs;
  jobs.reserve(all_jobs.size());
  for (const Job& job : all_jobs) {
    if (job.release >= cutoff) {
      jobs.push_back(job);
    }
  }

  std::vector<std::optional<Clock>> first_owners;
  std::vector<std::optional<Clock>> last_owners;
  first_owners.reserve(jobs.size());
  last_owners.reserve(jobs.size());

  std::size_t no_subtraction = 0U;
  std::size_t local_last = 0U;
  LagWitness worst_lag;
  Mass minimum_individual_slack = std::numeric_limits<Mass>::max();
  for (const Job& job : jobs) {
    const std::optional<Clock> first = FirstSubtraction(orbit, job);
    const std::optional<Clock> last = LastSubtraction(orbit, job);
    first_owners.push_back(first);
    last_owners.push_back(last);
    if (!last.has_value()) {
      ++no_subtraction;
      continue;
    }

    const Mass sub_mass =
        orbit.sub_sum[job.deadline] - orbit.sub_sum[job.release - 1U];
    const Mass slack = sub_mass + 3 - static_cast<Mass>(job.demand);
    minimum_individual_slack = std::min(minimum_individual_slack, slack);
    const Clock lag = static_cast<Clock>(job.demand - *last);
    if (lag <= 3U) {
      ++local_last;
    }
    if (lag > worst_lag.lag) {
      worst_lag = LagWitness{lag, job, *last, slack};
    }
  }

  const OwnershipFailure first_failure =
      MeasureOwnership(jobs, first_owners);
  const OwnershipFailure last_failure =
      MeasureOwnership(jobs, last_owners);

  RunWitness longest_addition_run;
  Clock current_run_start = 0U;
  Clock current_run_length = 0U;
  for (Clock clock = 1U; clock <= horizon; ++clock) {
    if (!IsSubtraction(orbit, clock)) {
      if (current_run_length == 0U) {
        current_run_start = clock;
      }
      ++current_run_length;
      if (current_run_length > longest_addition_run.length) {
        longest_addition_run =
            RunWitness{current_run_length, current_run_start, clock};
      }
    } else {
      current_run_length = 0U;
    }
  }

  std::cout << "horizon=" << horizon << " cutoff=" << cutoff
            << " jobs=" << jobs.size() << '\n';
  std::cout << "  individual: noSub=" << no_subtraction
            << " minSlack=" << minimum_individual_slack
            << " lastSubWithin3=" << local_last << '/' << jobs.size()
            << " worstLag=" << worst_lag.lag
            << " job=(release=" << worst_lag.job.release
            << ",deadline=" << worst_lag.job.deadline
            << ",demand=" << worst_lag.job.demand
            << ",blocker=" << worst_lag.job.blocker << ')'
            << " lastSub=" << worst_lag.last_subtraction
            << " slack=" << worst_lag.individual_slack << '\n';
  std::cout << "  first-sub owner: overload=" << first_failure.overload
            << " at=" << first_failure.subtraction
            << " load=" << first_failure.load
            << " jobs=" << first_failure.jobs << '\n';
  std::cout << "  last-sub owner: overload=" << last_failure.overload
            << " at=" << last_failure.subtraction
            << " load=" << last_failure.load
            << " jobs=" << last_failure.jobs << '\n';
  std::cout << "  longest addition run: length=" << longest_addition_run.length
            << " interval=[" << longest_addition_run.start << ','
            << longest_addition_run.end << "]\n";
}

void AnalyzeAdditionRuns(Clock horizon) {
  DenseSeen seen;
  seen.Insert(0U);
  Value value = 0U;
  Clock current_start = 0U;
  Clock current_length = 0U;
  RunWitness longest;
  std::array<Clock, 8U> completed_run_counts{};
  Clock completed_runs_longer_than_seven = 0U;
  std::vector<std::optional<Value>> current_blockers;
  std::vector<std::optional<Value>> longest_blockers;

  for (std::uint64_t raw_clock = 1U; raw_clock <= horizon; ++raw_clock) {
    const Clock clock = static_cast<Clock>(raw_clock);
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool blocked = positive && seen.Contains(candidate);
    const bool subtract = positive && !blocked;
    if (subtract) {
      if (current_length == 2U) {
        throw std::runtime_error(
            "exactly two additions formed a maximal run");
      }
      if (current_length > 0U) {
        if (current_length <= 7U) {
          ++completed_run_counts[current_length];
        } else {
          ++completed_runs_longer_than_seven;
        }
      }
      value = candidate;
      current_length = 0U;
      current_blockers.clear();
    } else {
      if (current_length == 0U) {
        current_start = clock;
      }
      ++current_length;
      current_blockers.push_back(blocked ? std::optional<Value>(candidate)
                                         : std::nullopt);
      value += clock;
      if (current_length > longest.length) {
        longest = RunWitness{current_length, current_start, clock};
        longest_blockers = current_blockers;
      }
    }
    seen.Insert(value);
  }

  std::cout << "run-only horizon=" << horizon
            << " longest=" << longest.length
            << " interval=[" << longest.start << ',' << longest.end << ']'
            << " seenMiB=" << (seen.Bytes() / (1024U * 1024U)) << '\n';
  std::cout << "  blockers:";
  for (const std::optional<Value> blocker : longest_blockers) {
    if (blocker.has_value()) {
      std::cout << ' ' << *blocker;
    } else {
      std::cout << " nonpositive";
    }
  }
  std::cout << '\n';

  std::unordered_map<Value, std::size_t> target_index;
  std::vector<Value> targets;
  for (const std::optional<Value> blocker : longest_blockers) {
    if (blocker.has_value() && target_index.find(*blocker) == target_index.end()) {
      target_index.emplace(*blocker, targets.size());
      targets.push_back(*blocker);
    }
  }
  std::vector<Clock> first_times(targets.size(), 0U);
  std::vector<char> first_branches(targets.size(), '?');
  DenseSeen replay_seen;
  replay_seen.Insert(0U);
  Value replay_value = 0U;
  std::size_t unresolved = targets.size();
  for (std::uint64_t raw_clock = 1U;
       raw_clock <= longest.start && unresolved > 0U; ++raw_clock) {
    const Clock clock = static_cast<Clock>(raw_clock);
    const bool positive = replay_value > clock;
    const Value candidate = positive ? replay_value - clock : 0U;
    const bool subtract = positive && !replay_seen.Contains(candidate);
    replay_value = subtract ? candidate : replay_value + clock;
    const auto target = target_index.find(replay_value);
    if (target != target_index.end() && first_times[target->second] == 0U) {
      first_times[target->second] = clock;
      first_branches[target->second] = subtract ? '-' : '+';
      --unresolved;
    }
    replay_seen.Insert(replay_value);
  }
  std::cout << "  first installations:";
  for (std::size_t index = 0U; index < targets.size(); ++index) {
    std::cout << ' ' << targets[index] << '@' << first_times[index]
              << first_branches[index];
  }
  std::cout << '\n';
  std::cout << "  completed addition runs:";
  for (Clock length = 1U; length <= 7U; ++length) {
    if (completed_run_counts[length] != 0U) {
      std::cout << " len=" << length << ':' << completed_run_counts[length];
    }
  }
  if (completed_runs_longer_than_seven != 0U) {
    std::cout << " len>7:" << completed_runs_longer_than_seven;
  }
  std::cout << '\n';
}

void AnalyzeSaturationEdges(Clock horizon, bool detailed_predecessor_times) {
  DenseSeen seen;
  seen.Insert(0U);
  std::unordered_map<Value, Clock> last_occurrence;
  if (detailed_predecessor_times) {
    last_occurrence.reserve(
        static_cast<std::size_t>(horizon) * 2U / 3U + 1U);
    last_occurrence.emplace(0U, 0U);
  }
  std::unordered_map<Value, SaturationSourceStats> source_stats;
  source_stats.reserve(std::min<std::size_t>(
      static_cast<std::size_t>(horizon) / 4U + 1U, 2000000U));
  std::unordered_map<Value, Clock> repeated_occurrences;
  if (detailed_predecessor_times) {
    repeated_occurrences.reserve(std::min<std::size_t>(
        static_cast<std::size_t>(horizon) / 20U + 1U, 1000000U));
  }
  std::unordered_map<Clock, Clock> predecessor_load;
  if (detailed_predecessor_times) {
    predecessor_load.reserve(std::min<std::size_t>(
        static_cast<std::size_t>(horizon) / 4U + 1U, 2000000U));
  }

  Value value = 0U;
  bool value_fresh = true;
  Value two_back_value = 0U;
  bool two_back_fresh = true;
  bool previous_addition = false;
  Clock event_count = 0U;
  Clock fresh_source_count = 0U;
  Clock revisit_source_count = 0U;
  Clock low_source_count = 0U;
  Clock high_source_count = 0U;
  Clock diagonal_source_count = 0U;
  Value weighted_event_sum = 0U;
  Clock current_addition_run = 0U;
  std::array<Clock, 8U> depth_counts{};
  std::array<Value, 8U> depth_weights{};
  SaturationWitness most_reused_source;
  SaturationWitness most_reused_predecessor;
  SaturationWitness oldest_predecessor;
  SaturationWitness most_occurrences;

  for (std::uint64_t raw_clock = 1U; raw_clock <= horizon; ++raw_clock) {
    const Clock clock = static_cast<Clock>(raw_clock);
    const Value old_value = value;
    const bool old_value_fresh = value_fresh;
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const bool blocked = positive && seen.Contains(candidate);
    const bool subtract = positive && !blocked;
    const bool addition = !subtract;
    current_addition_run =
        addition ? static_cast<Clock>(current_addition_run + 1U) : 0U;
    const Clock recorded_depth = std::min<Clock>(current_addition_run, 7U);
    for (Clock depth = 2U; depth <= recorded_depth; ++depth) {
      ++depth_counts[depth];
      if (depth_weights[depth] >
          std::numeric_limits<Value>::max() - static_cast<Value>(clock)) {
        throw std::overflow_error("weighted addition-depth sum overflow");
      }
      depth_weights[depth] += clock;
    }

    if (clock >= 2U && previous_addition && addition) {
      const Clock source_time = static_cast<Clock>(clock - 2U);
      const Value source_value = two_back_value;
      ++event_count;
      if (weighted_event_sum >
          std::numeric_limits<Value>::max() - static_cast<Value>(clock)) {
        throw std::overflow_error("weighted saturation sum overflow");
      }
      weighted_event_sum += clock;
      if (two_back_fresh) {
        ++fresh_source_count;
      } else {
        ++revisit_source_count;
        if (source_value < source_time) {
          throw std::runtime_error(
              "revisited value occurred after its value clock bound");
        }
      }
      if (source_value < source_time) {
        ++low_source_count;
      } else if (source_value == source_time) {
        ++diagonal_source_count;
      } else {
        ++high_source_count;
      }

      auto& stats = source_stats[source_value];
      if (stats.uses == 0U) {
        stats.first_time = source_time;
      }
      ++stats.uses;
      stats.last_time = source_time;
      if (two_back_fresh) {
        ++stats.fresh_uses;
      } else {
        ++stats.revisit_uses;
      }
      if (stats.uses > most_reused_source.count) {
        most_reused_source = SaturationWitness{
            stats.uses, source_value, source_time, 0U};
      }

      if (source_value > 1U) {
        if (!seen.Contains(source_value - 1U)) {
          throw std::runtime_error(
              "consecutive additions lack their causal predecessor");
        }
        if (detailed_predecessor_times) {
          const auto predecessor = last_occurrence.find(source_value - 1U);
          if (predecessor == last_occurrence.end() ||
              predecessor->second > source_time) {
            throw std::runtime_error(
                "consecutive additions have invalid predecessor time");
          }
          const Clock predecessor_time = predecessor->second;
          Clock& load = predecessor_load[predecessor_time];
          ++load;
          if (load > most_reused_predecessor.count) {
            most_reused_predecessor = SaturationWitness{
                load, source_value, source_time, predecessor_time};
          }
          const Clock age = static_cast<Clock>(source_time - predecessor_time);
          if (age > oldest_predecessor.count) {
            oldest_predecessor = SaturationWitness{
                age, source_value, source_time, predecessor_time};
          }
        }
      }
    }

    value = subtract ? candidate : value + clock;
    value_fresh = !seen.Contains(value);
    if (detailed_predecessor_times && !value_fresh) {
      Clock& occurrences = repeated_occurrences[value];
      occurrences = occurrences == 0U ? 2U : static_cast<Clock>(occurrences + 1U);
      if (occurrences > most_occurrences.count) {
        most_occurrences =
            SaturationWitness{occurrences, value, clock, 0U};
      }
    }
    seen.Insert(value);
    if (detailed_predecessor_times) {
      last_occurrence[value] = clock;
    }
    two_back_value = old_value;
    two_back_fresh = old_value_fresh;
    previous_addition = addition;
  }

  std::cout << (detailed_predecessor_times ? "saturation" : "saturation-lite")
            << " horizon=" << horizon
            << " events=" << event_count
            << " distinctSources=" << source_stats.size()
            << " fresh=" << fresh_source_count
            << " revisit=" << revisit_source_count << '\n';
  std::cout << "  weightedEventSum=" << weighted_event_sum
            << " averageEventClock="
            << (event_count == 0U ? 0U : weighted_event_sum / event_count)
            << " finalValue=" << value
            << " upperBoundSlack="
            << weighted_event_sum + static_cast<Value>(horizon) - value
            << '\n';
  std::cout << "  addition depths:";
  for (Clock depth = 2U; depth <= 7U; ++depth) {
    if (depth_counts[depth] != 0U) {
      std::cout << " depth>=" << depth << ":count=" << depth_counts[depth]
                << ",weight=" << depth_weights[depth];
    }
  }
  std::cout << '\n';
  std::cout << "  coordinates: low=" << low_source_count
            << " diagonal=" << diagonal_source_count
            << " high=" << high_source_count << '\n';
  std::cout << "  max source reuse=" << most_reused_source.count
            << " value=" << most_reused_source.source_value
            << " latestTime=" << most_reused_source.source_time << '\n';
  if (detailed_predecessor_times) {
    std::cout << "  max total occurrences=" << most_occurrences.count
              << " value=" << most_occurrences.source_value
              << " latestTime=" << most_occurrences.source_time
              << " repeatedValues=" << repeated_occurrences.size() << '\n';
  }
  if (detailed_predecessor_times) {
    std::cout << "  max predecessor-edge reuse="
              << most_reused_predecessor.count
              << " predecessorTime=" << most_reused_predecessor.predecessor_time
              << " sourceValue=" << most_reused_predecessor.source_value
              << " sourceTime=" << most_reused_predecessor.source_time << '\n';
    std::cout << "  oldest predecessor age=" << oldest_predecessor.count
              << " predecessorTime=" << oldest_predecessor.predecessor_time
              << " sourceValue=" << oldest_predecessor.source_value
              << " sourceTime=" << oldest_predecessor.source_time << '\n';
  }
}

Clock ParseProbeHorizon(const char* text) {
  return ParseHorizon(text);
}

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc >= 3 && std::string(argv[1]) == "--run-only") {
      AnalyzeAdditionRuns(ParseProbeHorizon(argv[2]));
      return EXIT_SUCCESS;
    }
    if (argc >= 3 && std::string(argv[1]) == "--saturation") {
      AnalyzeSaturationEdges(ParseProbeHorizon(argv[2]), true);
      return EXIT_SUCCESS;
    }
    if (argc >= 3 && std::string(argv[1]) == "--saturation-lite") {
      AnalyzeSaturationEdges(ParseProbeHorizon(argv[2]), false);
      return EXIT_SUCCESS;
    }
    const Clock horizon = argc >= 2 ? ParseProbeHorizon(argv[1]) : 1000000U;
    const Clock cutoff = argc >= 3 ? ParseProbeHorizon(argv[2]) : 7U;
    if (cutoff > horizon) {
      throw std::invalid_argument("cutoff must not exceed horizon");
    }
    Analyze(horizon, cutoff);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
