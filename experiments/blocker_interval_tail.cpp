// This probe deliberately reuses the exact orbit/job generator and Hall tree
// from blocker_interval_hall.cpp in one translation unit.  Renaming its main
// keeps this file independent while avoiding a second copy of the recurrence.
#define main blocker_interval_hall_embedded_main
#include "blocker_interval_hall.cpp"
#undef main

#include <optional>
#include <tuple>

namespace {

struct Restriction {
  Clock minimum_left;
  Clock minimum_right;
  std::optional<std::pair<Clock, Clock>> excluded_interval;
};

struct RestrictedResult {
  Mass constant;
  HallWitness witness;
  IntervalStats stats;
};

constexpr Mass kPointMask = 1000000000000000LL;

HallWitness EvaluateRestricted(const OrbitData& orbit, const std::vector<Job>& jobs,
                               Mass constant, const Restriction& restriction) {
  std::vector<Job> eligible;
  eligible.reserve(jobs.size());
  std::vector<Clock> releases;
  releases.reserve(jobs.size());
  for (const Job& job : jobs) {
    if (job.release >= restriction.minimum_left) {
      eligible.push_back(job);
      releases.push_back(job.release);
    }
  }
  if (eligible.empty()) {
    return HallWitness{0, 0U, 0U};
  }
  std::sort(releases.begin(), releases.end());
  releases.erase(std::unique(releases.begin(), releases.end()), releases.end());

  std::vector<Mass> initial;
  initial.reserve(releases.size());
  for (const Clock release : releases) {
    initial.push_back(CapacityPrefix(orbit, release - 1U, constant));
  }
  PrefixAddMaxTree tree(initial);
  HallWitness worst{std::numeric_limits<Mass>::min(), 0U, 0U};

  auto query_at = [&](Clock right, HallWitness current) {
    if (right < restriction.minimum_right) {
      return current;
    }
    const auto right_position = std::upper_bound(releases.begin(), releases.end(), right);
    if (right_position == releases.begin()) {
      return current;
    }
    const std::size_t right_index =
        static_cast<std::size_t>(right_position - releases.begin() - 1);

    std::optional<std::size_t> masked_index;
    if (restriction.excluded_interval.has_value() &&
        restriction.excluded_interval->second == right) {
      const Clock excluded_left = restriction.excluded_interval->first;
      const auto position = std::lower_bound(releases.begin(), releases.end(), excluded_left);
      if (position != releases.end() && *position == excluded_left) {
        const std::size_t index = static_cast<std::size_t>(position - releases.begin());
        if (index <= right_index) {
          tree.AddPrefix(index, -kPointMask);
          if (index > 0U) {
            tree.AddPrefix(index - 1U, kPointMask);
          }
          masked_index = index;
        }
      }
    }

    const MaxPoint maximum = tree.QueryPrefix(right_index);
    if (masked_index.has_value()) {
      const std::size_t index = *masked_index;
      tree.AddPrefix(index, kPointMask);
      if (index > 0U) {
        tree.AddPrefix(index - 1U, -kPointMask);
      }
    }
    const Mass deficit = maximum.value - CapacityPrefix(orbit, right, constant);
    const Clock left = releases[maximum.index];
    if (deficit > current.max_deficit ||
        (deficit == current.max_deficit &&
         std::pair<Clock, Clock>{left, right} <
             std::pair<Clock, Clock>{current.left, current.right})) {
      return HallWitness{deficit, left, right};
    }
    return current;
  };

  std::size_t job_index = 0U;
  while (job_index < eligible.size() &&
         eligible[job_index].deadline <= restriction.minimum_right) {
    const Job& job = eligible[job_index];
    const auto release_position =
        std::upper_bound(releases.begin(), releases.end(), job.release);
    const std::size_t release_index =
        static_cast<std::size_t>(release_position - releases.begin() - 1);
    tree.AddPrefix(release_index, job.demand);
    ++job_index;
  }
  if (restriction.minimum_right > 0U) {
    worst = query_at(restriction.minimum_right, worst);
  }

  while (job_index < eligible.size()) {
    const Clock deadline = eligible[job_index].deadline;
    do {
      const Job& job = eligible[job_index];
      const auto release_position =
          std::upper_bound(releases.begin(), releases.end(), job.release);
      const std::size_t release_index =
          static_cast<std::size_t>(release_position - releases.begin() - 1);
      tree.AddPrefix(release_index, job.demand);
      ++job_index;
    } while (job_index < eligible.size() && eligible[job_index].deadline == deadline);
    worst = query_at(deadline, worst);
  }
  if (worst.max_deficit == std::numeric_limits<Mass>::min()) {
    return HallWitness{0, 0U, 0U};
  }
  return worst;
}

IntervalStats RestrictedStats(const OrbitData& orbit, const std::vector<Job>& jobs,
                              const HallWitness& witness, Mass constant) {
  if (witness.left == 0U) {
    return IntervalStats{0, 0, 0, 0, 0, 0};
  }
  Mass demand = 0;
  for (const Job& job : jobs) {
    if (job.release >= witness.left && job.deadline <= witness.right) {
      demand += job.demand;
    }
  }
  const Clock before = witness.left - 1U;
  const Mass sub_mass = orbit.sub_sum[witness.right] - orbit.sub_sum[before];
  const Mass sub_count = orbit.sub_count[witness.right] - orbit.sub_count[before];
  const Mass base_deficit = demand - sub_mass;
  const Mass previous = constant == 0 ? 0 : constant - 1;
  return IntervalStats{demand,
                       sub_mass,
                       sub_count,
                       base_deficit,
                       base_deficit - previous * sub_count,
                       constant * sub_count - base_deficit};
}

RestrictedResult AnalyzeRestricted(const OrbitData& orbit, const std::vector<Job>& jobs,
                                   const Restriction& restriction) {
  Mass lower = 0;
  Mass upper = 1;
  while (EvaluateRestricted(orbit, jobs, upper, restriction).max_deficit > 0) {
    upper *= 2;
  }
  while (lower < upper) {
    const Mass middle = lower + (upper - lower) / 2;
    if (EvaluateRestricted(orbit, jobs, middle, restriction).max_deficit <= 0) {
      upper = middle;
    } else {
      lower = middle + 1;
    }
  }
  const Mass constant = lower;
  const Mass witness_constant = constant == 0 ? 0 : constant - 1;
  HallWitness witness = EvaluateRestricted(orbit, jobs, witness_constant, restriction);
  Clock canonical_left = std::numeric_limits<Clock>::max();
  for (const Job& job : jobs) {
    if (job.release >= witness.left && job.deadline <= witness.right) {
      canonical_left = std::min(canonical_left, job.release);
    }
  }
  if (canonical_left != std::numeric_limits<Clock>::max()) {
    witness.left = canonical_left;
  }
  return RestrictedResult{constant, witness,
                          RestrictedStats(orbit, jobs, witness, constant)};
}

void PrintRestricted(const std::string& label, const RestrictedResult& result) {
  std::cout << "  " << label << " C*=" << result.constant;
  if (result.witness.left == 0U) {
    std::cout << " no-jobs\n";
    return;
  }
  std::cout << " witness=[" << result.witness.left << ',' << result.witness.right
            << "] demand=" << result.stats.demand
            << " subMass=" << result.stats.sub_mass
            << " subCount=" << result.stats.sub_count
            << " baseDeficit=" << result.stats.base_deficit
            << " residual@C*-1=" << result.stats.residual_at_previous
            << " slack@C*=" << result.stats.slack_at_constant << '\n';
}

void TailSelfTest() {
  const OrbitData orbit = GenerateOrbit(9U);
  const std::vector<Job> jobs = JobsThrough(orbit.jobs, 7U);
  const Restriction except_initial{1U, 0U, std::pair<Clock, Clock>{2U, 6U}};
  const HallWitness at_eight = EvaluateRestricted(orbit, jobs, 8, except_initial);
  if (at_eight.max_deficit > 0) {
    throw std::runtime_error("tail self-test failed after excluding [2,6]");
  }
  const Restriction right_at_least_seven{1U, 7U, std::nullopt};
  const HallWitness carried =
      EvaluateRestricted(orbit, jobs, 8, right_at_least_seven);
  if (carried.max_deficit != 1 || carried.left != 2U || carried.right != 7U) {
    throw std::runtime_error("tail self-test failed on carried interval [2,7]");
  }
}

Mass BruteMaximumDeficit(const OrbitData& orbit, const std::vector<Job>& jobs,
                         Mass constant, Clock horizon,
                         const Restriction& restriction) {
  Mass worst = 0;
  for (Clock left = restriction.minimum_left; left <= horizon; ++left) {
    for (Clock right = std::max(left, restriction.minimum_right); right <= horizon;
         ++right) {
      if (restriction.excluded_interval.has_value() &&
          *restriction.excluded_interval == std::pair<Clock, Clock>{left, right}) {
        continue;
      }
      Mass demand = 0;
      bool contains_job = false;
      for (const Job& job : jobs) {
        if (job.release >= left && job.deadline <= right) {
          demand += job.demand;
          contains_job = true;
        }
      }
      if (!contains_job) {
        continue;
      }
      const Mass capacity = CapacityPrefix(orbit, right, constant) -
                            CapacityPrefix(orbit, left - 1U, constant);
      worst = std::max(worst, demand - capacity);
    }
  }
  return worst;
}

void BruteForceEquivalenceSelfTest() {
  constexpr Clock kHorizon = 100U;
  const OrbitData orbit = GenerateOrbit(kHorizon);
  const std::vector<Job> jobs = JobsThrough(orbit.jobs, kHorizon);
  const std::vector<Restriction> restrictions = {
      Restriction{1U, 0U, std::nullopt},
      Restriction{7U, 0U, std::nullopt},
      Restriction{1U, 7U, std::nullopt}};
  for (const Restriction& restriction : restrictions) {
    for (Mass constant = 0; constant <= 12; ++constant) {
      const HallWitness fast_witness =
          EvaluateRestricted(orbit, jobs, constant, restriction);
      const Mass fast = fast_witness.max_deficit;
      const Mass brute =
          BruteMaximumDeficit(orbit, jobs, constant, kHorizon, restriction);
      if (fast != brute) {
        throw std::runtime_error(
            "lazy Hall scan disagrees with O(H^2) brute force: C=" +
            std::to_string(constant) + " fast=" + std::to_string(fast) +
            " brute=" + std::to_string(brute) + " minLeft=" +
            std::to_string(restriction.minimum_left) + " minRight=" +
            std::to_string(restriction.minimum_right) + " witness=[" +
            std::to_string(fast_witness.left) + "," +
            std::to_string(fast_witness.right) + "]");
      }
    }
  }
}

// Deliberately not an actual Recamán prefix: several preloaded seen values
// receive the same synthetic last-occurrence label.  The test shows exactly
// why a proof from a static seen-set plus local transitions cannot establish
// the causal Hall bound.
void FreeHistoryCounterexampleSelfTest() {
  constexpr Value kBase = 100U;
  Value value = kBase;
  std::unordered_map<Value, Clock> last = {
      {kBase, 6U}, {kBase - 24U, 5U}, {kBase - 16U, 5U},
      {kBase + 3U, 5U}, {kBase + 13U, 5U}};
  std::vector<Job> jobs;
  Mass sub_mass = 0;
  Mass sub_count = 0;
  for (Clock clock = 7U; clock <= 16U; ++clock) {
    const bool positive = value > clock;
    const Value candidate = positive ? value - clock : 0U;
    const auto position = positive ? last.find(candidate) : last.end();
    const bool seen = positive && position != last.end();
    if (positive && !seen) {
      value = candidate;
      if (clock <= 15U) {
        sub_mass += clock;
        sub_count += 1;
      }
    } else {
      if (seen) {
        jobs.push_back(Job{static_cast<Clock>(position->second + 1U),
                           static_cast<Clock>(clock - 1U), clock,
                           position->second, candidate});
      }
      value += clock;
    }
    last[value] = clock;
  }
  Mass contained_demand = 0;
  for (const Job& job : jobs) {
    if (job.release >= 7U && job.deadline <= 15U) {
      contained_demand += job.demand;
    }
  }
  if (contained_demand != 41 || sub_mass != 28 || sub_count != 3 ||
      contained_demand <= sub_mass + 3 * sub_count) {
    throw std::runtime_error("free-history C=3 counterexample self-test failed");
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    TailSelfTest();
    BruteForceEquivalenceSelfTest();
    FreeHistoryCounterexampleSelfTest();
    std::vector<Clock> horizons;
    if (argc == 1) {
      horizons = {1000U, 10000U, 100000U, 1000000U};
    } else {
      for (int index = 1; index < argc; ++index) {
        horizons.push_back(ParseHorizon(argv[index]));
      }
      std::sort(horizons.begin(), horizons.end());
      horizons.erase(std::unique(horizons.begin(), horizons.end()), horizons.end());
    }

    const Clock maximum_horizon = *std::max_element(horizons.begin(), horizons.end());
    const OrbitData orbit = GenerateOrbit(maximum_horizon);
    const std::vector<Clock> tail_cutoffs = {7U, 100U, 1000U, 10000U, 100000U};
    std::cout << "self-test: excluding canonical [2,6] removes the C=8 failure "
                 "through 7; right>=7 carries it to [2,7]\n";
    std::cout << "self-test: lazy scan equals O(H^2) brute force through H=100 "
                 "for C=0..12 and three restrictions\n";
    std::cout << "note: literal deletion of only [2,6] leaves the equivalent "
                 "zero-capacity extension [1,6]; 'except' below means the next "
                 "canonical release/deadline cut\n";
    std::cout << "free-history counterexample: seeded a(6)=100 gives jobs 11,14,16 "
                 "on [7,15], demand=41, subMass+3*subCount=37\n";
    std::cout << "first-family is diagnostic only: removed later jobs do not reserve "
                 "their annulus capacity\n";

    for (const Clock horizon : horizons) {
      const std::vector<Job> all_jobs = JobsThrough(orbit.jobs, horizon);
      const std::vector<Job> first_jobs = JobsThrough(orbit.first_jobs, horizon);
      std::cout << "horizon=" << horizon << '\n';
      const Restriction except_initial{1U, 0U,
                                       std::pair<Clock, Clock>{2U, 6U}};
      PrintRestricted("all canonical-second",
                      AnalyzeRestricted(orbit, all_jobs, except_initial));
      PrintRestricted("first canonical-second",
                      AnalyzeRestricted(orbit, first_jobs, except_initial));

      const Restriction left_at_least_seven{7U, 0U, std::nullopt};
      PrintRestricted("all left>=7",
                      AnalyzeRestricted(orbit, all_jobs, left_at_least_seven));
      PrintRestricted("first left>=7",
                      AnalyzeRestricted(orbit, first_jobs, left_at_least_seven));

      const Restriction right_at_least_seven{1U, 7U, std::nullopt};
      PrintRestricted("all right>=7",
                      AnalyzeRestricted(orbit, all_jobs, right_at_least_seven));
      PrintRestricted("first right>=7",
                      AnalyzeRestricted(orbit, first_jobs, right_at_least_seven));

      for (const Clock cutoff : tail_cutoffs) {
        if (cutoff > horizon) {
          continue;
        }
        const Restriction tail{cutoff, cutoff, std::nullopt};
        PrintRestricted("all tail p,q>=" + std::to_string(cutoff),
                        AnalyzeRestricted(orbit, all_jobs, tail));
        PrintRestricted("first tail p,q>=" + std::to_string(cutoff),
                        AnalyzeRestricted(orbit, first_jobs, tail));
      }
    }
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
