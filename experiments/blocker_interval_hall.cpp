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

// Exact Hall scan.  For a fixed C and right endpoint q, a job (r,d,w) with
// d <= q contributes w to every candidate left endpoint p <= r.  A lazy
// prefix-add/range-max tree therefore finds max_p(D(p,q)-Cap_C(p,q)) while q
// advances through the deadlines.  Binary search gives the least integral C.
// For J jobs and R distinct releases the cost is O(log(C+2) J log R) time and
// O(R) auxiliary memory per family and horizon; no O(horizon^2) scan occurs.

using Clock = std::uint32_t;
using Value = std::uint64_t;
using Mass = std::int64_t;

struct Job {
  Clock release;
  Clock deadline;
  Clock demand;
  Clock last_occurrence;
  Value blocker;
};

struct OrbitData {
  std::vector<Mass> sub_sum;
  std::vector<Mass> sub_count;
  std::vector<Job> jobs;
  std::vector<Job> first_jobs;
};

struct MaxPoint {
  Mass value;
  std::size_t index;
};

class PrefixAddMaxTree {
 public:
  explicit PrefixAddMaxTree(const std::vector<Mass>& initial)
      : size_(initial.size()), tree_(4U * initial.size()), lazy_(4U * initial.size(), 0) {
    if (initial.empty()) {
      throw std::invalid_argument("segment tree requires at least one point");
    }
    Build(1U, 0U, size_ - 1U, initial);
  }

  void AddPrefix(std::size_t right, Mass delta) {
    AddRange(1U, 0U, size_ - 1U, 0U, right, delta);
  }

  MaxPoint QueryPrefix(std::size_t right) {
    return QueryRange(1U, 0U, size_ - 1U, 0U, right);
  }

 private:
  static constexpr Mass kNegativeInfinity = std::numeric_limits<Mass>::min() / 4;

  std::size_t size_;
  std::vector<MaxPoint> tree_;
  std::vector<Mass> lazy_;

  static MaxPoint Better(const MaxPoint& lhs, const MaxPoint& rhs) {
    if (lhs.value != rhs.value) {
      return lhs.value > rhs.value ? lhs : rhs;
    }
    return lhs.index < rhs.index ? lhs : rhs;
  }

  void Build(std::size_t node, std::size_t left, std::size_t right,
             const std::vector<Mass>& initial) {
    if (left == right) {
      tree_[node] = MaxPoint{initial[left], left};
      return;
    }
    const std::size_t middle = left + (right - left) / 2U;
    Build(2U * node, left, middle, initial);
    Build(2U * node + 1U, middle + 1U, right, initial);
    tree_[node] = Better(tree_[2U * node], tree_[2U * node + 1U]);
  }

  void Apply(std::size_t node, Mass delta) {
    tree_[node].value += delta;
    lazy_[node] += delta;
  }

  void Push(std::size_t node) {
    if (lazy_[node] == 0) {
      return;
    }
    Apply(2U * node, lazy_[node]);
    Apply(2U * node + 1U, lazy_[node]);
    lazy_[node] = 0;
  }

  void AddRange(std::size_t node, std::size_t left, std::size_t right,
                std::size_t query_left, std::size_t query_right, Mass delta) {
    if (query_left <= left && right <= query_right) {
      Apply(node, delta);
      return;
    }
    Push(node);
    const std::size_t middle = left + (right - left) / 2U;
    if (query_left <= middle) {
      AddRange(2U * node, left, middle, query_left, query_right, delta);
    }
    if (middle < query_right) {
      AddRange(2U * node + 1U, middle + 1U, right, query_left, query_right,
               delta);
    }
    tree_[node] = Better(tree_[2U * node], tree_[2U * node + 1U]);
  }

  MaxPoint QueryRange(std::size_t node, std::size_t left, std::size_t right,
                      std::size_t query_left, std::size_t query_right) {
    if (query_left <= left && right <= query_right) {
      return tree_[node];
    }
    Push(node);
    const std::size_t middle = left + (right - left) / 2U;
    MaxPoint result{kNegativeInfinity, 0U};
    if (query_left <= middle) {
      result = Better(result,
                      QueryRange(2U * node, left, middle, query_left, query_right));
    }
    if (middle < query_right) {
      result = Better(result, QueryRange(2U * node + 1U, middle + 1U, right,
                                         query_left, query_right));
    }
    return result;
  }
};

struct HallWitness {
  Mass max_deficit;
  Clock left;
  Clock right;
};

struct IntervalStats {
  Mass demand;
  Mass sub_mass;
  Mass sub_count;
  Mass base_deficit;
  Mass residual_at_previous;
  Mass slack_at_constant;
};

struct FamilyResult {
  Mass constant;
  HallWitness witness;
  IntervalStats stats;
};

Mass CapacityPrefix(const OrbitData& orbit, Clock clock, Mass constant) {
  return orbit.sub_sum[clock] + constant * orbit.sub_count[clock];
}

OrbitData GenerateOrbit(Clock horizon) {
  OrbitData result;
  result.sub_sum.assign(static_cast<std::size_t>(horizon) + 1U, 0);
  result.sub_count.assign(static_cast<std::size_t>(horizon) + 1U, 0);
  result.jobs.reserve(static_cast<std::size_t>(horizon) / 4U);
  result.first_jobs.reserve(static_cast<std::size_t>(horizon) / 5U);

  std::unordered_map<Value, Clock> last_occurrence;
  last_occurrence.reserve(static_cast<std::size_t>(horizon) * 2U / 3U + 1U);
  last_occurrence.emplace(0U, 0U);
  std::unordered_set<Clock> episode_seen;
  episode_seen.reserve(static_cast<std::size_t>(horizon) / 5U + 1U);

  Value value = 0U;
  for (std::uint64_t raw_clock = 1U; raw_clock <= horizon; ++raw_clock) {
    const Clock clock = static_cast<Clock>(raw_clock);
    const bool candidate_positive = value > clock;
    const Value candidate = candidate_positive ? value - clock : 0U;
    const auto blocker_position =
        candidate_positive ? last_occurrence.find(candidate) : last_occurrence.end();
    const bool candidate_seen =
        candidate_positive && blocker_position != last_occurrence.end();
    const bool subtract = candidate_positive && !candidate_seen;

    result.sub_sum[clock] = result.sub_sum[clock - 1U];
    result.sub_count[clock] = result.sub_count[clock - 1U];
    if (subtract) {
      result.sub_sum[clock] += clock;
      result.sub_count[clock] += 1;
      value = candidate;
    } else {
      if (candidate_seen) {
        const Clock last = blocker_position->second;
        const Job job{static_cast<Clock>(last + 1U),
                      static_cast<Clock>(clock - 1U), clock, last, candidate};
        result.jobs.push_back(job);
        if (episode_seen.insert(job.release).second) {
          result.first_jobs.push_back(job);
        }
      }
      value += clock;
    }
    last_occurrence[value] = clock;
  }
  return result;
}

std::vector<Job> JobsThrough(const std::vector<Job>& jobs, Clock horizon) {
  const auto end = std::upper_bound(
      jobs.begin(), jobs.end(), horizon,
      [](Clock bound, const Job& job) { return bound < job.demand; });
  return std::vector<Job>(jobs.begin(), end);
}

HallWitness EvaluateConstant(const OrbitData& orbit, const std::vector<Job>& jobs,
                             Mass constant) {
  if (jobs.empty()) {
    return HallWitness{0, 0U, 0U};
  }

  std::vector<Clock> releases;
  releases.reserve(jobs.size());
  for (const Job& job : jobs) {
    releases.push_back(job.release);
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
  std::size_t job_index = 0U;
  while (job_index < jobs.size()) {
    const Clock deadline = jobs[job_index].deadline;
    do {
      const Job& job = jobs[job_index];
      const auto release_position =
          std::upper_bound(releases.begin(), releases.end(), job.release);
      const std::size_t release_index =
          static_cast<std::size_t>(release_position - releases.begin() - 1);
      tree.AddPrefix(release_index, job.demand);
      ++job_index;
    } while (job_index < jobs.size() && jobs[job_index].deadline == deadline);

    const auto right_position = std::upper_bound(releases.begin(), releases.end(), deadline);
    if (right_position == releases.begin()) {
      continue;
    }
    const std::size_t right_index =
        static_cast<std::size_t>(right_position - releases.begin() - 1);
    const MaxPoint maximum = tree.QueryPrefix(right_index);
    const Mass deficit = maximum.value - CapacityPrefix(orbit, deadline, constant);
    const Clock left = releases[maximum.index];
    if (deficit > worst.max_deficit ||
        (deficit == worst.max_deficit &&
         std::pair<Clock, Clock>{left, deadline} <
             std::pair<Clock, Clock>{worst.left, worst.right})) {
      worst = HallWitness{deficit, left, deadline};
    }
  }
  return worst;
}

IntervalStats ComputeStats(const OrbitData& orbit, const std::vector<Job>& jobs,
                           const HallWitness& witness, Mass constant) {
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

FamilyResult AnalyzeFamily(const OrbitData& orbit, const std::vector<Job>& jobs) {
  if (jobs.empty()) {
    return FamilyResult{0, HallWitness{0, 0U, 0U},
                        IntervalStats{0, 0, 0, 0, 0, 0}};
  }

  Mass lower = 0;
  Mass upper = 1;
  while (EvaluateConstant(orbit, jobs, upper).max_deficit > 0) {
    if (upper > std::numeric_limits<Mass>::max() / 2) {
      throw std::overflow_error("Hall constant search overflow");
    }
    upper *= 2;
  }
  while (lower < upper) {
    const Mass middle = lower + (upper - lower) / 2;
    if (EvaluateConstant(orbit, jobs, middle).max_deficit <= 0) {
      upper = middle;
    } else {
      lower = middle + 1;
    }
  }
  const Mass constant = lower;
  const Mass witness_constant = constant == 0 ? 0 : constant - 1;
  const HallWitness witness = EvaluateConstant(orbit, jobs, witness_constant);
  return FamilyResult{constant, witness,
                      ComputeStats(orbit, jobs, witness, constant)};
}

void PrintFamily(const std::string& name, std::size_t job_count,
                 const FamilyResult& result) {
  std::cout << "  " << name << ": jobs=" << job_count
            << " C*=" << result.constant;
  if (job_count == 0U) {
    std::cout << '\n';
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

void SelfTest() {
  const OrbitData orbit = GenerateOrbit(7U);
  const std::vector<Job> jobs = JobsThrough(orbit.jobs, 7U);
  const HallWitness at_eight = EvaluateConstant(orbit, jobs, 8);
  if (at_eight.max_deficit != 1 || at_eight.left != 2U || at_eight.right != 6U) {
    throw std::runtime_error("self-test failed: expected C=8 failure on [2,6]");
  }
  if (EvaluateConstant(orbit, jobs, 9).max_deficit > 0) {
    throw std::runtime_error("self-test failed: expected C=9 feasibility through clock 7");
  }
  const FamilyResult result = AnalyzeFamily(orbit, jobs);
  if (result.constant != 9 || result.witness.left != 2U ||
      result.witness.right != 6U) {
    throw std::runtime_error("self-test failed: exact Hall constant is not 9");
  }
}

Clock ParseHorizon(const char* text) {
  const std::string input(text);
  std::size_t consumed = 0U;
  const unsigned long parsed = std::stoul(input, &consumed, 10);
  if (consumed != input.size() || parsed == 0UL ||
      parsed > std::numeric_limits<Clock>::max()) {
    throw std::invalid_argument("invalid positive horizon: " + input);
  }
  return static_cast<Clock>(parsed);
}

}  // namespace

int main(int argc, char** argv) {
  try {
    SelfTest();

    std::vector<Clock> horizons;
    if (argc == 1) {
      horizons = {1000U, 10000U, 100000U, 1000000U};
    } else {
      horizons.reserve(static_cast<std::size_t>(argc - 1));
      for (int index = 1; index < argc; ++index) {
        horizons.push_back(ParseHorizon(argv[index]));
      }
      std::sort(horizons.begin(), horizons.end());
      horizons.erase(std::unique(horizons.begin(), horizons.end()), horizons.end());
    }

    const Clock maximum_horizon = *std::max_element(horizons.begin(), horizons.end());
    const OrbitData orbit = GenerateOrbit(maximum_horizon);
    std::cout << "self-test: C=8 fails exactly on [2,6]; C=9 succeeds through 7\n";
    std::cout << "algorithm: exact interval Hall scan by deadline; each job adds its demand "
                 "to all release cutoffs p<=release in a lazy range-max tree\n";
    std::cout << "complexity: O(log(C+2) J log R) time and O(R) auxiliary memory "
                 "per family/horizon (J jobs, R distinct releases)\n";
    std::cout << "note: first-family keeps only the earliest job for each exact "
                 "last-occurrence release; removed annulus jobs do not reserve capacity\n";

    for (const Clock horizon : horizons) {
      const std::vector<Job> jobs = JobsThrough(orbit.jobs, horizon);
      const std::vector<Job> first_jobs = JobsThrough(orbit.first_jobs, horizon);
      std::cout << "horizon=" << horizon << '\n';
      PrintFamily("all", jobs.size(), AnalyzeFamily(orbit, jobs));
      PrintFamily("first", first_jobs.size(), AnalyzeFamily(orbit, first_jobs));
    }
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
