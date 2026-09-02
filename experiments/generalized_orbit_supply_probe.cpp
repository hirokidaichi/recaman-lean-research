// Exact falsifier for H-20260902-04: same-candidate supply chains in
// generalized Recaman orbits.
//
// A generalized orbit starts from a single initial value v0 with history
// {v0} and follows the exact greedy rule of Basic.step: at clock n the
// candidate a - n is taken when a > n and the candidate is unvisited,
// otherwise a + n is taken.  Such a history never preloads blockers: it has
// exactly n + 1 values at clock n, which is the canonical cardinality
// invariant.  The probe reuses the counted-use semantics of
// fixed_seed_supply_falsifier's canonical scan:
//
//   a low entry is a legal subtraction into candidate c with 0 < c <= m;
//   a burst use also has three additions at m+1, m+2, m+3;
//   an internal demand use also has c + m first born at a clock in [1, m+1];
//   a strict-high link joins two internal demand uses of the same c with
//   every intermediate candidate strictly above its clock;
//   in c-floor mode (fourth argument 1) the link instead requires every
//   intermediate candidate to be at least c, which is the corridor's
//   least-recurring-candidate condition.
//
// For every start in [lo, hi] the probe reports the maximal same-candidate
// chain of strict-high links and a census of chain lengths.

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <map>
#include <stdexcept>
#include <unordered_map>
#include <vector>

namespace {

using Nat = std::uint64_t;
using Clock = std::uint32_t;

constexpr Clock kNoClock = std::numeric_limits<Clock>::max();
constexpr Nat kValueCap = 400000000ULL;

class DenseHistory {
 public:
  bool Contains(Nat value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < seen_.size() &&
           ((seen_[word] >> (value & 63U)) & 1ULL) != 0U;
  }

  Clock First(Nat value) const {
    const std::size_t index = static_cast<std::size_t>(value);
    return index < first_.size() ? first_[index] : kNoClock;
  }

  void Record(Nat value, Clock clock) {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    if (word >= seen_.size()) seen_.resize(word + 1U, 0U);
    const std::uint64_t mask = 1ULL << (value & 63U);
    if ((seen_[word] & mask) != 0U) return;
    seen_[word] |= mask;
    const std::size_t index = static_cast<std::size_t>(value);
    if (index >= first_.size()) first_.resize(index + 1U, kNoClock);
    first_[index] = clock;
  }

 private:
  std::vector<std::uint64_t> seen_;
  std::vector<Clock> first_;
};

struct OrbitResult {
  bool overflow = false;
  Nat low_entries = 0U;
  Nat burst_entries = 0U;
  Nat internal_demands = 0U;
  Nat valid_links = 0U;
  Nat max_chain = 0U;
  Nat best_candidate = 0U;
  std::vector<Clock> best_uses;
};

Nat ParseNat(const char* text, Nat lower, Nat upper, const char* name) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed < lower || parsed > upper)
    throw std::invalid_argument(std::string(name) + " out of range");
  return static_cast<Nat>(parsed);
}

OrbitResult ScanOrbit(Nat start, Clock horizon, bool floor_mode) {
  const Clock simulation_end = horizon + 3U;
  DenseHistory history;
  history.Record(start, 0U);
  std::vector<Nat> candidates(static_cast<std::size_t>(simulation_end) + 1U,
                              0U);
  std::vector<unsigned char> signs(
      static_cast<std::size_t>(simulation_end) + 1U, 0U);
  Nat value = start;
  OrbitResult result;
  for (Clock clock = 1U; clock <= simulation_end; ++clock) {
    const Clock time = clock - 1U;
    const Nat candidate = value > clock ? value - clock : 0U;
    candidates[time] = candidate;
    const bool subtract = value > clock && !history.Contains(candidate);
    signs[clock] = subtract ? static_cast<unsigned char>('S')
                            : static_cast<unsigned char>('A');
    value = subtract ? candidate : value + clock;
    if (value > kValueCap) {
      result.overflow = true;
      return result;
    }
    history.Record(value, clock);
  }

  struct ChainState {
    Clock previous = 0U;
    Nat chain = 0U;
    bool has_previous = false;
    std::vector<Clock> uses;
  };
  std::unordered_map<Nat, ChainState> chains;
  Clock last_bad = 0U;
  // Floor mode: a link requires every intermediate candidate to be >= c, the
  // corridor's least-recurring-candidate condition.  It is checked directly
  // over the interval instead of through last_bad.
  const auto floor_link = [&candidates](Clock previous, Clock m, Nat c) {
    for (Clock t = previous + 1U; t < m; ++t)
      if (candidates[t] < c) return false;
    return true;
  };
  for (Clock m = 1U; m <= horizon; ++m) {
    const Nat c = candidates[m];
    const bool low_entry = 0U < c && c <= m &&
                           signs[m] == static_cast<unsigned char>('S');
    if (low_entry) {
      ++result.low_entries;
      const bool burst = signs[m + 1U] == static_cast<unsigned char>('A') &&
                         signs[m + 2U] == static_cast<unsigned char>('A') &&
                         signs[m + 3U] == static_cast<unsigned char>('A');
      if (burst) {
        ++result.burst_entries;
        const Clock birth = history.First(c + m);
        if (birth != kNoClock && 0U < birth && birth <= m + 1U) {
          ++result.internal_demands;
          ChainState& state = chains[c];
          const bool linked =
              state.has_previous &&
              (floor_mode ? floor_link(state.previous, m, c)
                          : last_bad <= state.previous);
          if (linked) {
            ++result.valid_links;
            ++state.chain;
            state.uses.push_back(m);
          } else {
            state.chain = 1U;
            state.uses.assign(1U, m);
          }
          state.previous = m;
          state.has_previous = true;
          if (state.chain > result.max_chain) {
            result.max_chain = state.chain;
            result.best_candidate = c;
            result.best_uses = state.uses;
          }
        }
      }
    }
    if (candidates[m] <= m) last_bad = m;
  }
  return result;
}

void Run(Nat lo, Nat hi, Clock horizon, bool floor_mode) {
  std::map<Nat, Nat> chain_census;
  Nat overflow = 0U, total_links = 0U, total_demands = 0U;
  OrbitResult best;
  Nat best_start = 0U;
  std::vector<std::pair<Nat, OrbitResult>> long_chains;
  for (Nat start = lo; start <= hi; ++start) {
    OrbitResult result = ScanOrbit(start, horizon, floor_mode);
    if (result.overflow) {
      ++overflow;
      continue;
    }
    ++chain_census[result.max_chain];
    total_links += result.valid_links;
    total_demands += result.internal_demands;
    if (result.max_chain >= 3U) long_chains.emplace_back(start, result);
    if (result.max_chain > best.max_chain ||
        (result.max_chain == best.max_chain &&
         result.valid_links > best.valid_links)) {
      best = result;
      best_start = start;
    }
  }
  std::cout << "generalized-orbit-supply mode="
            << (floor_mode ? "c-floor" : "strict-high") << " starts=[" << lo
            << ',' << hi << "] horizon=" << horizon << " overflow=" << overflow
            << " internalDemandUses=" << total_demands
            << " strictHighLinks=" << total_links << '\n';
  std::cout << "maxChain census:";
  for (const auto& [chain, count] : chain_census)
    std::cout << ' ' << chain << ':' << count;
  std::cout << '\n';
  std::cout << "best start=" << best_start << " maxChain=" << best.max_chain
            << " links=" << best.valid_links << " c=" << best.best_candidate
            << " uses=";
  for (std::size_t index = 0U; index < best.best_uses.size(); ++index) {
    if (index != 0U) std::cout << ',';
    std::cout << best.best_uses[index];
  }
  std::cout << '\n';
  std::cout << "H-G3=" << (long_chains.empty() ? "not-refuted" : "REFUTED")
            << " startsWithChain3=" << long_chains.size();
  const std::size_t limit = std::min<std::size_t>(long_chains.size(), 8U);
  for (std::size_t index = 0U; index < limit; ++index) {
    const auto& [start, result] = long_chains[index];
    std::cout << " (start=" << start << ",c=" << result.best_candidate
              << ",uses=";
    for (std::size_t k = 0U; k < result.best_uses.size(); ++k) {
      if (k != 0U) std::cout << '/';
      std::cout << result.best_uses[k];
    }
    std::cout << ')';
  }
  std::cout << '\n';
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Nat lo = argc >= 2 ? ParseNat(argv[1], 0U, 100000000ULL, "lo") : 0U;
    const Nat hi =
        argc >= 3 ? ParseNat(argv[2], lo, 100000000ULL, "hi") : 1000U;
    const Clock horizon = static_cast<Clock>(
        argc >= 4 ? ParseNat(argv[3], 16U, 2000000000ULL, "horizon")
                  : 100000U);
    const bool floor_mode =
        argc >= 5 && ParseNat(argv[4], 0U, 1U, "floor_mode") == 1U;
    Run(lo, hi, horizon, floor_mode);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
