// Exact seeded countermodels for the local sqrt(6m) use-gap claim.
//
// For each q >= 3, set
//
//   m   = q^2 + 2q,
//   gap = 2q + 1,
//   n   = m + gap.
//
// Starting from candidate c at time m, the step word A^(q+1) S^q
// returns to candidate c at time n and keeps every intermediate candidate
// strictly above its absolute clock.  A finite seed supplies the addition
// blockers, including the successor demand at n, and the program follows
// the exact greedy rule (positive fresh candidate => subtraction, otherwise
// addition).  It also checks three additions after the second use clock.
//
// Since gap^2 / m tends to 4, this family violates gap^2 >= 6m at
// arbitrarily large clocks.  It does not claim canonical reachability or a
// single finite seed for the whole infinite family; it isolates the missing
// global self-supply assumption in any attempted use-gap theorem.
//
// Usage: use_gap_counterexample [q_first] [q_last]

#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_set>

namespace {

using Nat = std::uint64_t;

struct State {
  Nat value;
  std::unordered_set<Nat> seen;
};

Nat Parse(const char* text) {
  const unsigned long long value = std::stoull(text);
  if (value < 3ULL || value > 10000ULL)
    throw std::invalid_argument("q must lie in 3..10000");
  return static_cast<Nat>(value);
}

bool CanSubtract(Nat clock, const State& state) {
  return clock < state.value &&
         state.seen.find(state.value - clock) == state.seen.end();
}

char StepAt(Nat clock, State& state) {
  const bool subtract = CanSubtract(clock, state);
  state.value = subtract ? state.value - clock : state.value + clock;
  state.seen.insert(state.value);
  return subtract ? 'S' : 'A';
}

Nat Candidate(Nat time, const State& state) {
  const Nat clock = time + 1U;
  return state.value > clock ? state.value - clock : 0U;
}

struct Result {
  Nat q;
  Nat m;
  Nat n;
  Nat gap;
  std::size_t seed_size;
};

Result Check(Nat q) {
  constexpr Nat c = 10U;
  if (q > (std::numeric_limits<Nat>::max() - 1U) / q)
    throw std::overflow_error("q^2 overflow");
  const Nat m = q * q + 2U * q;
  const Nat gap = 2U * q + 1U;
  const Nat n = m + gap;

  // Candidate excesses before the q+1 intended addition steps.
  std::unordered_set<Nat> blockers;
  Nat excess = 0U;
  for (Nat offset = 0U; offset <= q; ++offset) {
    blockers.insert(c + excess);
    excess += m + offset;
  }
  blockers.insert(c + n);  // successor demand at the second use clock
  blockers.insert(0U);

  State state{c + 2U * m + 1U, blockers};
  state.seen.insert(state.value);
  const std::size_t seed_size = state.seen.size();

  if (StepAt(m, state) != 'S')
    throw std::runtime_error("entry step was not a subtraction");
  if (Candidate(m, state) != c)
    throw std::runtime_error("wrong first use candidate");

  for (Nat offset = 0U; offset < gap; ++offset) {
    const Nat time = m + offset;
    const char expected = offset <= q ? 'A' : 'S';
    if (StepAt(time + 1U, state) != expected)
      throw std::runtime_error("greedy step disagrees with A^(q+1)S^q");
    const Nat next_time = time + 1U;
    const Nat candidate = Candidate(next_time, state);
    if (candidate < c)
      throw std::runtime_error("candidate floor violated");
    if (next_time < n && candidate <= next_time)
      throw std::runtime_error("intermediate low candidate found");
  }

  if (Candidate(n, state) != c)
    throw std::runtime_error("wrong second use candidate");
  for (Nat offset = 0U; offset < 3U; ++offset) {
    if (StepAt(n + offset + 1U, state) != 'A')
      throw std::runtime_error("second use did not emit a three-addition burst");
    if (Candidate(n + offset + 1U, state) < c)
      throw std::runtime_error("post-use candidate floor violated");
  }

  if (!(gap * gap < 6U * m))
    throw std::runtime_error("counterexample does not violate gap^2 >= 6m");

  return {q, m, n, gap, seed_size};
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Nat first = argc >= 2 ? Parse(argv[1]) : 3U;
    const Nat last = argc >= 3 ? Parse(argv[2]) : 100U;
    if (first > last) throw std::invalid_argument("q_first must be <= q_last");

    Result initial{};
    Result final{};
    for (Nat q = first; q <= last; ++q) {
      const Result result = Check(q);
      if (q == first) initial = result;
      final = result;
    }

    const auto Print = [](const char* label, const Result& result) {
      const double ratio = static_cast<double>(result.gap * result.gap) /
                           static_cast<double>(result.m);
      std::cout << label << " q=" << result.q << " m=" << result.m
                << " n=" << result.n << " gap=" << result.gap
                << " gapSquaredOverM=" << std::fixed << std::setprecision(9)
                << ratio << std::defaultfloat
                << " seedSize=" << result.seed_size << '\n';
    };

    std::cout << "use-gap-counterexample checked=" << (last - first + 1U)
              << " qRange=[" << first << ',' << last << "]\n";
    Print("first", initial);
    Print("last", final);
    std::cout << "all exact greedy continuations passed; every row has "
                 "gap^2 < 6m\n";
    return EXIT_SUCCESS;
  } catch (const std::exception& error) {
    std::cerr << "use-gap-counterexample error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
}
