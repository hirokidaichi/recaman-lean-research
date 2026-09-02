// Per-decade census of near-diagonal events on the canonical Recaman orbit.
//
// For every state clock n in [10^k, 10^(k+1)) the probe counts
//   interior       a n <= 2n + 1            (cone-interior clock)
//   subDiagonal    a n <  n                 (the value sits below its clock)
//   candidate01    a n <= n + 2             (next candidate is 0 or 1)
//   smallExcess    2n + 1 < a n <= 2n + 65  (cone excess in 1..64)
//   interiorSub    interior clock followed by a subtraction
//   doubleInterior interior clock followed by an interior clock
// These are the quantities that decide which side of the dichotomy
// "candidate <= 1 infinitely often, or missing density >= 1/4" the orbit is
// on, and how fast a fixed value can still be landed late.

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>

namespace {

using Nat = std::uint64_t;

class DenseSet {
 public:
  bool Contains(Nat value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < bits_.size() && ((bits_[word] >> (value & 63U)) & 1ULL) != 0U;
  }
  Nat CountUnvisited(Nat lo, Nat hi) const {
    Nat count = 0U;
    for (Nat v = lo; v <= hi; ++v)
      if (!Contains(v)) ++count;
    return count;
  }
  void Insert(Nat value) {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    if (word >= bits_.size()) bits_.resize(word + word / 2U + 1U, 0U);
    bits_[word] |= 1ULL << (value & 63U);
  }

 private:
  std::vector<std::uint64_t> bits_;
};

struct Decade {
  Nat clocks = 0U, interior = 0U, sub_diagonal = 0U, candidate01 = 0U,
      small_excess = 0U, interior_sub = 0U, double_interior = 0U,
      near_relative = 0U;
  // Cone excess e = a n - 2n - 1 > 0 binned by floor(log4 e), bins 0..14.
  Nat excess_bins[15] = {};
  // Sharp thresholds around the frozen least missing value 1355.
  Nat excess_le_1356 = 0U, excess_1357_4095 = 0U, min_excess = 0U,
      min_excess_clock = 0U;
  Nat height_le_1356 = 0U, height_1357_4095 = 0U, min_height = 0U,
      min_height_clock = 0U;
};

// Checkpoint statistics at clock n = 10^k: unvisited values in [0, n] and in
// the band [n, n + 100000] just above the clock.  These densities govern how
// often a fresh candidate can still land near the diagonal.
struct Checkpoint {
  Nat clock = 0U, unvisited_below = 0U, unvisited_band = 0U;
};

}  // namespace

int main(int argc, char** argv) {
  try {
    const Nat horizon = argc >= 2 ? std::stoull(argv[1]) : 100000000ULL;
    if (horizon < 10U || horizon > 4000000000ULL)
      throw std::invalid_argument("horizon must be in 10..4e9");
    std::vector<Decade> decades(12);
    std::vector<Checkpoint> checkpoints;
    Nat next_checkpoint = 10U;
    DenseSet seen;
    seen.Insert(0U);
    Nat value = 0U;
    bool previous_interior = false;
    std::size_t previous_decade = 0U;
    for (Nat clock = 1U; clock <= horizon; ++clock) {
      const Nat candidate = value > clock ? value - clock : 0U;
      const bool subtract = value > clock && !seen.Contains(candidate);
      // The step into `clock` decides the classification of the previous
      // interior clock.
      if (previous_interior && subtract) ++decades[previous_decade].interior_sub;
      value = subtract ? candidate : value + clock;
      seen.Insert(value);
      std::size_t decade = 0U;
      for (Nat power = 10U; power <= clock; power *= 10U) ++decade;
      Decade& d = decades[decade];
      ++d.clocks;
      const bool interior = value <= 2U * clock + 1U;
      if (interior) ++d.interior;
      if (value < clock) ++d.sub_diagonal;
      if (value <= clock + 2U) ++d.candidate01;
      if (!interior && value <= 2U * clock + 65U) ++d.small_excess;
      if (value > clock && value - clock <= clock / 1000U + 1U) ++d.near_relative;
      if (!interior) {
        const Nat raw_excess = value - 2U * clock - 1U;
        if (raw_excess <= 1356U) ++d.excess_le_1356;
        else if (raw_excess <= 4095U) ++d.excess_1357_4095;
        if (d.min_excess == 0U || raw_excess < d.min_excess) {
          d.min_excess = raw_excess;
          d.min_excess_clock = clock;
        }
        Nat excess = raw_excess;
        std::size_t bin = 0U;
        while (excess >= 4U && bin < 14U) { excess /= 4U; ++bin; }
        ++d.excess_bins[bin];
      } else if (value > clock) {
        const Nat height = value - clock;
        if (height <= 1356U) ++d.height_le_1356;
        else if (height <= 4095U) ++d.height_1357_4095;
        if (d.min_height == 0U || height < d.min_height) {
          d.min_height = height;
          d.min_height_clock = clock;
        }
      }
      if (clock == next_checkpoint) {
        checkpoints.push_back(Checkpoint{clock, seen.CountUnvisited(0U, clock),
                                         seen.CountUnvisited(clock, clock + 100000U)});
        next_checkpoint *= 10U;
      }
      if (previous_interior && interior) ++decades[previous_decade].double_interior;
      previous_interior = interior;
      previous_decade = decade;
    }
    std::cout << "near-diagonal-rate horizon=" << horizon << '\n';
    std::cout << "decade clocks interior subDiagonal candidate01 smallExcess"
                 " interiorSub doubleInterior nearRelative(h<=n/1000)\n";
    for (std::size_t k = 0U; k < decades.size(); ++k) {
      const Decade& d = decades[k];
      if (d.clocks == 0U) continue;
      std::cout << "1e" << k << ' ' << d.clocks << ' ' << d.interior << ' '
                << d.sub_diagonal << ' ' << d.candidate01 << ' '
                << d.small_excess << ' ' << d.interior_sub << ' '
                << d.double_interior << ' ' << d.near_relative << '\n';
    }
    std::cout << "excess bins per decade: e in [4^j, 4^(j+1)) for j=0..14\n";
    for (std::size_t k = 0U; k < decades.size(); ++k) {
      const Decade& d = decades[k];
      if (d.clocks == 0U) continue;
      std::cout << "1e" << k;
      for (std::size_t j = 0U; j < 15U; ++j) std::cout << ' ' << d.excess_bins[j];
      std::cout << '\n';
    }
    std::cout << "thresholds per decade: excess<=1356 excess1357..4095 minExcess@clock"
                 " | interior height<=1356 height1357..4095 minHeight@clock\n";
    for (std::size_t k = 0U; k < decades.size(); ++k) {
      const Decade& d = decades[k];
      if (d.clocks == 0U) continue;
      std::cout << "1e" << k << ' ' << d.excess_le_1356 << ' ' << d.excess_1357_4095
                << ' ' << d.min_excess << '@' << d.min_excess_clock << " | "
                << d.height_le_1356 << ' ' << d.height_1357_4095 << ' '
                << d.min_height << '@' << d.min_height_clock << '\n';
    }
    std::cout << "checkpoint clock unvisited[0,n] unvisited[n,n+1e5]\n";
    for (const Checkpoint& c : checkpoints)
      std::cout << "at " << c.clock << ' ' << c.unvisited_below << ' '
                << c.unvisited_band << '\n';
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
