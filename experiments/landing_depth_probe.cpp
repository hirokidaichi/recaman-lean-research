// Arc minima ("landings") of Recaman-type orbits, in Chaffin's sense.
//
// For an orbit a(0)=v0 with history {v0} and the exact greedy rule, the
// residue a(n) mod n is nonincreasing until it wraps around; a landing is the
// minimum value of a(n) between two consecutive increases of the residue
// (OEIS A393814 / A393815 for the canonical orbit).  The probe lists the
// landings per decade of index with the depth D = log10(index) - log10(value)
// and reports the per-decade count and the quantiles of D, so that the
// stationarity of the depth distribution can be compared between the
// canonical orbit and generalized orbits (single initial value v0).
//
// Usage: landing_depth_probe v0 horizon [list]
//   list = 1 prints every landing (index value) after the summary.

#include <algorithm>
#include <cmath>
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
  void Insert(Nat value) {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    if (word >= bits_.size()) bits_.resize(word + word / 2U + 1U, 0U);
    bits_[word] |= 1ULL << (value & 63U);
  }

 private:
  std::vector<std::uint64_t> bits_;
};

struct Landing {
  Nat index;
  Nat value;
};

}  // namespace

int main(int argc, char** argv) {
  try {
    const Nat start = argc >= 2 ? std::stoull(argv[1]) : 0U;
    const Nat horizon = argc >= 3 ? std::stoull(argv[2]) : 100000000ULL;
    const bool list = argc >= 4 && std::stoull(argv[3]) == 1U;
    if (horizon < 100U || horizon > 4000000000ULL)
      throw std::invalid_argument("horizon must be in 100..4e9");
    DenseSet seen;
    seen.Insert(start);
    Nat value = start;
    std::vector<Landing> landings;
    Nat previous_residue = 0U;
    Nat arc_min_value = 0U, arc_min_index = 0U;
    bool in_arc = false;
    for (Nat clock = 1U; clock <= horizon; ++clock) {
      const Nat candidate = value > clock ? value - clock : 0U;
      const bool subtract = value > clock && !seen.Contains(candidate);
      value = subtract ? candidate : value + clock;
      seen.Insert(value);
      const Nat residue = value % clock;
      if (in_arc && residue > previous_residue) {
        landings.push_back(Landing{arc_min_index, arc_min_value});
        in_arc = false;
      }
      if (!in_arc) {
        in_arc = true;
        arc_min_value = value;
        arc_min_index = clock;
      } else if (value < arc_min_value) {
        arc_min_value = value;
        arc_min_index = clock;
      }
      previous_residue = residue;
    }
    std::vector<Nat> per_decade(12, 0U);
    std::vector<double> depths;
    for (const Landing& l : landings) {
      std::size_t decade = 0U;
      for (Nat power = 10U; power <= l.index; power *= 10U) ++decade;
      ++per_decade[decade];
      if (l.index >= 1000U && l.value > 0U)
        depths.push_back(std::log10(static_cast<double>(l.index)) -
                         std::log10(static_cast<double>(l.value)));
    }
    std::sort(depths.begin(), depths.end());
    std::cout << "landing-depth start=" << start << " horizon=" << horizon
              << " landings=" << landings.size() << " perDecade=";
    for (std::size_t k = 0U; k < per_decade.size(); ++k)
      if (per_decade[k] != 0U) std::cout << "1e" << k << ':' << per_decade[k] << ' ';
    std::cout << '\n';
    if (!depths.empty()) {
      const std::size_t n = depths.size();
      std::cout << "depth(index>=1e3) n=" << n
                << " median=" << depths[n / 2]
                << " q90=" << depths[static_cast<std::size_t>(n * 0.9)]
                << " q99=" << depths[static_cast<std::size_t>(n * 0.99)]
                << " max=" << depths[n - 1] << '\n';
    }
    std::cout << "first landings:";
    for (std::size_t i = 0U; i < std::min<std::size_t>(landings.size(), 19U); ++i)
      std::cout << ' ' << landings[i].index << '=' << landings[i].value;
    std::cout << '\n';
    if (list)
      for (const Landing& l : landings) std::cout << l.index << ' ' << l.value << '\n';
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
