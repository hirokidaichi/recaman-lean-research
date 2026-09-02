// Run-length simulator of the canonical Recaman orbit.
//
// The visited set is stored as a sorted std::vector of disjoint, maximal,
// closed intervals [lo, hi] instead of a dense bitset, so the orbit can be
// followed far beyond the memory limit of dense storage.  Empirically the
// number of maximal runs grows by ~2.8x per decade (4,456 at clock 1e7,
// 13,652 at 1e8, 37,651 at 1e9), so the interval vector stays small.
// Extending a run at either end is an in-place update; a brand-new isolated
// value or a merge of two runs costs a memmove, and both events are rare
// (about 1e-4 per clock).  Two cached indices (one for the subtraction side,
// one for the addition side) make the typical membership query and insertion
// O(1); the fallback is a binary search, O(log k) in the number k of runs.
//
// Definition (exact): a(0) = 0, history {0}.  At clock n >= 1 the candidate is
// a(n-1) - n when a(n-1) > n.  Subtract (a(n) = candidate) iff a(n-1) > n and
// the candidate is not in the history; otherwise a(n) = a(n-1) + n.  Insert
// a(n) into the history.
//
// Two modes.
//   plain  : one clock per loop iteration.
//   accel  : ping-pong sections (after Ben Chaffin).  From a state
//            (clock n, a(n-1) = v) with L = v - n unvisited the orbit
//            alternates subtraction/addition, landing v-n-j at clock n+2j and
//            v+j+1 at clock n+2j+1, until (a) the lower value v-n-j is already
//            visited (then two additions follow) or (b) after landing v-n-j
//            the value v-2n-3j-1 is unvisited and positive (two subtractions
//            follow).  Both stopping steps are decided by the visited set as it
//            was at the section start, so the number J of complete
//            (subtract, add) pairs is found by one look-up below v-n and one
//            scan of the holes below v-2n-1 restricted to one residue class
//            mod 3.  The J pairs are then applied at once: two contiguous
//            ranges are inserted into the interval set and every census
//            column is updated in closed form (all clocks, values and heights
//            of the pairs are affine in j).  The stopping steps themselves and
//            every special clock (decade boundary, progress line, a section
//            whose lower range would cover the least missing value) are
//            executed by the plain step, so the output of the two modes is
//            identical by construction; this is checked against the plain
//            mode at 1e9 and 3e9.
//
// Output per decade [10^k, 10^(k+1)) of state clocks n:
//   clocks, interior (a n <= 2n+1), subDiagonal (a n < n), and for interior
//   clocks with height h = a n - n >= 1: the counts with h <= 1356 and
//   1357 <= h <= 4095 and the minimum h with its (first) clock (these
//   columns are defined exactly as in near_diagonal_rate_probe.cpp);
//   chain entries into the height band [1, K] for K in {2^10, 2^12, ..., 2^20}:
//   a clock n with 1 <= h(n) <= K and h(n-1) not in [1, K], counted with the
//   residue of h(n) mod 3;
//   late landings: clocks n with a(n) < n and a(n) <= 2^20, with the first 20
//   such clocks beyond 1e9 listed.
// At every decade boundary 10^k (after the clock 10^k is processed) the
// interval count, the visited count, the least missing value (mex) and the
// largest value so far are recorded.  Every change of the mex is logged with
// its clock, and the first clocks landing on 19 and on 1355 are reported.
//
// Build:  c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
//           experiments/run_length_recaman_simulator.cpp -o /tmp/rlsim
// Run:    /tmp/rlsim HORIZON [plain|accel] [ACCEL_FROM]
//         default mode accel, ACCEL_FROM (first clock at which sections are
//         used) default 2097152.  Progress lines go to stderr every 1e9 clocks.

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using Nat = std::uint64_t;
using Int = std::int64_t;

constexpr Int kInf = std::numeric_limits<Int>::max() / 4;

Int FloorDiv(Int a, Int b) {  // b > 0
  Int q = a / b;
  if (a % b != 0 && a < 0) --q;
  return q;
}
Int CeilDiv(Int a, Int b) { return -FloorDiv(-a, b); }
Int Mod3(Int a) { return ((a % 3) + 3) % 3; }

struct Range {
  Int lo, hi;
  bool Empty() const { return lo > hi; }
  Int Size() const { return Empty() ? 0 : hi - lo + 1; }
  bool Has(Int j) const { return lo <= j && j <= hi; }
};
Range Meet(Range a, Range b) {
  return Range{std::max(a.lo, b.lo), std::min(a.hi, b.hi)};
}
// Number of j in r with j = t (mod 3), 0 <= t < 3.
Int CountResidue(Range r, Int t) {
  if (r.Empty()) return 0;
  return FloorDiv(r.hi - t, 3) - FloorDiv(r.lo - 1 - t, 3);
}

class IntervalSet {
 public:
  enum Slot : std::size_t { kSub = 0, kAdd = 1 };
  struct Interval {
    Nat lo, hi;
  };

  IntervalSet() { runs_.push_back(Interval{0U, 0U}); }

  // Index of the last run with lo <= x, consulting the cached index of
  // `slot` first; the cache is updated.  Every x has one because the first
  // run starts at 0.
  std::size_t Locate(Nat x, std::size_t slot) {
    const std::size_t p = LocateFrom(x, hint_[slot]);
    hint_[slot] = p;
    return p;
  }
  const Interval& Run(std::size_t p) const { return runs_[p]; }

  bool Contains(Nat x, std::size_t slot) {
    return x <= runs_[Locate(x, slot)].hi;
  }

  // Inserts x; returns true iff x was not yet visited.
  bool Insert(Nat x, std::size_t slot) {
    const std::size_t p = Locate(x, slot);
    const std::size_t n = runs_.size();
    if (x <= runs_[p].hi) return false;
    const bool touch_lo = runs_[p].hi + 1U == x;
    const bool touch_hi = p + 1U < n && runs_[p + 1U].lo == x + 1U;
    if (touch_lo && touch_hi) {
      runs_[p].hi = runs_[p + 1U].hi;
      runs_.erase(runs_.begin() + static_cast<std::ptrdiff_t>(p) + 1);
      for (std::size_t& h : hint_)
        if (h > p) --h;
      hint_[slot] = p;
    } else if (touch_lo) {
      runs_[p].hi = x;
      hint_[slot] = p;
    } else if (touch_hi) {
      runs_[p + 1U].lo = x;
      hint_[slot] = p + 1U;
    } else {
      runs_.insert(runs_.begin() + static_cast<std::ptrdiff_t>(p) + 1,
                   Interval{x, x});
      for (std::size_t& h : hint_)
        if (h > p) ++h;
      hint_[slot] = p + 1U;
    }
    return true;
  }

  // Inserts the whole range [lo, hi]; returns the number of fresh values and
  // caches the index of the run that now contains the range in `slot`.
  Nat InsertRange(Nat lo, Nat hi, std::size_t slot) {
    const std::size_t n = runs_.size();
    const std::size_t p = Predecessor(lo);
    const std::size_t first = runs_[p].hi + 1U >= lo ? p : p + 1U;
    std::size_t q = first;
    Nat overlap = 0U;
    while (q < n && runs_[q].lo <= hi + 1U) {
      overlap += Overlap(runs_[q], lo, hi);
      ++q;
    }
    if (q == first) {
      runs_.insert(runs_.begin() + static_cast<std::ptrdiff_t>(first),
                   Interval{lo, hi});
      for (std::size_t& h : hint_)
        if (h >= first) ++h;
      hint_[slot] = first;
      return hi - lo + 1U;
    }
    const Nat new_lo = std::min(lo, runs_[first].lo);
    const Nat new_hi = std::max(hi, runs_[q - 1U].hi);
    runs_[first] = Interval{new_lo, new_hi};
    if (q - first > 1U) {
      const std::size_t removed = q - first - 1U;
      runs_.erase(runs_.begin() + static_cast<std::ptrdiff_t>(first) + 1,
                  runs_.begin() + static_cast<std::ptrdiff_t>(q));
      for (std::size_t& h : hint_) {
        if (h >= q) h -= removed;
        else if (h > first) h = first;
      }
    }
    hint_[slot] = first;
    return hi - lo + 1U - overlap;
  }

  Nat CountVisited(Nat lo, Nat hi) const {
    Nat total = 0U;
    for (std::size_t q = Predecessor(lo); q < runs_.size() && runs_[q].lo <= hi;
         ++q)
      total += Overlap(runs_[q], lo, hi);
    return total;
  }

  // Largest unvisited u <= c with u = c (mod 3) and u >= 1, or 0 if none.
  Nat LargestUnvisitedSameResidue(Nat c) const {
    std::size_t q = Predecessor(c);
    if (runs_[q].hi < c) return c;
    while (q > 0U) {
      const Nat gap_hi = runs_[q].lo - 1U;
      const Nat gap_lo = runs_[q - 1U].hi + 1U;
      const Nat u = gap_hi - (gap_hi + 3U - c % 3U) % 3U;
      if (u >= gap_lo) return u;
      --q;
    }
    return 0U;
  }

  std::size_t Count() const { return runs_.size(); }
  // Least missing value; the first run always starts at 0.
  Nat Mex() const { return runs_.front().hi + 1U; }
  Nat Visited() const {
    Nat total = 0U;
    for (const Interval& r : runs_) total += r.hi - r.lo + 1U;
    return total;
  }
  Nat Max() const { return runs_.back().hi; }

 private:
  static Nat Overlap(const Interval& r, Nat lo, Nat hi) {
    const Nat a = std::max(r.lo, lo), b = std::min(r.hi, hi);
    return a <= b ? b - a + 1U : 0U;
  }

  std::size_t Predecessor(Nat x) const {
    const auto it = std::upper_bound(
        runs_.begin(), runs_.end(), x,
        [](Nat value, const Interval& r) { return value < r.lo; });
    return static_cast<std::size_t>(it - runs_.begin()) - 1U;
  }

  std::size_t LocateFrom(Nat x, std::size_t hint) const {
    const std::size_t n = runs_.size();
    if (hint < n) {
      if (runs_[hint].lo <= x) {
        if (hint + 1U == n || runs_[hint + 1U].lo > x) return hint;
        if (hint + 2U == n || runs_[hint + 2U].lo > x) return hint + 1U;
      } else if (hint > 0U && runs_[hint - 1U].lo <= x) {
        return hint - 1U;
      }
    }
    return Predecessor(x);
  }

  std::vector<Interval> runs_;
  std::size_t hint_[2] = {0U, 0U};
};

constexpr std::size_t kBands = 6U;
constexpr Int kBand[kBands] = {1024, 4096, 16384, 65536, 262144, 1048576};
constexpr Int kLateBound = 1048576;
constexpr Nat kLateListFrom = 1000000000ULL;
constexpr std::size_t kLateListSize = 20U;
constexpr std::size_t kMexLogSize = 256U;
// Values whose first landing clock is reported (OEIS A057167: 19 first
// appears at index 99734, 1355 at index 325374625245).
constexpr std::size_t kWatchedCount = 8U;
constexpr Nat kWatched[kWatchedCount] = {
    19U, 1355U,
    // level-two continuation values 2c+v+2 that locked the six deep arcs
    // found through 1e10 (arc trace, 2026-09-02)
    116114826U, 1808080190U, 3220375114U, 5578301875U, 9821537786U,
    16833143412U};
constexpr Nat kProgressStep = 1000000000ULL;

// Band level of a height: the smallest i with h <= kBand[i] when
// 1 <= h <= kBand[5], otherwise kBands.  h is in band i iff Level(h) <= i.
std::size_t Level(Int h) {
  if (h < 1 || h > kBand[kBands - 1U]) return kBands;
  std::size_t i = 0U;
  while (h > kBand[i]) ++i;
  return i;
}

struct Decade {
  Nat clocks = 0U, interior = 0U, sub_diagonal = 0U, subtractions = 0U,
      fresh = 0U;
  Nat height_le_1356 = 0U, height_1357_4095 = 0U, min_height = 0U,
      min_height_clock = 0U;
  Nat entries[kBands] = {};
  Nat entries_mod3[kBands][3] = {};
  Nat late = 0U, late_fresh = 0U;
  Nat sections = 0U, section_clocks = 0U, max_pairs = 0U, plain_steps = 0U;
  // Section look-ahead census: histograms of log10(j_a / n) and
  // log10(j_b / n) in bins of width 0.5 from -12 to 0 (index 0 collects
  // everything below -12), and which bound was binding.
  static constexpr std::size_t kLogBins = 25U;
  Nat hist_ja[kLogBins] = {};
  Nat hist_jb[kLogBins] = {};
  Nat jb_infinite = 0U;
  Nat stop_a = 0U, stop_b = 0U, stop_cap = 0U;

  void UpdateMin(Nat h, Nat clock) {
    if (min_height == 0U || h < min_height ||
        (h == min_height && clock < min_height_clock)) {
      min_height = h;
      min_height_clock = clock;
    }
  }
};

struct Checkpoint {
  Nat clock = 0U, intervals = 0U, visited = 0U, mex = 0U, max_value = 0U,
      value = 0U;
  double elapsed = 0.0;
};

struct LateLanding {
  Nat clock = 0U, value = 0U;
  bool fresh = false;
};

struct MexChange {
  Nat clock = 0U, old_mex = 0U, new_mex = 0U;
};

class Simulator {
 public:
  Simulator(Nat horizon, bool accel, Nat accel_from)
      : horizon_(horizon), accel_(accel), accel_from_(accel_from),
        start_(std::chrono::steady_clock::now()) {}

  void Run() {
    while (clock_ <= horizon_) {
      if (accel_ && clock_ >= accel_from_ && clock_ >= plain_until_ &&
          TrySection())
        continue;
      PlainStep();
    }
  }

  void Print() const;

 private:
  double Elapsed() const {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() -
                                         start_)
        .count();
  }

  void PlainStep() {
    const Nat clock = clock_;
    if (clock == next_boundary_) {
      ++decade_;
      next_boundary_ *= 10U;
    }
    const Nat candidate = value_ > clock ? value_ - clock : 0U;
    const bool subtract =
        value_ > clock && !seen_.Contains(candidate, IntervalSet::kSub);
    value_ = subtract ? candidate : value_ + clock;
    const bool fresh = seen_.Insert(
        value_, subtract ? IntervalSet::kSub : IntervalSet::kAdd);

    Decade& d = decades_[decade_];
    ++d.clocks;
    ++d.plain_steps;
    if (subtract) ++d.subtractions;
    if (fresh) ++d.fresh;
    const bool interior = value_ <= 2U * clock + 1U;
    if (interior) ++d.interior;
    if (value_ < clock) ++d.sub_diagonal;
    const Int height = static_cast<Int>(value_) - static_cast<Int>(clock);
    if (interior && height > 0) {
      const Nat h = static_cast<Nat>(height);
      if (h <= 1356U) ++d.height_le_1356;
      else if (h <= 4095U) ++d.height_1357_4095;
      d.UpdateMin(h, clock);
    }
    const std::size_t level = Level(height);
    if (level < previous_level_) {
      const std::size_t residue = static_cast<std::size_t>(Mod3(height));
      for (std::size_t i = level; i < previous_level_; ++i) {
        ++d.entries[i];
        ++d.entries_mod3[i][residue];
      }
    }
    previous_level_ = level;
    if (value_ < clock && value_ <= static_cast<Nat>(kLateBound)) {
      ++d.late;
      if (fresh) ++d.late_fresh;
      if (clock > kLateListFrom && late_list_.size() < kLateListSize)
        late_list_.push_back(LateLanding{clock, value_, fresh});
    }
    for (std::size_t w = 0U; w < kWatchedCount; ++w)
      if (value_ == kWatched[w]) Watched_(w, clock);
    if (fresh && value_ == mex_) {
      const Nat new_mex = seen_.Mex();
      if (mex_log_.size() < kMexLogSize)
        mex_log_.push_back(MexChange{clock, mex_, new_mex});
      else
        ++mex_log_dropped_;
      mex_ = new_mex;
    }
    if (clock * 10U == next_boundary_) Checkpoint_();
    if (clock == next_progress_) {
      Progress_();
      next_progress_ += kProgressStep;
    }
    clock_ = clock + 1U;
  }

  // Attempts to apply a ping-pong section from the current state; returns
  // false when no complete pair can be applied (the caller then takes a
  // plain step).
  bool TrySection() {
    const Nat n = clock_, v = value_;
    if (v <= n) return false;
    const Nat lower0 = v - n;
    const std::size_t p = seen_.Locate(lower0, IntervalSet::kSub);
    const Nat below = seen_.Run(p).hi;
    if (below >= lower0) return false;  // first subtraction blocked
    const Int j_a = static_cast<Int>(lower0 - below);
    Int j_b = kInf;
    const Int c0 = static_cast<Int>(v) - 2 * static_cast<Int>(n) - 1;
    if (c0 >= 1) {
      const Nat u = seen_.LargestUnvisitedSameResidue(static_cast<Nat>(c0));
      if (u != 0U) j_b = (c0 - static_cast<Int>(u)) / 3;
    }
    const Nat last_allowed =
        std::min({next_boundary_ - 1U, next_progress_ - 1U, horizon_});
    if (last_allowed < n) return false;
    const Int cap = static_cast<Int>((last_allowed - n + 1U) / 2U);
    const Int pairs = std::min({j_a, j_b, cap});
    if (pairs < 1) return false;
    {
      Decade& dc = decades_[decade_];
      const auto bin_of = [](Int x, Nat nn) {
        const double r = std::log10(static_cast<double>(x) /
                                    static_cast<double>(nn));
        Int b = static_cast<Int>(std::floor((r + 12.0) * 2.0)) + 1;
        if (b < 0) b = 0;
        if (b > static_cast<Int>(Decade::kLogBins) - 1)
          b = static_cast<Int>(Decade::kLogBins) - 1;
        return static_cast<std::size_t>(b);
      };
      ++dc.hist_ja[bin_of(j_a, n)];
      if (j_b == kInf) ++dc.jb_infinite; else ++dc.hist_jb[bin_of(j_b, n)];
      if (pairs == j_a) ++dc.stop_a;
      else if (pairs == j_b) ++dc.stop_b;
      else ++dc.stop_cap;
    }
    // Hazard: the lower range would cover the least missing value (or the
    // mex is not far below the clock).  Let the plain step handle it.
    if (mex_ >= n) {
      plain_until_ = n + 1U;
      return false;
    }
    if (lower0 - static_cast<Nat>(pairs) + 1U <= mex_ && mex_ <= lower0) {
      plain_until_ = n + 2U * (lower0 - mex_) + 2U;
      return false;
    }
    ApplySection(static_cast<Nat>(pairs));
    return true;
  }

  // Applies J complete pairs: lower values v-n-j at clocks n+2j and upper
  // values v+j+1 at clocks n+2j+1 for j = 0..J-1.
  void ApplySection(Nat pairs) {
    const Nat n = clock_, v = value_;
    const Int J = static_cast<Int>(pairs);
    const Int nn = static_cast<Int>(n), vv = static_cast<Int>(v);
    const Int A = vv - 2 * nn;      // lower height v-2n-3j
    const Int B = vv - nn;          // upper height v-n-j; B = lower0 >= 1
    const Int C = vv - 3 * nn - 1;  // lower interior iff 5j >= C
    const Range all{0, J - 1};
    Decade& d = decades_[decade_];

    ++d.sections;
    d.section_clocks += 2U * pairs;
    d.max_pairs = std::max(d.max_pairs, pairs);
    d.clocks += 2U * pairs;
    d.subtractions += pairs;

    const Range interior_l = Meet(all, Range{CeilDiv(C, 5), kInf});
    const Range interior_u = Meet(all, Range{CeilDiv(A - 2, 3), kInf});
    d.interior += static_cast<Nat>(interior_l.Size() + interior_u.Size());
    const Range sub_l = Meet(all, Range{FloorDiv(A, 3) + 1, kInf});
    const Range sub_u = Meet(all, Range{B + 1, kInf});
    d.sub_diagonal += static_cast<Nat>(sub_l.Size() + sub_u.Size());

    const Range pos_l = Meet(interior_l, Range{-kInf, FloorDiv(A - 1, 3)});
    if (!pos_l.Empty()) {
      d.height_le_1356 += static_cast<Nat>(
          Meet(pos_l, Range{CeilDiv(A - 1356, 3), kInf}).Size());
      d.height_1357_4095 += static_cast<Nat>(
          Meet(pos_l, Range{CeilDiv(A - 4095, 3), FloorDiv(A - 1357, 3)})
              .Size());
      d.UpdateMin(static_cast<Nat>(A - 3 * pos_l.hi),
                  n + 2U * static_cast<Nat>(pos_l.hi));
    }
    const Range pos_u = Meet(interior_u, Range{-kInf, B - 1});
    if (!pos_u.Empty()) {
      d.height_le_1356 +=
          static_cast<Nat>(Meet(pos_u, Range{B - 1356, kInf}).Size());
      d.height_1357_4095 +=
          static_cast<Nat>(Meet(pos_u, Range{B - 4095, B - 1357}).Size());
      d.UpdateMin(static_cast<Nat>(B - pos_u.hi),
                  n + 2U * static_cast<Nat>(pos_u.hi) + 1U);
    }

    // Chain entries.  Lower clock n+2j (j >= 1) is preceded by the upper
    // clock n+2j-1 with height B-(j-1); upper clock n+2j+1 by the lower
    // clock n+2j with height A-3j; lower clock n is preceded by the state
    // before the section (previous_level_).
    for (std::size_t i = 0U; i < kBands; ++i) {
      const Int K = kBand[i];
      const Range in_l =
          Meet(all, Range{CeilDiv(A - K, 3), FloorDiv(A - 1, 3)});
      const Range in_u = Meet(all, Range{B - K, B - 1});
      const Range x = Meet(in_l, Range{1, kInf});
      Int lower_entries = x.Size() - Meet(x, Range{B - K + 1, B}).Size();
      if (in_l.Has(0) && previous_level_ > i) ++lower_entries;
      d.entries[i] += static_cast<Nat>(lower_entries);
      d.entries_mod3[i][static_cast<std::size_t>(Mod3(A))] +=
          static_cast<Nat>(lower_entries);
      Range pieces[2] = {in_u, Range{1, 0}};
      if (!in_u.Empty() && !in_l.Empty() && in_l.lo <= in_u.hi &&
          in_u.lo <= in_l.hi) {
        pieces[0] = Range{in_u.lo, in_l.lo - 1};
        pieces[1] = Range{in_l.hi + 1, in_u.hi};
      }
      for (const Range& piece : pieces) {
        if (piece.Empty()) continue;
        d.entries[i] += static_cast<Nat>(piece.Size());
        for (Int r = 0; r < 3; ++r)
          d.entries_mod3[i][static_cast<std::size_t>(r)] +=
              static_cast<Nat>(CountResidue(piece, Mod3(B - r)));
      }
    }

    // Late landings.  All lower values are fresh.
    const Range late_l = Meet(sub_l, Range{B - kLateBound, kInf});
    d.late += static_cast<Nat>(late_l.Size());
    d.late_fresh += static_cast<Nat>(late_l.Size());
    for (Int j = late_l.lo; j <= late_l.hi && late_list_.size() < kLateListSize;
         ++j) {
      const Nat clock = n + 2U * static_cast<Nat>(j);
      if (clock > kLateListFrom)
        late_list_.push_back(
            LateLanding{clock, v - n - static_cast<Nat>(j), true});
    }
    const Range late_u = Meet(sub_u, Range{-kInf, kLateBound - vv - 1});
    if (!late_u.Empty()) {
      const Nat lo = v + 1U + static_cast<Nat>(late_u.lo);
      const Nat hi = v + 1U + static_cast<Nat>(late_u.hi);
      d.late += static_cast<Nat>(late_u.Size());
      d.late_fresh +=
          static_cast<Nat>(late_u.Size()) - seen_.CountVisited(lo, hi);
      for (Int j = late_u.lo;
           j <= late_u.hi && late_list_.size() < kLateListSize; ++j) {
        const Nat clock = n + 2U * static_cast<Nat>(j) + 1U;
        const Nat value = v + 1U + static_cast<Nat>(j);
        if (clock > kLateListFrom)
          late_list_.push_back(LateLanding{
              clock, value, seen_.CountVisited(value, value) == 0U});
      }
    }

    // Watched values.
    const Nat lower_lo = v - n - pairs + 1U, lower_hi = v - n;
    for (std::size_t w = 0U; w < kWatchedCount; ++w) {
      const Nat x = kWatched[w];
      if (lower_lo <= x && x <= lower_hi) Watched_(w, n + 2U * (lower_hi - x));
      if (v + 1U <= x && x <= v + pairs) Watched_(w, n + 2U * (x - v - 1U) + 1U);
    }

    // Interval set.
    const Nat fresh_l = seen_.InsertRange(lower_lo, lower_hi, IntervalSet::kSub);
    if (fresh_l != pairs) throw std::logic_error("lower range not fresh");
    const Nat fresh_u = seen_.InsertRange(v + 1U, v + pairs, IntervalSet::kAdd);
    d.fresh += pairs + fresh_u;
    if (seen_.Mex() != mex_) throw std::logic_error("mex moved in a section");

    previous_level_ = Level(B - J + 1);
    value_ = v + pairs;
    clock_ = n + 2U * pairs;
  }

  void Watched_(std::size_t w, Nat clock) {
    ++watched_landings_[w];
    if (watched_first_clock_[w] == 0U) watched_first_clock_[w] = clock;
  }
  void Checkpoint_() {
    checkpoints_.push_back(Checkpoint{clock_, seen_.Count(), seen_.Visited(),
                                      mex_, seen_.Max(), value_, Elapsed()});
  }
  void Progress_() const {
    std::cerr << "progress clock=" << clock_ << " value=" << value_
              << " intervals=" << seen_.Count() << " mex=" << mex_
              << " elapsed=" << Elapsed() << "s\n";
  }

  const Nat horizon_;
  const bool accel_;
  const Nat accel_from_;
  const std::chrono::steady_clock::time_point start_;
  std::vector<Decade> decades_ = std::vector<Decade>(20);
  std::vector<Checkpoint> checkpoints_;
  std::vector<LateLanding> late_list_;
  std::vector<MexChange> mex_log_;
  Nat mex_log_dropped_ = 0U;
  Nat watched_first_clock_[kWatchedCount] = {};
  Nat watched_landings_[kWatchedCount] = {};
  IntervalSet seen_;
  Nat clock_ = 1U;
  Nat value_ = 0U;
  Nat mex_ = 1U;
  std::size_t previous_level_ = Level(0);  // h(0) = 0 is in no band.
  std::size_t decade_ = 0U;
  Nat next_boundary_ = 10U;
  Nat next_progress_ = kProgressStep;
  Nat plain_until_ = 0U;
};

void Simulator::Print() const {
  std::cout << "run-length-recaman horizon=" << horizon_ << '\n';
  std::cout << "decade clocks interior subDiagonal height<=1356"
               " height1357..4095 minHeight@clock subtractions fresh\n";
  for (std::size_t k = 0U; k < decades_.size(); ++k) {
    const Decade& d = decades_[k];
    if (d.clocks == 0U) continue;
    std::cout << "1e" << k << ' ' << d.clocks << ' ' << d.interior << ' '
              << d.sub_diagonal << ' ' << d.height_le_1356 << ' '
              << d.height_1357_4095 << ' ' << d.min_height << '@'
              << d.min_height_clock << ' ' << d.subtractions << ' ' << d.fresh
              << '\n';
  }
  std::cout << "chain entries per decade into height band [1,K]:"
               " entries (h mod 3 = 0/1/2) for K =";
  for (Int k : kBand) std::cout << ' ' << k;
  std::cout << '\n';
  for (std::size_t k = 0U; k < decades_.size(); ++k) {
    const Decade& d = decades_[k];
    if (d.clocks == 0U) continue;
    std::cout << "1e" << k;
    for (std::size_t i = 0U; i < kBands; ++i)
      std::cout << " | " << d.entries[i] << " (" << d.entries_mod3[i][0] << '/'
                << d.entries_mod3[i][1] << '/' << d.entries_mod3[i][2] << ')';
    std::cout << '\n';
  }
  std::cout << "late landings per decade (a n < n and a n <= " << kLateBound
            << "): count fresh\n";
  for (std::size_t k = 0U; k < decades_.size(); ++k) {
    const Decade& d = decades_[k];
    if (d.clocks == 0U) continue;
    std::cout << "1e" << k << ' ' << d.late << ' ' << d.late_fresh << '\n';
  }
  std::cout << "first " << kLateListSize << " late landings beyond clock "
            << kLateListFrom << ": clock value fresh (" << late_list_.size()
            << " listed)\n";
  for (const LateLanding& l : late_list_)
    std::cout << "late " << l.clock << ' ' << l.value << ' '
              << (l.fresh ? "fresh" : "revisit") << '\n';
  std::cout << "checkpoint clock intervals visited mex maxValue value"
               " elapsed\n";
  for (const Checkpoint& c : checkpoints_)
    std::cout << "at " << c.clock << ' ' << c.intervals << ' ' << c.visited
              << ' ' << c.mex << ' ' << c.max_value << ' ' << c.value << ' '
              << c.elapsed << '\n';
  std::cout << "mex changes: clock oldMex newMex (" << mex_log_.size()
            << " listed, " << mex_log_dropped_ << " dropped)\n";
  for (const MexChange& m : mex_log_)
    std::cout << "mex " << m.clock << ' ' << m.old_mex << ' ' << m.new_mex
              << '\n';
  for (std::size_t w = 0U; w < kWatchedCount; ++w) {
    std::cout << "value " << kWatched[w] << ": ";
    if (watched_first_clock_[w] == 0U)
      std::cout << "never visited through clock " << horizon_ << '\n';
    else
      std::cout << "first visited at clock " << watched_first_clock_[w]
                << ", " << watched_landings_[w] << " landings\n";
  }
  std::cout << "final clock=" << horizon_ << " value=" << value_
            << " intervals=" << seen_.Count() << " mex=" << mex_
            << " elapsed=" << Elapsed() << "s\n";
  std::cout << "mode=" << (accel_ ? "accel" : "plain")
            << " accelFrom=" << accel_from_ << '\n';
  std::cout << "sections per decade: sections sectionClocks maxPairs"
               " plainSteps\n";
  for (std::size_t k = 0U; k < decades_.size(); ++k) {
    const Decade& d = decades_[k];
    if (d.clocks == 0U) continue;
    std::cout << "1e" << k << ' ' << d.sections << ' ' << d.section_clocks
              << ' ' << d.max_pairs << ' ' << d.plain_steps << '\n';
  }
  std::cout << "section look-ahead per decade: stopA stopB stopCap jbInfinite\n";
  for (std::size_t k = 0U; k < decades_.size(); ++k) {
    const Decade& d = decades_[k];
    if (d.sections == 0U) continue;
    std::cout << "1e" << k << ' ' << d.stop_a << ' ' << d.stop_b << ' '
              << d.stop_cap << ' ' << d.jb_infinite << '\n';
  }
  std::cout << "histogram bins: log10(x/n) in [-12,-11.5) ... [-0.5,0) plus"
               " an underflow bin first\n";
  for (std::size_t k = 0U; k < decades_.size(); ++k) {
    const Decade& d = decades_[k];
    if (d.sections == 0U) continue;
    std::cout << "ja 1e" << k;
    for (std::size_t b = 0U; b < Decade::kLogBins; ++b) std::cout << ' ' << d.hist_ja[b];
    std::cout << "\njb 1e" << k;
    for (std::size_t b = 0U; b < Decade::kLogBins; ++b) std::cout << ' ' << d.hist_jb[b];
    std::cout << '\n';
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Nat horizon = argc >= 2 ? std::stoull(argv[1]) : 1000000000ULL;
    if (horizon < 10U) throw std::invalid_argument("horizon must be >= 10");
    const std::string mode = argc >= 3 ? argv[2] : "accel";
    if (mode != "plain" && mode != "accel")
      throw std::invalid_argument("mode must be plain or accel");
    const Nat accel_from = argc >= 4 ? std::stoull(argv[3]) : 2097152ULL;
    Simulator simulator(horizon, mode == "accel", accel_from);
    simulator.Run();
    simulator.Print();
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
