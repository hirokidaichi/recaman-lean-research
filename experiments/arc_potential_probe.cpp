// Arc potential probe of the canonical Recaman orbit.
//
// Simulator core copied from arc_trace_probe.cpp: a plain (one clock per
// iteration) run with the interval-set history, the exact step rule and
// Chaffin's arc detector.  Definitions (exact).  a(0) = 0, history {0}.  At
// clock n >= 1 the candidate is a(n-1) - n; subtract iff a(n-1) > n and the
// candidate is not in the history, else add n.  Write a(n) = k(n) n + r(n)
// with 0 <= r(n) < n.  Both step types send r to r - k, so an arc is a maximal
// stretch of clocks without a residue increase; the wrap clock starts the next
// arc.  Late landing: a(n) < n (k = 0).  Comb end: a late landing a(c) = v
// with v - 1 already visited at time c.  At a comb end the step rule forces
// a(c+1) = c+v+1, a(c+2) = 2c+v+3, a(c+3) = 3c+v+6 (the candidate c+v is
// a(c-1)), and the candidate at clock c+4 is the test value 2c+v+2.
// "Blocked" = the test value is visited at time c+3; the three values visited
// at c+1..c+3 differ from it, so this is the same as visited at time c, which
// is what is looked up; both the forced value a(c+3) and "step c+4 is an
// addition iff blocked" are verified at clocks c+3 and c+4 and mismatches are
// counted.
//
// Potential.  At a level-1 clock m (k(m) = 1, i.e. m <= a(m) < 2m) put
// Phi(m) = a(m) + m = 2m + h(m).  Phi* = running maximum of Phi over the
// level-1 clocks of the current arc (reset at each arc start).  At a comb end
// (c, v) the clock c-1 has a(c-1) = c+v and Phi(c-1) = 2c+v-1, the test value
// is Phi(c-1) + 3, and drop = Phi* - (2c+v-1) with Phi* over the level-1
// clocks <= c-1 of the arc (undefined when the arc has no level-1 clock yet,
// which happens only when c-1 is not level 1 or not in the arc, i.e. v >= c-2).
//
// Depth class of a comb end (c, v): 0 if 10v >= c, 1 if 10v < c <= 100v,
// 2 if 100v < c <= 1000v, 3 if 1000v < c (class 3 is the traced regime of
// arc_trace_probe.cpp, where r * 1000 < n at a k = 0 clock).
//
// Per comb end: drop, blocked, continued (the arc has a later late landing;
// a comb end is itself a late landing, so at most one comb end waits for this
// resolution at any time, and the tables in summary.txt count every resolved
// comb end, i.e. all comb ends of the completed arcs plus those of the open
// arc that were followed by a later late landing; for continued comb ends the
// gap to that next late landing is binned by powers of two), endedEarly (the
// arc ends before clock c+4).  Per arc: comb ends, blocked comb ends, comb
// ends with drop >= 3, the first comb end with drop >= 3, the first blocked
// comb end (all classes and class 3 only), the landing (arc minimum), and the
// Phi decreases: level-1 clocks m with Phi(m) below the Phi of the previous
// level-1 clock of the arc (size, height, and the pattern (gap, max k) of the
// clocks between the two level-1 clocks).
//
// Outputs (OUTDIR): summary.txt, arcs.txt (one line per completed arc),
// marked_comb_ends.txt (comb ends that are blocked or have drop >= 3, capped),
// lowdrop_blocked.txt (blocked comb ends with drop < 3 or undefined, capped),
// watch_values.txt (test values of the first 20 of those, for watch mode),
// decreases.txt (8-step windows m-4..m+3 around the first Phi decreases),
// blocked_windows.txt (16-step windows c-3..c+12 around the first blocked
// comb ends of each depth class).
//
// Watch mode: `HORIZON OUTDIR --watch FILE` re-runs the orbit and writes to
// OUTDIR/watch.txt the first-visit clock (with k, r and step type) of every
// value listed in FILE (one per line); the run stops when all are found.
//
// Build: c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
//          experiments/arc_potential_probe.cpp -o /tmp/arcpot
// Run:   /tmp/arcpot HORIZON OUTDIR
//        /tmp/arcpot HORIZON OUTDIR --watch OUTDIR/watch_values.txt

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace {

using Nat = std::uint64_t;
using Int = std::int64_t;

class IntervalSet {
 public:
  enum Slot : std::size_t { kSub = 0, kAdd = 1, kBelow = 2, kTest = 3 };
  static constexpr std::size_t kSlots = 4U;
  struct Interval {
    Nat lo, hi;
  };

  IntervalSet() { runs_.push_back(Interval{0U, 0U}); }

  std::size_t Locate(Nat x, std::size_t slot) {
    const std::size_t p = LocateFrom(x, hint_[slot]);
    hint_[slot] = p;
    return p;
  }

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

  std::size_t Count() const { return runs_.size(); }
  Nat Mex() const { return runs_.front().hi + 1U; }

 private:
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
  std::size_t hint_[kSlots] = {};
};

constexpr Nat kFSub = 1U, kFHasCand = 2U, kFLate = 4U, kFCombEnd = 8U;
constexpr Nat kValueBits = 56U;
constexpr Nat kValueMask = (1ULL << kValueBits) - 1U;

struct Rec {
  Nat clock = 0U;
  Nat value = 0U;
  Nat prev = 0U;  // a(clock-1) in the low 56 bits, flags in the high byte
  Nat Prev() const { return prev & kValueMask; }
  Nat Flags() const { return prev >> kValueBits; }
};

Rec MakeRec(Nat clock, Nat value, Nat prev, Nat flags) {
  return Rec{clock, value, prev | (flags << kValueBits)};
}

// Columns: clock a h k r Phi(k=1 only, else -) step cand candState class.
void PrintRec(std::ostream& out, const Rec& rec, bool mark) {
  const Nat flags = rec.Flags();
  const Nat k = rec.value / rec.clock, r = rec.value % rec.clock;
  const Int h = static_cast<Int>(rec.value) - static_cast<Int>(rec.clock);
  const bool sub = (flags & kFSub) != 0U, has_cand = (flags & kFHasCand) != 0U,
             late = (flags & kFLate) != 0U,
             comb_end = (flags & kFCombEnd) != 0U;
  out << (mark ? "* " : "  ") << rec.clock << ' ' << rec.value << ' ' << h
      << ' ' << k << ' ' << r << ' ';
  if (k == 1U)
    out << rec.value + rec.clock;
  else
    out << '-';
  out << ' ' << (sub ? 'S' : 'A') << ' ';
  if (has_cand)
    out << rec.Prev() - rec.clock << ' ' << (sub ? "fresh" : "blocked");
  else
    out << "- none";
  out << ' ' << (sub ? (late ? "late" : "band") : "-");
  if (comb_end) out << " combEnd";
  out << '\n';
}

struct Landing {
  Nat index = 0U, value = 0U;
};

constexpr std::size_t kCheckpoints = 19U;
constexpr Landing kExpected[kCheckpoints] = {
    {1U, 1U},         {2U, 3U},         {4U, 2U},         {10U, 11U},
    {16U, 8U},        {31U, 14U},       {64U, 26U},       {131U, 4U},
    {222U, 47U},      {403U, 92U},      {770U, 111U},     {1409U, 181U},
    {2652U, 150U},    {4825U, 371U},    {9078U, 361U},    {16773U, 781U},
    {30768U, 828U},   {56827U, 366U},   {99734U, 19U}};

constexpr Nat kProgressStep = 1000000000ULL;
constexpr std::size_t kDropBins = 22U;  // 0..20, 21 = > 20
constexpr std::size_t kSizeBins = 22U;  // 1..20 at index 1..20, 21 = > 20
constexpr std::size_t kDecades = 12U;
constexpr std::size_t kClasses = 4U;
constexpr std::size_t kGapBins = 40U;  // bin b: 2^b <= gap < 2^(b+1)
constexpr std::size_t kRing = 16U;
constexpr Nat kMarkedCap = 200000U, kLowdropCap = 1000000U;
constexpr Nat kGlobalDumps = 10U, kArcDumps = 2U, kClassWindows = 10U;
constexpr std::size_t kWatchFirst = 20U;

std::size_t DropBin(Int drop) {
  return drop > 20 ? 21U : static_cast<std::size_t>(drop);
}
std::size_t SizeBin(Nat size) {
  return size > 20U ? 21U : static_cast<std::size_t>(size);
}
std::size_t Decade(Nat x) {
  std::size_t d = 0U;
  while (x >= 10U && d + 1U < kDecades) {
    x /= 10U;
    ++d;
  }
  return d;
}
std::size_t GapBin(Nat gap) {
  std::size_t b = 0U;
  while (gap >= 2U && b + 1U < kGapBins) {
    gap /= 2U;
    ++b;
  }
  return b;
}
std::size_t DepthClass(Nat c, Nat v) {
  if (v * 10U >= c) return 0U;
  if (v * 100U >= c) return 1U;
  if (v * 1000U >= c) return 2U;
  return 3U;
}

struct CombRef {
  Nat clock = 0U, value = 0U;
  Int drop = 0;
  bool defined = false;
};

struct Arc {
  Nat ordinal = 0U, start_clock = 0U, start_value = 0U;
  Nat min_value = 0U, min_clock = 0U;
  Nat late_total = 0U, last_late_clock = 0U, last_late_value = 0U;
  Nat level1 = 0U;
  bool phi_valid = false;
  Nat phi_star = 0U;
  bool prev_phi_valid = false;
  Nat prev_phi = 0U, prev_l1_clock = 0U, max_k_since = 0U;
  Nat comb_ends = 0U, blocked_ends = 0U, drop3_ends = 0U, undef_ends = 0U,
      neg_ends = 0U;
  Nat comb_ends_c3 = 0U, blocked_ends_c3 = 0U;
  CombRef first_drop3, first_blocked, first_blocked_c3;
  Int max_drop = -1;
  CombRef last_comb;
  bool last_comb_blocked = false;
  Nat decreases = 0U, dec_sum = 0U, dec_max = 0U, dec_hmin = 0U, dec_hmax = 0U,
      dec_printed = 0U;
};

struct PendingComb {  // a comb end waiting for its "continued" resolution
  bool active = false;
  Nat clock = 0U, value = 0U;
  Int drop = 0;
  bool defined = false, blocked = false;
  std::size_t cls = 0U;
};

struct Verify {  // the forced steps after a comb end
  bool active = false;
  Nat clock = 0U, value = 0U;
  bool blocked = false;
};

struct Dump {
  Nat at_clock = 0U, mark_clock = 0U;
  std::size_t window = 0U;
  std::string label;
};

class Probe {
 public:
  Probe(Nat horizon, std::string outdir)
      : horizon_(horizon), outdir_(std::move(outdir)),
        start_(std::chrono::steady_clock::now()) {
    arcs_.open(outdir_ + "/arcs.txt");
    marked_.open(outdir_ + "/marked_comb_ends.txt");
    lowdrop_.open(outdir_ + "/lowdrop_blocked.txt");
    dumps_.open(outdir_ + "/decreases.txt");
    windows_.open(outdir_ + "/blocked_windows.txt");
    if (!arcs_ || !marked_ || !lowdrop_ || !dumps_ || !windows_)
      throw std::runtime_error("cannot open output files");
    arcs_ << "# ordinal startClock endClock startValue landingIndex"
             " landingValue landingIsLastLate stepsAfterLanding lateTotal"
             " level1Clocks combEnds blockedEnds drop3Ends undefEnds negEnds"
             " combEndsC3 blockedEndsC3 firstDrop3(c=v:drop)"
             " firstBlocked(c=v:drop) firstBlockedC3(c=v:drop)"
             " landingCombEnd(drop:blocked) landing==firstBlocked"
             " landing==firstDrop3 landing==firstBlockedC3 maxDrop decreases"
             " decSum decMax decHeightMin decHeightMax\n";
    marked_ << "# comb ends that are blocked or have drop >= 3 (cap "
            << kMarkedCap << ")\n# arc clock value class drop blocked"
            << " test=2c+v+2 phiStar\n";
    lowdrop_ << "# blocked comb ends with drop < 3 or undefined (cap "
             << kLowdropCap << ")\n# arc clock value class drop test=2c+v+2"
             << " phiStar arcStart\n";
    dumps_ << "# 8-step windows (clocks m-4..m+3) around Phi decreases at"
              " level-1 clocks m (marked *); first " << kGlobalDumps
           << " decreases globally and the first " << kArcDumps
           << " of every arc\n# columns: clock a h k r Phi step cand candState"
              " class [combEnd]\n";
    windows_ << "# 16-step windows (clocks c-3..c+12) around the first "
             << kClassWindows << " blocked comb ends (c, v) of each depth"
                " class (marked *)\n# columns: clock a h k r Phi step cand"
                " candState class [combEnd]\n";
  }

  void Run() {
    while (clock_ <= horizon_) Step();
  }

  void WriteSummary() const {
    std::ofstream out(outdir_ + "/summary.txt");
    out << "arc-potential-probe horizon=" << horizon_ << " elapsed="
        << Elapsed() << "s intervals=" << seen_.Count() << " mex="
        << seen_.Mex() << " finalValue=" << value_ << '\n';
    bool ok = landings_.size() >= kCheckpoints;
    for (std::size_t i = 0U; ok && i < kCheckpoints; ++i)
      if (landings_[i].index != kExpected[i].index ||
          landings_[i].value != kExpected[i].value)
        ok = false;
    out << "checkpoint(first " << kCheckpoints << " landings) "
        << (ok ? "PASS" : "FAIL") << '\n';
    out << "first landings:";
    for (std::size_t i = 0U; i < std::min(landings_.size(), kCheckpoints); ++i)
      out << ' ' << landings_[i].index << '=' << landings_[i].value;
    out << '\n';
    out << "completed arcs=" << landings_.size() << '\n';
    out << "verification: a(c+3)=3c+v+6 checked=" << verify3_checked_
        << " mismatches=" << verify3_mismatch_
        << "; step c+4 is addition <=> blocked checked=" << verify4_checked_
        << " mismatches=" << verify4_mismatch_ << '\n';

    Nat total = 0U;
    for (std::size_t s = 0U; s < kClasses; ++s)
      for (std::size_t b = 0U; b < 2U; ++b)
        for (std::size_t c = 0U; c < 2U; ++c)
          for (std::size_t e = 0U; e < 2U; ++e) total += tab_bc_[s][b][c][e];
    out << "\ncomb ends resolved (all comb ends of the completed arcs plus"
           " those of the open arc that are followed by a later late landing;"
           " only the last comb end of the open arc can be unresolved):"
           " total=" << total
        << " blocked=" << blocked_total_ << " dropUndefined="
        << drop_undef_[0] + drop_undef_[1] << " (blocked "
        << drop_undef_[1] << ") dropNegative="
        << drop_neg_[0] + drop_neg_[1] << " (blocked " << drop_neg_[1]
        << ")\n";
    out << "depth class: 0: 10v>=c, 1: 10v<c<=100v, 2: 100v<c<=1000v,"
           " 3: 1000v<c\n";

    out << "\n(i) blocked x continued (continued = the arc has a later late"
           " landing); columns: all | class0 class1 class2 class3\n";
    const char* names[4] = {"blocked & continued     ",
                            "blocked & not continued ",
                            "fresh & continued       ",
                            "fresh & not continued   "};
    for (std::size_t row = 0U; row < 4U; ++row) {
      const std::size_t b = row < 2U ? 1U : 0U, c = (row % 2U == 0U) ? 1U : 0U;
      Nat all = 0U, per[kClasses] = {}, early = 0U;
      for (std::size_t s = 0U; s < kClasses; ++s) {
        per[s] = tab_bc_[s][b][c][0] + tab_bc_[s][b][c][1];
        all += per[s];
        early += tab_bc_[s][b][c][1];
      }
      out << "  " << names[row] << " = " << all << " |";
      for (std::size_t s = 0U; s < kClasses; ++s) out << ' ' << per[s];
      if (c == 0U) out << "  (arc ended before c+4: " << early << ")";
      out << '\n';
    }

    out << "\n(ii) blocked x drop>=3 (defined, nonnegative drops only);"
           " columns: all | class0 class1 class2 class3\n";
    const char* names2[4] = {"blocked & drop>=3 ", "blocked & drop<3  ",
                             "fresh & drop>=3   ", "fresh & drop<3    "};
    for (std::size_t row = 0U; row < 4U; ++row) {
      const std::size_t b = row < 2U ? 1U : 0U, d = (row % 2U == 0U) ? 1U : 0U;
      Nat all = 0U;
      for (std::size_t s = 0U; s < kClasses; ++s) all += tab_bd_[s][b][d];
      out << "  " << names2[row] << " = " << all << " |";
      for (std::size_t s = 0U; s < kClasses; ++s)
        out << ' ' << tab_bd_[s][b][d];
      out << '\n';
    }
    out << "(ii') blocked x drop>=2 (all classes):\n";
    Nat b_ge2 = 0U, b_lt2 = 0U, f_ge2 = 0U, f_lt2 = 0U;
    for (std::size_t s = 0U; s < kClasses; ++s)
      for (std::size_t d = 0U; d < kDropBins; ++d) {
        const Nat b = cross_[s][1][0][d] + cross_[s][1][1][d];
        const Nat f = cross_[s][0][0][d] + cross_[s][0][1][d];
        if (d >= 2U) {
          b_ge2 += b;
          f_ge2 += f;
        } else {
          b_lt2 += b;
          f_lt2 += f;
        }
      }
    out << "  blocked & drop>=2 = " << b_ge2 << "  blocked & drop<2 = "
        << b_lt2 << "  fresh & drop>=2 = " << f_ge2 << "  fresh & drop<2 = "
        << f_lt2 << '\n';

    out << "\nblocked comb ends with drop < 3 (or undefined): count="
        << lowdrop_count_ << "; first " << kWatchFirst
        << " (arc, c, v, class, drop, test=2c+v+2, arcStart):\n";
    for (const auto& e : lowdrop_first_)
      out << "  arc=" << e[0] << " c=" << e[1] << " v=" << e[2] << " class="
          << e[3] << " drop=" << static_cast<Int>(e[4]) << " test=" << e[5]
          << " arcStart=" << e[6] << '\n';

    out << "\ndrop histogram at comb ends (defined, nonnegative; all"
           " classes):\n";
    out << "  drop total blocked fresh | continued notContinued\n";
    for (std::size_t d = 0U; d < kDropBins; ++d) {
      Nat b = 0U, f = 0U, cont = 0U, ncont = 0U;
      for (std::size_t s = 0U; s < kClasses; ++s) {
        b += cross_[s][1][0][d] + cross_[s][1][1][d];
        f += cross_[s][0][0][d] + cross_[s][0][1][d];
        cont += cross_[s][0][1][d] + cross_[s][1][1][d];
        ncont += cross_[s][0][0][d] + cross_[s][1][0][d];
      }
      if (d == 21U)
        out << "  >20 ";
      else
        out << "  " << d << ' ';
      out << b + f << ' ' << b << ' ' << f << " | " << cont << ' ' << ncont
          << '\n';
    }
    out << "  class 3 only (drop: total blocked fresh | continued"
           " notContinued):\n";
    for (std::size_t d = 0U; d < kDropBins; ++d) {
      const Nat b = cross_[3][1][0][d] + cross_[3][1][1][d];
      const Nat f = cross_[3][0][0][d] + cross_[3][0][1][d];
      const Nat cont = cross_[3][0][1][d] + cross_[3][1][1][d];
      const Nat ncont = cross_[3][0][0][d] + cross_[3][1][0][d];
      if (b + f == 0U) continue;
      if (d == 21U)
        out << "    >20 ";
      else
        out << "    " << d << ' ';
      out << b + f << ' ' << b << ' ' << f << " | " << cont << ' ' << ncont
          << '\n';
    }
    out << "  fresh & drop>=3 detail (class:drop:count, capped):";
    for (const auto& kv : fresh_drop3_)
      out << ' ' << kv.first.first << ':' << kv.first.second << ':'
          << kv.second;
    out << '\n';

    out << "\ngap to the next late landing after continued comb ends"
           " (bin b: 2^b <= gap < 2^(b+1)); rows: blocked/fresh x class\n";
    for (std::size_t b = 0U; b < 2U; ++b)
      for (std::size_t s = 0U; s < kClasses; ++s) {
        out << "  " << (b == 1U ? "blocked" : "fresh  ") << " class" << s
            << ':';
        bool any = false;
        for (std::size_t g = 0U; g < kGapBins; ++g)
          if (gap_hist_[s][b][g] != 0U) {
            out << " b" << g << '=' << gap_hist_[s][b][g];
            any = true;
          }
        if (!any) out << " -";
        out << '\n';
      }

    out << "\nPhi decreases at level-1 clocks (completed arcs and the open"
           " arc): total="
        << dec_total_ << " sizeSum=" << dec_sum_ << '\n';
    out << "  size histogram (size:count):";
    for (std::size_t s = 1U; s < kSizeBins; ++s)
      if (dec_size_hist_[s] != 0U)
        out << ' ' << (s == 21U ? std::string(">20") : std::to_string(s))
            << ':' << dec_size_hist_[s];
    out << '\n';
    out << "  height decade histogram (10^d <= h < 10^(d+1), d:count):";
    for (std::size_t d = 0U; d < kDecades; ++d)
      if (dec_height_hist_[d] != 0U)
        out << ' ' << d << ':' << dec_height_hist_[d];
    out << '\n';
    out << "  max k between the two level-1 clocks (maxk:count):";
    for (const auto& kv : dec_maxk_) out << ' ' << kv.first << ':' << kv.second;
    out << '\n';
    out << "  pattern (gap between the two level-1 clocks, max k in between,"
           " size) : count [top 40]\n";
    std::vector<std::pair<Nat, std::string>> pats;
    for (const auto& kv : dec_pattern_)
      pats.emplace_back(kv.second, "gap=" + std::to_string(kv.first[0]) +
                                       " maxk=" + std::to_string(kv.first[1]) +
                                       " size=" + std::to_string(kv.first[2]));
    std::sort(pats.begin(), pats.end(),
              [](const auto& a, const auto& b) { return a.first > b.first; });
    for (std::size_t i = 0U; i < std::min<std::size_t>(40U, pats.size()); ++i)
      out << "    " << pats[i].second << " : " << pats[i].first << '\n';
    out << "  distinct patterns=" << dec_pattern_.size();
    if (dec_pattern_overflow_ != 0U)
      out << " (pattern map overflow, uncounted: " << dec_pattern_overflow_
          << ")";
    out << '\n';
    out << "  size vs gap check: maxk=3 with size == gap/2 - 2: "
        << dec_law3_ok_ << " of " << dec_law3_all_
        << "; maxk=4 with 2*size == 3*gap - 12: " << dec_law4_ok_ << " of "
        << dec_law4_all_ << '\n';

    out << "\narc summary (completed arcs=" << landings_.size() << "):\n";
    out << "  arcs with >=1 comb end=" << arcs_with_comb_
        << " arcs with >=1 blocked comb end=" << arcs_with_blocked_
        << " arcs with >=1 drop>=3 comb end=" << arcs_with_drop3_
        << " arcs with >=1 class-3 blocked comb end=" << arcs_with_blocked_c3_
        << '\n';
    out << "  landing == first blocked comb end (clock and value): "
        << arcs_landing_eq_blocked_ << '\n';
    out << "  landing == first drop>=3 comb end: " << arcs_landing_eq_drop3_
        << '\n';
    out << "  landing == first class-3 blocked comb end: "
        << arcs_landing_eq_blocked_c3_ << " (arcs whose landing is class 3: "
        << arcs_landing_c3_ << ")\n";
    out << "  landing is a comb end: " << arcs_landing_comb_
        << "; of these blocked: " << arcs_landing_comb_blocked_ << '\n';
    out << "  landing is the last late landing: " << arcs_landing_last_late_
        << '\n';
    out << "  first blocked == first drop>=3 (same comb end): "
        << arcs_first_blocked_eq_drop3_ << '\n';

    out << "\nopen arc at horizon: ordinal=" << arc_.ordinal << " start="
        << arc_.start_clock << " minValue=" << arc_.min_value << " minClock="
        << arc_.min_clock << " lateTotal=" << arc_.late_total << " combEnds="
        << arc_.comb_ends << " blockedEnds=" << arc_.blocked_ends
        << " drop3Ends=" << arc_.drop3_ends << " combEndsC3="
        << arc_.comb_ends_c3 << " blockedEndsC3=" << arc_.blocked_ends_c3
        << " decreases=" << arc_.decreases << " phiStar=" << arc_.phi_star
        << '\n';
    if (arc_.first_blocked_c3.clock != 0U)
      out << "  first class-3 blocked comb end: " << arc_.first_blocked_c3.clock
          << '=' << arc_.first_blocked_c3.value << " drop="
          << arc_.first_blocked_c3.drop << '\n';
    if (pending_.active)
      out << "  unresolved comb end: c=" << pending_.clock << " v="
          << pending_.value << " drop=" << pending_.drop << " blocked="
          << pending_.blocked << '\n';

    std::ofstream wv(outdir_ + "/watch_values.txt");
    wv << "# test values 2c+v+2 of the first " << kWatchFirst
       << " blocked comb ends with drop < 3\n";
    for (const auto& e : lowdrop_first_) wv << e[5] << '\n';
  }

 private:
  double Elapsed() const {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() -
                                         start_)
        .count();
  }

  void Step() {
    const Nat clock = clock_;
    const Nat prev = value_;
    const bool has_cand = prev > clock;
    const Nat cand = has_cand ? prev - clock : 0U;
    const bool subtract =
        has_cand && !seen_.Contains(cand, IntervalSet::kSub);
    value_ = subtract ? cand : prev + clock;
    seen_.Insert(value_, subtract ? IntervalSet::kSub : IntervalSet::kAdd);
    const Nat k = value_ / clock;
    const Nat r = value_ - k * clock;
    const bool late = value_ < clock;

    if (verify_.active) {
      if (clock == verify_.clock + 3U) {
        ++verify3_checked_;
        if (value_ != 3U * verify_.clock + verify_.value + 6U)
          ++verify3_mismatch_;
      } else if (clock == verify_.clock + 4U) {
        ++verify4_checked_;
        if ((!subtract) != verify_.blocked) ++verify4_mismatch_;
        verify_.active = false;
      }
    }

    if (in_arc_ && r > prev_residue_) {
      FinishArc(clock);
      StartArc(clock);
    } else if (!in_arc_) {
      StartArc(clock);
    }
    prev_residue_ = r;

    if (value_ < arc_.min_value) {
      arc_.min_value = value_;
      arc_.min_clock = clock;
    }

    Nat flags = (subtract ? kFSub : 0U) | (has_cand ? kFHasCand : 0U) |
                (late ? kFLate : 0U);

    if (k == 1U) {
      OnLevel1(clock);
    } else if (k > arc_.max_k_since) {
      arc_.max_k_since = k;
    }

    if (late) {
      ++arc_.late_total;
      arc_.last_late_clock = clock;
      arc_.last_late_value = value_;
      if (pending_.active) Resolve(true, false, clock);
      // value_ >= 1: 0 is visited from the start and additions are positive.
      if (seen_.Contains(value_ - 1U, IntervalSet::kBelow)) {
        flags |= kFCombEnd;
        OnCombEnd(clock, value_);
      }
    }

    ring_[ring_pos_] = MakeRec(clock, value_, prev, flags);
    ring_pos_ = (ring_pos_ + 1U) % kRing;
    if (ring_count_ < kRing) ++ring_count_;
    if (!dumps_pending_.empty()) FlushDumps(clock);

    if (clock == next_progress_) {
      std::cerr << "progress clock=" << clock << " value=" << value_
                << " intervals=" << seen_.Count() << " arcs="
                << landings_.size() << " combEnds=" << comb_total_
                << " blocked=" << blocked_total_ << " elapsed=" << Elapsed()
                << "s\n";
      next_progress_ += kProgressStep;
    }
    clock_ = clock + 1U;
  }

  void OnLevel1(Nat clock) {
    const Nat phi = value_ + clock;
    ++arc_.level1;
    if (arc_.prev_phi_valid && phi < arc_.prev_phi) {
      const Nat size = arc_.prev_phi - phi;
      const Nat height = value_ - clock;
      const Nat gap = clock - arc_.prev_l1_clock;
      const Nat maxk = arc_.max_k_since;
      ++arc_.decreases;
      arc_.dec_sum += size;
      if (size > arc_.dec_max) arc_.dec_max = size;
      if (arc_.decreases == 1U || height < arc_.dec_hmin)
        arc_.dec_hmin = height;
      if (height > arc_.dec_hmax) arc_.dec_hmax = height;
      ++dec_total_;
      dec_sum_ += size;
      ++dec_size_hist_[SizeBin(size)];
      ++dec_height_hist_[Decade(height)];
      ++dec_maxk_[maxk];
      if (maxk == 3U) {
        ++dec_law3_all_;
        if (gap >= 4U && size == gap / 2U - 2U) ++dec_law3_ok_;
      } else if (maxk == 4U) {
        ++dec_law4_all_;
        if (3U * gap >= 12U && 2U * size == 3U * gap - 12U) ++dec_law4_ok_;
      }
      const std::array<Nat, 3> key{gap, maxk, size};
      auto it = dec_pattern_.find(key);
      if (it != dec_pattern_.end())
        ++it->second;
      else if (dec_pattern_.size() < 100000U)
        dec_pattern_.emplace(key, 1U);
      else
        ++dec_pattern_overflow_;
      if (dec_dumped_ < kGlobalDumps || arc_.dec_printed < kArcDumps) {
        ++dec_dumped_;
        ++arc_.dec_printed;
        dumps_pending_.push_back(
            Dump{clock + 3U, clock, 8U,
                 "decrease at clock " + std::to_string(clock) + " arc " +
                     std::to_string(arc_.ordinal) + " size " +
                     std::to_string(size) + " gap " + std::to_string(gap) +
                     " maxk " + std::to_string(maxk)});
      }
    }
    arc_.prev_phi = phi;
    arc_.prev_phi_valid = true;
    arc_.prev_l1_clock = clock;
    arc_.max_k_since = 0U;
    if (!arc_.phi_valid || phi > arc_.phi_star) {
      arc_.phi_star = phi;
      arc_.phi_valid = true;
    }
  }

  void OnCombEnd(Nat c, Nat v) {
    const Nat test = 2U * c + v + 2U;
    const bool blocked = seen_.Contains(test, IntervalSet::kTest);
    const bool defined = arc_.phi_valid;
    const Int drop = defined ? static_cast<Int>(arc_.phi_star) -
                                   static_cast<Int>(2U * c + v - 1U)
                             : 0;
    const std::size_t cls = DepthClass(c, v);
    const CombRef ref{c, v, drop, defined};
    ++comb_total_;
    ++arc_.comb_ends;
    if (cls == 3U) ++arc_.comb_ends_c3;
    if (blocked) {
      ++blocked_total_;
      ++arc_.blocked_ends;
      if (arc_.first_blocked.clock == 0U) arc_.first_blocked = ref;
      if (cls == 3U) {
        ++arc_.blocked_ends_c3;
        if (arc_.first_blocked_c3.clock == 0U) arc_.first_blocked_c3 = ref;
      }
      if (windows_done_[cls] < kClassWindows) {
        ++windows_done_[cls];
        dumps_pending_.push_back(
            Dump{c + 12U, c, 16U,
                 "blocked comb end c=" + std::to_string(c) + " v=" +
                     std::to_string(v) + " class " + std::to_string(cls) +
                     " drop " + (defined ? std::to_string(drop) : "undef") +
                     " arc " + std::to_string(arc_.ordinal)});
      }
    }
    if (!defined) ++arc_.undef_ends;
    if (defined && drop < 0) ++arc_.neg_ends;
    if (defined && drop > arc_.max_drop) arc_.max_drop = drop;
    if (defined && drop >= 3) {
      ++arc_.drop3_ends;
      if (arc_.first_drop3.clock == 0U) arc_.first_drop3 = ref;
    }
    arc_.last_comb = ref;
    arc_.last_comb_blocked = blocked;
    if (blocked && (!defined || drop < 3)) {
      ++lowdrop_count_;
      if (lowdrop_first_.size() < kWatchFirst)
        lowdrop_first_.push_back(std::array<Nat, 7>{
            arc_.ordinal, c, v, cls, static_cast<Nat>(drop), test,
            arc_.start_clock});
      if (lowdrop_count_ <= kLowdropCap) {
        lowdrop_ << arc_.ordinal << ' ' << c << ' ' << v << ' ' << cls << ' ';
        if (defined)
          lowdrop_ << drop;
        else
          lowdrop_ << "undef";
        lowdrop_ << ' ' << test << ' ' << arc_.phi_star << ' '
                 << arc_.start_clock << '\n';
      }
    }
    if (blocked || (defined && drop >= 3)) {
      ++marked_count_;
      if (marked_count_ <= kMarkedCap) {
        marked_ << arc_.ordinal << ' ' << c << ' ' << v << ' ' << cls << ' ';
        if (defined)
          marked_ << drop;
        else
          marked_ << "undef";
        marked_ << ' ' << (blocked ? "blocked" : "fresh") << ' ' << test << ' '
                << arc_.phi_star << '\n';
      }
    }
    pending_ = PendingComb{true, c, v, drop, defined, blocked, cls};
    verify_ = Verify{true, c, v, blocked};
  }

  void Resolve(bool continued, bool ended_early, Nat now) {
    const std::size_t s = pending_.cls;
    const std::size_t b = pending_.blocked ? 1U : 0U;
    const std::size_t ct = continued ? 1U : 0U;
    const std::size_t e = ended_early ? 1U : 0U;
    ++tab_bc_[s][b][ct][e];
    if (continued) ++gap_hist_[s][b][GapBin(now - pending_.clock)];
    if (pending_.defined && pending_.drop >= 0) {
      ++tab_bd_[s][b][pending_.drop >= 3 ? 1U : 0U];
      ++cross_[s][b][ct][DropBin(pending_.drop)];
      if (!pending_.blocked && pending_.drop >= 3) {
        const std::pair<std::size_t, Int> key{s, pending_.drop};
        auto it = fresh_drop3_.find(key);
        if (it != fresh_drop3_.end())
          ++it->second;
        else if (fresh_drop3_.size() < 200U)
          fresh_drop3_.emplace(key, 1U);
      }
    } else if (pending_.defined) {
      ++drop_neg_[b];
    } else {
      ++drop_undef_[b];
    }
    pending_.active = false;
  }

  void FlushDumps(Nat clock) {
    std::size_t w = 0U;
    for (std::size_t i = 0U; i < dumps_pending_.size(); ++i) {
      const Dump& d = dumps_pending_[i];
      if (d.at_clock != clock) {
        dumps_pending_[w++] = d;
        continue;
      }
      std::ofstream& out = d.window == 8U ? dumps_ : windows_;
      out << d.label << '\n';
      const std::size_t n = std::min(d.window, ring_count_);
      const std::size_t start = (ring_pos_ + kRing - n) % kRing;
      for (std::size_t j = 0U; j < n; ++j) {
        const Rec& rec = ring_[(start + j) % kRing];
        PrintRec(out, rec, rec.clock == d.mark_clock);
      }
      out.flush();
    }
    dumps_pending_.resize(w);
  }

  void StartArc(Nat clock) {
    in_arc_ = true;
    arc_ = Arc{};
    arc_.ordinal = landings_.size() + 1U;
    arc_.start_clock = clock;
    arc_.start_value = value_;
    arc_.min_value = value_;
    arc_.min_clock = clock;
  }

  static void PrintRef(std::ostream& out, const CombRef& ref) {
    if (ref.clock == 0U) {
      out << "none";
      return;
    }
    out << ref.clock << '=' << ref.value << ':';
    if (ref.defined)
      out << ref.drop;
    else
      out << "undef";
  }

  // The arc consists of the clocks [arc_.start_clock, wrap_clock - 1].
  void FinishArc(Nat wrap_clock) {
    const Nat end = wrap_clock - 1U;
    if (pending_.active) Resolve(false, end < pending_.clock + 4U, wrap_clock);
    const Nat index = arc_.min_clock, value = arc_.min_value;
    landings_.push_back(Landing{index, value});
    const bool landing_last_late =
        arc_.late_total != 0U && arc_.last_late_clock == index;
    const bool landing_comb =
        arc_.comb_ends != 0U && arc_.last_comb.clock == index;
    const bool eq_blocked = arc_.first_blocked.clock != 0U &&
                            arc_.first_blocked.clock == index &&
                            arc_.first_blocked.value == value;
    const bool eq_drop3 = arc_.first_drop3.clock != 0U &&
                          arc_.first_drop3.clock == index &&
                          arc_.first_drop3.value == value;
    const bool eq_blocked_c3 = arc_.first_blocked_c3.clock != 0U &&
                               arc_.first_blocked_c3.clock == index &&
                               arc_.first_blocked_c3.value == value;
    const bool landing_c3 = value * 1000U < index;
    if (arc_.comb_ends != 0U) ++arcs_with_comb_;
    if (arc_.blocked_ends != 0U) ++arcs_with_blocked_;
    if (arc_.blocked_ends_c3 != 0U) ++arcs_with_blocked_c3_;
    if (arc_.drop3_ends != 0U) ++arcs_with_drop3_;
    if (eq_blocked) ++arcs_landing_eq_blocked_;
    if (eq_drop3) ++arcs_landing_eq_drop3_;
    if (eq_blocked_c3) ++arcs_landing_eq_blocked_c3_;
    if (landing_c3) ++arcs_landing_c3_;
    if (landing_comb) ++arcs_landing_comb_;
    if (landing_comb && arc_.last_comb_blocked) ++arcs_landing_comb_blocked_;
    if (landing_last_late) ++arcs_landing_last_late_;
    if (arc_.first_blocked.clock != 0U &&
        arc_.first_blocked.clock == arc_.first_drop3.clock)
      ++arcs_first_blocked_eq_drop3_;

    arcs_ << arc_.ordinal << ' ' << arc_.start_clock << ' ' << end << ' '
          << arc_.start_value << ' ' << index << ' ' << value << ' '
          << (landing_last_late ? 'Y' : 'N') << ' ' << end - index << ' '
          << arc_.late_total << ' ' << arc_.level1 << ' ' << arc_.comb_ends
          << ' ' << arc_.blocked_ends << ' ' << arc_.drop3_ends << ' '
          << arc_.undef_ends << ' ' << arc_.neg_ends << ' '
          << arc_.comb_ends_c3 << ' ' << arc_.blocked_ends_c3 << ' ';
    PrintRef(arcs_, arc_.first_drop3);
    arcs_ << ' ';
    PrintRef(arcs_, arc_.first_blocked);
    arcs_ << ' ';
    PrintRef(arcs_, arc_.first_blocked_c3);
    arcs_ << ' ';
    if (landing_comb) {
      if (arc_.last_comb.defined)
        arcs_ << arc_.last_comb.drop;
      else
        arcs_ << "undef";
      arcs_ << ':' << (arc_.last_comb_blocked ? "blocked" : "fresh");
    } else {
      arcs_ << "notCombEnd";
    }
    arcs_ << ' ' << (eq_blocked ? 'Y' : 'N') << ' ' << (eq_drop3 ? 'Y' : 'N')
          << ' ' << (eq_blocked_c3 ? 'Y' : 'N') << ' ' << arc_.max_drop << ' '
          << arc_.decreases << ' ' << arc_.dec_sum << ' ' << arc_.dec_max
          << ' ' << arc_.dec_hmin << ' ' << arc_.dec_hmax << '\n';
    arcs_.flush();
    in_arc_ = false;
  }

  const Nat horizon_;
  const std::string outdir_;
  const std::chrono::steady_clock::time_point start_;
  std::ofstream arcs_, marked_, lowdrop_, dumps_, windows_;
  IntervalSet seen_;
  Nat clock_ = 1U;
  Nat value_ = 0U;
  bool in_arc_ = false;
  Nat prev_residue_ = 0U;
  Arc arc_;
  PendingComb pending_;
  Verify verify_;
  Nat verify3_checked_ = 0U, verify3_mismatch_ = 0U;
  Nat verify4_checked_ = 0U, verify4_mismatch_ = 0U;
  std::array<Rec, kRing> ring_{};
  std::size_t ring_pos_ = 0U, ring_count_ = 0U;
  std::vector<Dump> dumps_pending_;
  Nat dec_dumped_ = 0U;
  Nat windows_done_[kClasses] = {};
  std::vector<Landing> landings_;
  Nat comb_total_ = 0U, blocked_total_ = 0U;
  Nat marked_count_ = 0U, lowdrop_count_ = 0U;
  std::vector<std::array<Nat, 7>> lowdrop_first_;
  Nat tab_bc_[kClasses][2][2][2] = {};
  Nat tab_bd_[kClasses][2][2] = {};
  Nat cross_[kClasses][2][2][kDropBins] = {};
  Nat gap_hist_[kClasses][2][kGapBins] = {};
  Nat drop_neg_[2] = {}, drop_undef_[2] = {};
  std::map<std::pair<std::size_t, Int>, Nat> fresh_drop3_;
  Nat dec_total_ = 0U, dec_sum_ = 0U;
  Nat dec_size_hist_[kSizeBins] = {};
  Nat dec_height_hist_[kDecades] = {};
  std::map<Nat, Nat> dec_maxk_;
  std::map<std::array<Nat, 3>, Nat> dec_pattern_;
  Nat dec_pattern_overflow_ = 0U;
  Nat dec_law3_ok_ = 0U, dec_law3_all_ = 0U, dec_law4_ok_ = 0U,
      dec_law4_all_ = 0U;
  Nat arcs_with_comb_ = 0U, arcs_with_blocked_ = 0U, arcs_with_drop3_ = 0U,
      arcs_with_blocked_c3_ = 0U;
  Nat arcs_landing_eq_blocked_ = 0U, arcs_landing_eq_drop3_ = 0U,
      arcs_landing_eq_blocked_c3_ = 0U, arcs_landing_c3_ = 0U;
  Nat arcs_landing_comb_ = 0U, arcs_landing_comb_blocked_ = 0U;
  Nat arcs_landing_last_late_ = 0U, arcs_first_blocked_eq_drop3_ = 0U;
  Nat next_progress_ = kProgressStep;
};

// Watch mode: first-visit clocks of the listed values.
void RunWatch(Nat horizon, const std::string& outdir, const std::string& file) {
  std::ifstream in(file);
  if (!in) throw std::runtime_error("cannot open watch file " + file);
  std::vector<Nat> values;
  std::string line;
  while (std::getline(in, line)) {
    if (line.empty() || line[0] == '#') continue;
    values.push_back(std::stoull(line));
  }
  std::unordered_set<Nat> want(values.begin(), values.end());
  constexpr std::size_t kFilterBits = 24U;
  std::vector<std::uint64_t> filter(std::size_t{1} << (kFilterBits - 6U), 0U);
  const Nat mask = (Nat{1} << kFilterBits) - 1U;
  for (Nat v : values) filter[(v & mask) >> 6U] |= Nat{1} << (v & 63U);
  struct Hit {
    Nat clock, k, r;
    bool sub;
  };
  std::unordered_map<Nat, Hit> found;
  IntervalSet seen;
  Nat clock = 1U, value = 0U;
  const auto start = std::chrono::steady_clock::now();
  while (clock <= horizon && found.size() < want.size()) {
    const bool has_cand = value > clock;
    const Nat cand = has_cand ? value - clock : 0U;
    const bool subtract = has_cand && !seen.Contains(cand, IntervalSet::kSub);
    value = subtract ? cand : value + clock;
    seen.Insert(value, subtract ? IntervalSet::kSub : IntervalSet::kAdd);
    if (((filter[(value & mask) >> 6U] >> (value & 63U)) & 1U) != 0U &&
        want.count(value) != 0U && found.count(value) == 0U)
      found.emplace(value, Hit{clock, value / clock, value % clock, subtract});
    ++clock;
  }
  std::ofstream out(outdir + "/watch.txt");
  out << "# watch: horizon=" << horizon << " stoppedAtClock=" << clock - 1U
      << " elapsed="
      << std::chrono::duration<double>(std::chrono::steady_clock::now() - start)
             .count()
      << "s\n# value firstClock k r step\n";
  for (Nat v : values) {
    const auto it = found.find(v);
    if (it == found.end()) {
      out << v << " notFound\n";
      continue;
    }
    out << v << ' ' << it->second.clock << ' ' << it->second.k << ' '
        << it->second.r << ' ' << (it->second.sub ? 'S' : 'A') << '\n';
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc < 3)
      throw std::invalid_argument("usage: HORIZON OUTDIR [--watch FILE]");
    const Nat horizon = std::stoull(argv[1]);
    if (horizon < 10U) throw std::invalid_argument("horizon must be >= 10");
    const std::string outdir = argv[2];
    if (argc >= 5 && std::string(argv[3]) == "--watch") {
      RunWatch(horizon, outdir, argv[4]);
      return EXIT_SUCCESS;
    }
    Probe probe(horizon, outdir);
    probe.Run();
    probe.WriteSummary();
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
