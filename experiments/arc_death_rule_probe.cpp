// Arc death-rule probe of the canonical Recaman orbit.
//
// Simulator core copied from arc_potential_probe.cpp: a plain (one clock per
// iteration) run with the interval-set history, the exact step rule and
// Chaffin's arc detector.  Definitions (exact).  a(0) = 0, history {0}.  At
// clock n >= 1 the candidate is a(n-1) - n; subtract iff a(n-1) > n and the
// candidate is not in the history, else add n.  Write a(n) = k(n) n + r(n)
// with 0 <= r(n) < n.  Both step types send r to r - k, so an arc is a maximal
// stretch of clocks without a residue increase; the wrap clock starts the next
// arc.  Late landing: a(n) < n (k = 0).  Comb: consecutive late landings
// v0, v0-1, v0-2, ... two clocks apart (a late landing w with w-1 fresh is
// followed by the addition w+n+1 and the landing w-1).  Comb end: the last
// tooth, a late landing a(c) = v with v-1 visited at time c.  T = number of
// teeth, c0 = c - 2(T-1) and v0 = v + T - 1 are the comb's first landing.
//
// Forced steps after a comb end (Recaman/PopupLock.lean, LevelTwoThree.lean):
// a(c+1) = c+v+1, a(c+2) = 2c+v+3, a(c+3) = 3c+v+6, and the candidate at c+4
// is the test value 2c+v+2.  Blocked = the test value is visited at time c
// (the values visited at c+1..c+3 differ from it).  Blocked => a(c+4) =
// 4c+v+10 and the level-3/4 lock: at clock c+5+2i the orbit lands 3c+v+5-i
// (level 3, residue v-10-7i), at clock c+6+2i the candidate is 2c+v-1-3i;
// visited => addition to 4c+v+11+i (level 4, residue v-13-7i), fresh =>
// subtraction to it (the lock breaks; level 2, residue v-13-7i).  i_obs =
// number of completed pairs before the lock ends; the lock ends by "break"
// (subtraction at a clock c+6+2i), "wrap" (residue increase = arc end, at any
// clock after c), "l3blocked" (addition at a clock c+5+2i, i.e. the level-3
// value was visited) or "interrupted" (a late landing while the lock is
// active; impossible by the Lean facts, counted as a guard).
//
// Pre-landing run (J_obs, h_prev).  The run is the maximal alternation
// L1 L2 L1 L2 ... L1 ending at the clock before the comb's first landing c0,
// where a level-1 clock reached by a subtraction from a level-2 clock that
// was itself reached by an addition from a level-1 clock of the run completes
// a pair; any other level-1 clock starts a new run (its height a - clock is
// h_prev; after a late landing w this is the addition clock with height w);
// a level >= 3 clock, a late landing, or a level-2 clock not reached by an
// addition from the run breaks the run.  J_obs = completed pairs of the run
// ending at c0-1 (has_run = false when c0-1 is not a level-1 clock of a run,
// e.g. a landing straight from level 2).  With T = 1 the run's additions
// produced exactly the values 2c+v-j, j = 1..J_obs (prelanding_upper_values);
// in general they are 2c0+v0-j, which the probe verifies at time c
// (sweepOk).  candMask bit i = the lock candidate 2c+v-1-3i is visited at
// time c (i < 64).  The values visited between time c and the test clock
// c+6+2i are c+v+1 (clock c+1) and values >= 2c+v+3, and the candidates are
// < 2c+v, so the status at time c equals the status at the test clock except
// for a candidate equal to c+v+1 (flagged as candEqCV1).
//
// Predictions tested over the comb ends of the completed arcs:
// (a) break at i_pred = min{i : 3i+1 > J_obs} = floor((J_obs+2)/3);
// (b) wrap iff v < 13 + 7 i_pred (the residue v-10-7i at the level-3 clock
//     c+5+2i must be >= 3 for the step to c+6+2i not to wrap; also reported:
//     the literal 7 i_pred > v-6, and i_obs = i_wrap(v) = min{i : v < 13+7i}
//     at wraps);
// (c) not continued (no later late landing in the arc) iff wrap;
// (5) not continued iff 16 v < 7 h_prev.
//
// Outputs (OUTDIR): summary.txt, comb_ends.txt (one line per comb end),
// arcs.txt, exceptions_a.txt, fresh_end_windows.txt (the steps after the
// fresh comb ends whose arc ends without a later late landing),
// break_notcont_windows.txt, other_lock_windows.txt.
//
// Build: c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
//          experiments/arc_death_rule_probe.cpp -o /tmp/deathrule
// Run:   /tmp/deathrule HORIZON OUTDIR

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
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

constexpr Nat kFSub = 1U, kFHasCand = 2U, kFLate = 4U;
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

void PrintRec(std::ostream& out, const Rec& rec, Nat c, bool mark) {
  const Nat flags = rec.Flags();
  const Nat k = rec.value / rec.clock, r = rec.value % rec.clock;
  const bool sub = (flags & kFSub) != 0U, has_cand = (flags & kFHasCand) != 0U,
             late = (flags & kFLate) != 0U;
  out << (mark ? "* " : "  ") << rec.clock << " c+" << rec.clock - c << " a="
      << rec.value << " k=" << k << " r=" << r << ' ' << (sub ? 'S' : 'A')
      << " cand=";
  if (has_cand)
    out << rec.Prev() - rec.clock << (sub ? " fresh" : " blocked");
  else
    out << "none";
  if (late) out << " late";
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
constexpr std::size_t kWindow = 20U;
constexpr Nat kWindowCap = 100U;
constexpr std::size_t kMaskBits = 64U;
constexpr std::size_t kRatioBins = 21U;  // 0.05 wide, bin 20 = ratio >= 1
constexpr std::size_t kListCap = 10U;

enum class Outcome : unsigned char {
  kNone = 0,
  kBreak,
  kWrap,
  kL3Blocked,
  kInterrupted
};

const char* OutcomeName(Outcome o) {
  switch (o) {
    case Outcome::kBreak:
      return "break";
    case Outcome::kWrap:
      return "wrap";
    case Outcome::kL3Blocked:
      return "l3blocked";
    case Outcome::kInterrupted:
      return "interrupted";
    default:
      return "none";
  }
}

struct CombRec {
  Nat arc = 0U, c = 0U, v = 0U, teeth = 0U, c0 = 0U, v0 = 0U;
  Nat j_obs = 0U, h_prev = 0U, run_start = 0U;
  bool has_run = false, sweep_ok = false;
  bool run_start_sub = false;  // the run's first level-1 clock was a subtraction
  bool sweep_next = false;     // 2c0+v0-(J+1) visited at time c
  bool teeth_cands = false;    // T >= 2: candidates i <= T-2 all visited at c
  bool blocked = false, resolved = false, continued = false,
       ended_early = false, arc_completed = false;
  Nat gap = 0U;
  Outcome outcome = Outcome::kNone;
  Nat i_obs = 0U, r_break = 0U, k_break = 0U, end_offset = 0U;
  Nat cand_mask = 0U;  // bit i: 2c+v-1-3i visited at time c
  bool cand_cv1 = false;  // some candidate i < 64 equals c+v+1 (visited at c+1)
};

Nat IPred(Nat j) { return (j + 2U) / 3U; }
// Generalized break index: the earlier teeth's test values occupy candidates
// 0..T-2, and a run started by a subtraction adds the level-2 value
// 2c0+v0-(J+1) to the sweep.
Nat JEff(const CombRec& r) { return r.j_obs + (r.run_start_sub ? 1U : 0U); }
Nat IGen(const CombRec& r) { return r.teeth - 1U + IPred(JEff(r)); }
Nat IWrap(Nat v) { return v < 13U ? 0U : (v - 13U) / 7U + 1U; }
bool PredWrapExact(const CombRec& r) {
  return r.v < 13U + 7U * IPred(r.j_obs);
}
bool PredWrapLiteral(const CombRec& r) {  // 7 i_pred > v - 6
  return 7U * IPred(r.j_obs) + 6U > r.v;
}
Nat LowestZeroBit(Nat mask) {
  Nat i = 0U;
  while (i < kMaskBits && ((mask >> i) & 1U) != 0U) ++i;
  return i;
}
std::string MaskString(Nat mask, Nat bits) {
  std::string s;
  for (Nat i = 0U; i < bits && i < kMaskBits; ++i)
    s += ((mask >> i) & 1U) != 0U ? '1' : '0';
  return s;
}
std::size_t RatioBin(double ratio) {
  if (ratio < 0.0) return 0U;
  const double b = ratio / 0.05;
  if (b >= 20.0) return 20U;
  return static_cast<std::size_t>(b);
}

enum class RunState : unsigned char { kNone, kL1, kL2 };

struct LockState {
  bool active = false;
  Nat c = 0U, v = 0U, i = 0U;
  std::size_t idx = 0U;
};

struct CombState {
  Nat first_clock = 0U, first_value = 0U, teeth = 0U;
  Nat j = 0U, h = 0U, run_start = 0U;
  bool has_run = false, start_sub = false;
};

struct Verify {
  bool active = false;
  Nat clock = 0U, value = 0U;
  bool blocked = false;
};

struct Arc {
  Nat ordinal = 0U, start_clock = 0U, start_value = 0U;
  Nat min_value = 0U, min_clock = 0U;
  Nat late_total = 0U, comb_ends = 0U, blocked_ends = 0U;
  std::size_t first_record = 0U;
};

std::string PatternString(const std::vector<Rec>& window, Nat mark_clock) {
  std::string s;
  for (const Rec& rec : window) {
    if (!s.empty()) s += ' ';
    if (rec.clock == mark_clock) s += '*';
    s += std::to_string(rec.value / rec.clock);
    s += (rec.Flags() & kFSub) != 0U ? 'S' : 'A';
  }
  return s;
}

class Probe {
 public:
  Probe(Nat horizon, std::string outdir)
      : horizon_(horizon), outdir_(std::move(outdir)),
        start_(std::chrono::steady_clock::now()) {
    arcs_.open(outdir_ + "/arcs.txt");
    fresh_windows_.open(outdir_ + "/fresh_end_windows.txt");
    break_windows_.open(outdir_ + "/break_notcont_windows.txt");
    other_windows_.open(outdir_ + "/other_lock_windows.txt");
    if (!arcs_ || !fresh_windows_ || !break_windows_ || !other_windows_)
      throw std::runtime_error("cannot open output files");
    arcs_ << "# ordinal startClock endClock startValue landingIndex"
             " landingValue lateTotal combEnds blockedEnds\n";
    fresh_windows_ << "# steps after fresh comb ends (c, v) whose arc ends"
                      " without a later late landing; up to " << kWindow
                   << " steps, the wrap clock (first clock of the next arc)"
                      " is marked *\n";
    break_windows_ << "# steps after blocked comb ends whose lock breaks but"
                      " whose arc ends without a later late landing (cap "
                   << kWindowCap << ")\n";
    other_windows_ << "# steps after blocked comb ends whose lock ends by"
                      " l3blocked/interrupted (cap " << kWindowCap << ")\n";
  }

  void Run() {
    while (clock_ <= horizon_) Step();
  }

  void WriteOutputs() {
    WriteCombEnds();
    WriteSummary();
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

    const Nat flags = (subtract ? kFSub : 0U) | (has_cand ? kFHasCand : 0U) |
                      (late ? kFLate : 0U);
    if (window_active_ && window_.size() < kWindow)
      window_.push_back(MakeRec(clock, value_, prev, flags));

    const bool wrapped = in_arc_ && r > prev_residue_;
    if (wrapped) {
      FinishArc(clock);
      StartArc(clock);
    } else if (!in_arc_) {
      StartArc(clock);
    }

    if (lock_.active) OnLockStep(clock, subtract, k, r);

    if (value_ < arc_.min_value) {
      arc_.min_value = value_;
      arc_.min_clock = clock;
    }

    // The run state before this clock is what a late landing at this clock
    // sees (the run ends at the clock before the landing).
    const bool run_l1_before = run_state_ == RunState::kL1;
    const bool start_sub_before = run_start_sub_;
    const Nat pairs_before = run_pairs_, h_before = run_start_height_,
              start_before = run_start_clock_;

    if (late) {
      ++arc_.late_total;
      if (lock_.active)
        ResolveLock(Outcome::kInterrupted, lock_.i, prev_residue_, prev_k_,
                    clock - lock_.c);
      if (pending_active_) Resolve(true, false, clock);
      OnLate(clock, value_, run_l1_before, pairs_before, h_before,
             start_before, start_sub_before);
    }

    if (k == 1U) {
      if (subtract && run_state_ == RunState::kL2) {
        ++run_pairs_;
      } else {
        run_pairs_ = 0U;
        run_start_clock_ = clock;
        run_start_height_ = value_ - clock;
        run_start_sub_ = subtract;
      }
      run_state_ = RunState::kL1;
    } else if (k == 2U && !subtract && run_state_ == RunState::kL1) {
      run_state_ = RunState::kL2;
    } else {
      run_state_ = RunState::kNone;
    }

    prev_residue_ = r;
    prev_k_ = k;

    if (clock == next_progress_) {
      std::cerr << "progress clock=" << clock << " value=" << value_
                << " intervals=" << seen_.Count() << " arcs="
                << landings_.size() << " combEnds=" << records_.size()
                << " blocked=" << blocked_total_ << " elapsed=" << Elapsed()
                << "s\n";
      next_progress_ += kProgressStep;
    }
    clock_ = clock + 1U;
  }

  void OnLate(Nat n, Nat v, bool has_run, Nat pairs, Nat h, Nat run_start,
              bool start_sub) {
    const bool cont = n >= 2U && last_late_clock_ == n - 2U &&
                      last_late_value_ == v + 1U;
    if (cont) {
      ++comb_.teeth;
    } else {
      comb_ = CombState{n, v, 1U, pairs, h, run_start, has_run, start_sub};
    }
    last_late_clock_ = n;
    last_late_value_ = v;
    // v >= 1: 0 is visited from the start and additions are positive.
    if (seen_.Contains(v - 1U, IntervalSet::kBelow)) OnCombEnd(n, v);
  }

  void OnCombEnd(Nat c, Nat v) {
    CombRec rec;
    rec.arc = arc_.ordinal;
    rec.c = c;
    rec.v = v;
    rec.teeth = comb_.teeth;
    rec.c0 = comb_.first_clock;
    rec.v0 = comb_.first_value;
    rec.j_obs = comb_.j;
    rec.h_prev = comb_.h;
    rec.run_start = comb_.run_start;
    rec.has_run = comb_.has_run;
    rec.run_start_sub = comb_.start_sub;
    const Nat test = 2U * c + v + 2U;
    rec.blocked = seen_.Contains(test, IntervalSet::kTest);
    const Nat base = 2U * c + v;  // candidates base - 1 - 3i
    for (Nat i = 0U; i < kMaskBits; ++i) {
      if (base < 1U + 3U * i) break;
      const Nat cand = base - 1U - 3U * i;
      if (cand == c + v + 1U) rec.cand_cv1 = true;
      if (seen_.Contains(cand, IntervalSet::kTest)) rec.cand_mask |= Nat{1} << i;
    }
    bool sweep_ok = rec.has_run;
    const Nat jmax = std::min<Nat>(rec.j_obs, kMaskBits);
    const Nat sweep_base = 2U * rec.c0 + rec.v0;
    for (Nat j = 1U; sweep_ok && j <= jmax; ++j)
      if (sweep_base < j || !seen_.Contains(sweep_base - j, IntervalSet::kTest))
        sweep_ok = false;
    rec.sweep_ok = sweep_ok;
    rec.sweep_next = sweep_base >= rec.j_obs + 1U &&
                     seen_.Contains(sweep_base - rec.j_obs - 1U,
                                    IntervalSet::kTest);
    if (rec.teeth >= 2U) {
      const Nat need = std::min<Nat>(rec.teeth - 1U, kMaskBits);
      const Nat want = need >= kMaskBits ? ~Nat{0} : (Nat{1} << need) - 1U;
      rec.teeth_cands = (rec.cand_mask & want) == want;
    }

    ++arc_.comb_ends;
    if (rec.blocked) {
      ++blocked_total_;
      ++arc_.blocked_ends;
    }
    records_.push_back(rec);
    pending_index_ = records_.size() - 1U;
    pending_active_ = true;
    window_.clear();
    window_active_ = true;
    verify_ = Verify{true, c, v, rec.blocked};
    if (rec.blocked) {
      if (lock_.active)  // cannot happen: a late landing resolves it first
        ResolveLock(Outcome::kInterrupted, lock_.i, prev_residue_, prev_k_, 0U);
      lock_ = LockState{true, c, v, 0U, pending_index_};
    }
  }

  void OnLockStep(Nat clock, bool subtract, Nat k, Nat r) {
    const Nat off = clock - lock_.c;
    if (off <= 3U) return;
    if (off == 4U) {
      if (subtract) ++lock_mismatch4_;
      return;
    }
    if ((off - 5U) % 2U == 0U) {
      const Nat i = (off - 5U) / 2U;
      if (i != lock_.i) ++lock_index_mismatch_;
      if (!subtract) {
        ResolveLock(Outcome::kL3Blocked, i, r, k, off);
        return;
      }
      if (value_ != 3U * lock_.c + lock_.v + 5U - i) ++lock_value_mismatch_;
      if (k != 3U) ++lock_level3_mismatch_;
    } else {
      const Nat i = (off - 6U) / 2U;
      if (!subtract) {
        lock_.i = i + 1U;
        if (k != 4U) ++lock_level4_mismatch_;
        return;
      }
      ResolveLock(Outcome::kBreak, i, r, k, off);
    }
  }

  void ResolveLock(Outcome o, Nat i, Nat r, Nat k, Nat end_offset) {
    CombRec& rec = records_[lock_.idx];
    rec.outcome = o;
    rec.i_obs = i;
    rec.r_break = r;
    rec.k_break = k;
    rec.end_offset = end_offset;
    lock_.active = false;
  }

  void DumpWindow(std::ofstream& out, const CombRec& rec, const char* label) {
    out << label << ": arc=" << rec.arc << " c=" << rec.c << " v=" << rec.v
        << " T=" << rec.teeth << " J=" << rec.j_obs << " hPrev=" << rec.h_prev
        << " blocked=" << rec.blocked << " outcome=" << OutcomeName(rec.outcome)
        << " iObs=" << rec.i_obs << " continued=" << rec.continued
        << " gap(wrap or next late)=" << rec.gap << '\n';
    const Nat mark = rec.continued ? 0U : rec.c + rec.gap;
    out << "  pattern(k,step): " << PatternString(window_, mark) << '\n';
    for (const Rec& r : window_) PrintRec(out, r, rec.c, r.clock == mark);
    out.flush();
  }

  void Resolve(bool continued, bool ended_early, Nat now) {
    CombRec& rec = records_[pending_index_];
    rec.resolved = true;
    rec.continued = continued;
    rec.ended_early = ended_early;
    rec.gap = now - rec.c;
    if (!rec.blocked && !continued) {
      DumpWindow(fresh_windows_, rec, "fresh comb end, arc ends");
    } else if (rec.blocked && rec.outcome == Outcome::kBreak && !continued &&
               break_dumped_ < kWindowCap) {
      ++break_dumped_;
      DumpWindow(break_windows_, rec, "blocked comb end, break, arc ends");
    } else if (rec.blocked && rec.outcome != Outcome::kBreak &&
               rec.outcome != Outcome::kWrap && other_dumped_ < kWindowCap) {
      ++other_dumped_;
      DumpWindow(other_windows_, rec, "blocked comb end, other lock end");
    }
    pending_active_ = false;
    window_active_ = false;
  }

  void StartArc(Nat clock) {
    in_arc_ = true;
    arc_ = Arc{};
    arc_.ordinal = landings_.size() + 1U;
    arc_.start_clock = clock;
    arc_.start_value = value_;
    arc_.min_value = value_;
    arc_.min_clock = clock;
    arc_.first_record = records_.size();
  }

  // The arc consists of the clocks [arc_.start_clock, wrap_clock - 1].
  void FinishArc(Nat wrap_clock) {
    const Nat end = wrap_clock - 1U;
    if (lock_.active)
      ResolveLock(Outcome::kWrap, lock_.i, prev_residue_, prev_k_,
                  wrap_clock - lock_.c);
    if (pending_active_)
      Resolve(false, end < records_[pending_index_].c + 4U, wrap_clock);
    landings_.push_back(Landing{arc_.min_clock, arc_.min_value});
    for (std::size_t i = arc_.first_record; i < records_.size(); ++i)
      records_[i].arc_completed = true;
    arcs_ << arc_.ordinal << ' ' << arc_.start_clock << ' ' << end << ' '
          << arc_.start_value << ' ' << arc_.min_clock << ' ' << arc_.min_value
          << ' ' << arc_.late_total << ' ' << arc_.comb_ends << ' '
          << arc_.blocked_ends << '\n';
    in_arc_ = false;
  }

  void WriteCombEnds() const {
    std::ofstream out(outdir_ + "/comb_ends.txt");
    out << "# arc c v T c0 v0 hasRun J hPrev runStart sweepOk blocked"
           " outcome iObs rBreak kBreak endOffset continued gap endedEarly"
           " arcCompleted iPred iWrap candMask(first 24 bits, 1=visited)"
           " candEqCV1 runStartSub sweepNext teethCands jEff iGen\n";
    for (const CombRec& r : records_) {
      out << r.arc << ' ' << r.c << ' ' << r.v << ' ' << r.teeth << ' '
          << r.c0 << ' ' << r.v0 << ' ' << r.has_run << ' ' << r.j_obs << ' '
          << r.h_prev << ' ' << r.run_start << ' ' << r.sweep_ok << ' '
          << r.blocked << ' ' << OutcomeName(r.outcome) << ' ' << r.i_obs
          << ' ' << r.r_break << ' ' << r.k_break << ' ' << r.end_offset << ' '
          << r.continued << ' ' << r.gap << ' ' << r.ended_early << ' '
          << r.arc_completed << ' ' << IPred(r.j_obs) << ' ' << IWrap(r.v)
          << ' ' << MaskString(r.cand_mask, 24U) << ' ' << r.cand_cv1 << ' '
          << r.run_start_sub << ' ' << r.sweep_next << ' ' << r.teeth_cands
          << ' ' << JEff(r) << ' ' << IGen(r) << '\n';
    }
  }

  static void PrintRecLine(std::ostream& out, const CombRec& r) {
    out << "    arc=" << r.arc << " c=" << r.c << " v=" << r.v << " T="
        << r.teeth << " c0=" << r.c0 << " v0=" << r.v0 << " hasRun="
        << r.has_run << " J=" << r.j_obs << " hPrev=" << r.h_prev
        << " sweepOk=" << r.sweep_ok << " blocked=" << r.blocked
        << " outcome=" << OutcomeName(r.outcome) << " iObs=" << r.i_obs
        << " iPred=" << IPred(r.j_obs) << " iWrap=" << IWrap(r.v)
        << " rBreak=" << r.r_break << " kBreak=" << r.k_break
        << " endOffset=" << r.end_offset << " continued=" << r.continued
        << " gap=" << r.gap << " mask="
        << MaskString(r.cand_mask,
                      std::max<Nat>(std::max({r.i_obs, IPred(r.j_obs),
                                              IGen(r)}) + 3U, 8U))
        << " candEqCV1=" << r.cand_cv1 << " runStartSub=" << r.run_start_sub
        << " sweepNext=" << r.sweep_next << " teethCands=" << r.teeth_cands
        << " jEff=" << JEff(r) << " iGen=" << IGen(r) << '\n';
  }

  void WriteSummary() {
    std::ofstream out(outdir_ + "/summary.txt");
    out << "arc-death-rule-probe horizon=" << horizon_ << " elapsed="
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
    out << "lock checks: step c+4 not addition=" << lock_mismatch4_
        << " pairIndexMismatch=" << lock_index_mismatch_
        << " level3ValueMismatch=" << lock_value_mismatch_
        << " level3LevelMismatch=" << lock_level3_mismatch_
        << " level4LevelMismatch=" << lock_level4_mismatch_ << '\n';

    // Completed-arc records only.
    std::vector<const CombRec*> recs;
    Nat open_arc_ends = 0U, unresolved = 0U;
    for (const CombRec& r : records_) {
      if (!r.arc_completed) {
        ++open_arc_ends;
        continue;
      }
      if (!r.resolved) ++unresolved;
      recs.push_back(&r);
    }
    out << "\ncomb ends total=" << records_.size() << " inCompletedArcs="
        << recs.size() << " inOpenArc=" << open_arc_ends
        << " unresolved(inCompletedArcs, must be 0)=" << unresolved << '\n';

    Nat blocked = 0U, fresh = 0U, cont_b = 0U, cont_f = 0U, no_run = 0U,
        sweep_bad = 0U, cv1 = 0U, ended_early = 0U;
    std::map<Nat, std::array<Nat, 2>> teeth_hist;  // T -> {fresh, blocked}
    std::map<Nat, std::array<Nat, 2>> j_hist;      // J -> {fresh, blocked}
    std::map<Nat, Nat> iobs_hist_break, iobs_hist_wrap;
    Nat outcome_count[5] = {};
    for (const CombRec* r : recs) {
      if (r->blocked) {
        ++blocked;
        if (r->continued) ++cont_b;
        ++outcome_count[static_cast<std::size_t>(r->outcome)];
        if (r->outcome == Outcome::kBreak) ++iobs_hist_break[r->i_obs];
        if (r->outcome == Outcome::kWrap) ++iobs_hist_wrap[r->i_obs];
      } else {
        ++fresh;
        if (r->continued) ++cont_f;
      }
      if (!r->has_run) ++no_run;
      if (r->has_run && !r->sweep_ok) ++sweep_bad;
      if (r->cand_cv1) ++cv1;
      if (r->ended_early) ++ended_early;
      ++teeth_hist[r->teeth][r->blocked ? 1U : 0U];
      ++j_hist[r->j_obs][r->blocked ? 1U : 0U];
    }
    out << "blocked=" << blocked << " fresh=" << fresh << " continued(blocked)="
        << cont_b << " notContinued(blocked)=" << blocked - cont_b
        << " continued(fresh)=" << cont_f << " notContinued(fresh)="
        << fresh - cont_f << '\n';
    out << "hasRun=false (J/hPrev undefined)=" << no_run
        << " sweepCheckFailed(hasRun, some 2c0+v0-j, j<=J, not visited at c)="
        << sweep_bad << " candidateEqualsC+v+1(mask may be stale)=" << cv1
        << " endedEarly(arc ends before c+4)=" << ended_early << '\n';
    out << "teeth T (T:fresh/blocked):";
    for (const auto& kv : teeth_hist)
      out << ' ' << kv.first << ':' << kv.second[0] << '/' << kv.second[1];
    out << '\n';
    out << "J_obs (J:fresh/blocked):";
    for (const auto& kv : j_hist)
      out << ' ' << kv.first << ':' << kv.second[0] << '/' << kv.second[1];
    out << '\n';
    out << "lock outcomes (blocked comb ends): break=" << outcome_count[1]
        << " wrap=" << outcome_count[2] << " l3blocked=" << outcome_count[3]
        << " interrupted=" << outcome_count[4] << " none=" << outcome_count[0]
        << '\n';
    out << "i_obs at breaks (i:count):";
    for (const auto& kv : iobs_hist_break) out << ' ' << kv.first << ':' << kv.second;
    out << '\n';
    out << "i_obs at wraps (i:count):";
    for (const auto& kv : iobs_hist_wrap) out << ' ' << kv.first << ':' << kv.second;
    out << '\n';

    // (a) break pair index prediction.
    out << "\n(a) breaks: i_obs == i_pred = floor((J_obs+2)/3)\n";
    Nat a_ok = 0U, a_all = 0U, a_ok_t1 = 0U, a_all_t1 = 0U, a_gt = 0U,
        a_lt = 0U, a_mask_ok = 0U, a_mask_all = 0U, a_res_ok = 0U, a_k2 = 0U;
    Nat a_ok_norun = 0U, a_all_norun = 0U;
    std::vector<const CombRec*> a_exc;
    std::ofstream exc(outdir_ + "/exceptions_a.txt");
    exc << "# all breaks with i_obs != floor((J_obs+2)/3); see summary.txt"
           " for the field meanings\n";
    for (const CombRec* r : recs) {
      if (!r->blocked || r->outcome != Outcome::kBreak) continue;
      ++a_all;
      const Nat ip = IPred(r->j_obs);
      const bool hit = r->i_obs == ip;
      if (hit) ++a_ok;
      if (r->teeth == 1U) {
        ++a_all_t1;
        if (hit) ++a_ok_t1;
      }
      if (!r->has_run) {
        ++a_all_norun;
        if (hit) ++a_ok_norun;
      }
      if (!hit) {
        if (r->i_obs > ip) ++a_gt;
        else ++a_lt;
        a_exc.push_back(r);
        PrintRecLine(exc, *r);
      }
      if (r->i_obs < kMaskBits) {
        ++a_mask_all;
        if (LowestZeroBit(r->cand_mask) == r->i_obs) ++a_mask_ok;
      }
      if (r->v >= 13U + 7U * r->i_obs && r->r_break == r->v - 13U - 7U * r->i_obs)
        ++a_res_ok;
      if (r->k_break == 2U) ++a_k2;
    }
    out << "  holds for " << a_ok << " of " << a_all << " breaks; T=1 only: "
        << a_ok_t1 << " of " << a_all_t1 << "; T>=2: " << a_ok - a_ok_t1
        << " of " << a_all - a_all_t1 << "; hasRun=false: " << a_ok_norun
        << " of " << a_all_norun << '\n';
    out << "  exceptions: i_obs > i_pred (extra blocked candidates)=" << a_gt
        << ", i_obs < i_pred (a predicted-blocked candidate was fresh)="
        << a_lt << '\n';
    out << "  mask consistency (i_obs == lowest fresh candidate index at time"
           " c): " << a_mask_ok << " of " << a_mask_all << '\n';
    out << "  residue at break == v-13-7*i_obs: " << a_res_ok << " of " << a_all
        << "; level at break == 2: " << a_k2 << " of " << a_all << '\n';
    out << "  first " << kListCap << " exceptions:\n";
    for (std::size_t i = 0U; i < std::min(a_exc.size(), kListCap); ++i)
      PrintRecLine(out, *a_exc[i]);

    // (a-gen) generalized break index.
    Nat g_ok = 0U, g_all = 0U, g_gt = 0U, g_lt = 0U, g_ok_t1 = 0U,
        g_all_t1 = 0U;
    std::vector<const CombRec*> g_exc;
    for (const CombRec* r : recs) {
      if (!r->blocked || r->outcome != Outcome::kBreak) continue;
      ++g_all;
      const Nat ig = IGen(*r);
      const bool hit = r->i_obs == ig;
      if (hit) ++g_ok;
      if (r->teeth == 1U) {
        ++g_all_t1;
        if (hit) ++g_ok_t1;
      }
      if (!hit) {
        if (r->i_obs > ig) ++g_gt;
        else ++g_lt;
        g_exc.push_back(r);
      }
    }
    out << "(a-gen) breaks: i_obs == i_gen = (T-1) + floor((J_eff+2)/3),"
           " J_eff = J_obs + [run start was a subtraction]: " << g_ok
        << " of " << g_all << "; T=1 only: " << g_ok_t1 << " of " << g_all_t1
        << "; i_obs > i_gen=" << g_gt << " i_obs < i_gen=" << g_lt << '\n';
    out << "  first " << kListCap << " exceptions:\n";
    for (std::size_t i = 0U; i < std::min(g_exc.size(), kListCap); ++i)
      PrintRecLine(out, *g_exc[i]);
    Nat sn_match = 0U, sn_all = 0U, tc_ok = 0U, tc_all = 0U, rss = 0U;
    for (const CombRec* r : recs) {
      if (r->has_run) {
        ++sn_all;
        if (r->sweep_next == r->run_start_sub) ++sn_match;
        if (r->run_start_sub) ++rss;
      }
      if (r->teeth >= 2U) {
        ++tc_all;
        if (r->teeth_cands) ++tc_ok;
      }
    }
    out << "  run start by subtraction: " << rss << " of " << sn_all
        << " (hasRun); 2c0+v0-(J+1) visited at c <=> run start by"
           " subtraction: " << sn_match << " of " << sn_all << '\n';
    out << "  T >= 2: candidates i <= T-2 (the earlier teeth's test values"
           " 2c_t+v_t+2) all visited at c: " << tc_ok << " of " << tc_all
        << '\n';

    // (a') wraps: i_obs == i_wrap(v).
    Nat w_ok = 0U, w_all = 0U;
    std::vector<const CombRec*> w_exc;
    for (const CombRec* r : recs) {
      if (!r->blocked || r->outcome != Outcome::kWrap) continue;
      ++w_all;
      if (r->i_obs == IWrap(r->v)) ++w_ok;
      else w_exc.push_back(r);
    }
    out << "(a') wraps: i_obs == i_wrap(v) = min{i : v < 13+7i}: " << w_ok
        << " of " << w_all << '\n';
    for (std::size_t i = 0U; i < std::min(w_exc.size(), kListCap); ++i)
      PrintRecLine(out, *w_exc[i]);

    // (b) wrap prediction.
    out << "\n(b) blocked comb ends: wrap vs predicted wrap\n";
    out << "  exact: predicted wrap iff v < 13 + 7*i_pred (i_pred ="
           " floor((J_obs+2)/3)); rows observed, columns predicted\n";
    Nat b_tab[2][2] = {}, b_lit[2][2] = {}, b_other = 0U;
    std::vector<const CombRec*> b_exc, b_exc_lit;
    for (const CombRec* r : recs) {
      if (!r->blocked) continue;
      if (r->outcome != Outcome::kBreak && r->outcome != Outcome::kWrap) {
        ++b_other;
        continue;
      }
      const std::size_t obs = r->outcome == Outcome::kWrap ? 1U : 0U;
      const std::size_t pe = PredWrapExact(*r) ? 1U : 0U;
      const std::size_t pl = PredWrapLiteral(*r) ? 1U : 0U;
      ++b_tab[obs][pe];
      ++b_lit[obs][pl];
      if (obs != pe) b_exc.push_back(r);
      if (obs != pl) b_exc_lit.push_back(r);
    }
    out << "    wrap  & predWrap=" << b_tab[1][1] << "  wrap  & predBreak="
        << b_tab[1][0] << "\n    break & predWrap=" << b_tab[0][1]
        << "  break & predBreak=" << b_tab[0][0] << "  (other outcomes: "
        << b_other << ")\n";
    out << "  literal: predicted wrap iff 7*i_pred > v - 6\n";
    out << "    wrap  & predWrap=" << b_lit[1][1] << "  wrap  & predBreak="
        << b_lit[1][0] << "\n    break & predWrap=" << b_lit[0][1]
        << "  break & predBreak=" << b_lit[0][0] << '\n';
    out << "  first " << kListCap << " exceptions to the exact form:\n";
    for (std::size_t i = 0U; i < std::min(b_exc.size(), kListCap); ++i)
      PrintRecLine(out, *b_exc[i]);
    out << "  first " << kListCap << " exceptions to the literal form:\n";
    for (std::size_t i = 0U; i < std::min(b_exc_lit.size(), kListCap); ++i)
      PrintRecLine(out, *b_exc_lit[i]);

    Nat bg_tab[2][2] = {};
    for (const CombRec* r : recs) {
      if (!r->blocked) continue;
      if (r->outcome != Outcome::kBreak && r->outcome != Outcome::kWrap)
        continue;
      const std::size_t obs = r->outcome == Outcome::kWrap ? 1U : 0U;
      const std::size_t pg = r->v < 13U + 7U * IGen(*r) ? 1U : 0U;
      ++bg_tab[obs][pg];
    }
    out << "  generalized: predicted wrap iff v < 13 + 7*i_gen\n";
    out << "    wrap  & predWrap=" << bg_tab[1][1] << "  wrap  & predBreak="
        << bg_tab[1][0] << "\n    break & predWrap=" << bg_tab[0][1]
        << "  break & predBreak=" << bg_tab[0][0] << '\n';

    // (b'') wrap vs the mask-based break index (uses the observed candidate
    // status instead of J_obs).
    Nat bm_tab[2][2] = {};
    for (const CombRec* r : recs) {
      if (!r->blocked) continue;
      if (r->outcome != Outcome::kBreak && r->outcome != Outcome::kWrap)
        continue;
      const std::size_t obs = r->outcome == Outcome::kWrap ? 1U : 0U;
      const Nat ib = LowestZeroBit(r->cand_mask);
      const std::size_t pm = r->v < 13U + 7U * ib ? 1U : 0U;
      ++bm_tab[obs][pm];
    }
    out << "  mask form: predicted wrap iff v < 13 + 7*i_mask (i_mask ="
           " lowest fresh candidate index at time c)\n";
    out << "    wrap  & predWrap=" << bm_tab[1][1] << "  wrap  & predBreak="
        << bm_tab[1][0] << "\n    break & predWrap=" << bm_tab[0][1]
        << "  break & predBreak=" << bm_tab[0][0] << '\n';

    // (c) death rule.
    out << "\n(c) blocked comb ends: arc ends here (not continued) iff wrap\n";
    Nat c_tab[2][2] = {};  // [notContinued][wrap]
    Nat c_other[2] = {};
    std::vector<const CombRec*> c_exc;
    for (const CombRec* r : recs) {
      if (!r->blocked) continue;
      const std::size_t nc = r->continued ? 0U : 1U;
      if (r->outcome != Outcome::kBreak && r->outcome != Outcome::kWrap) {
        ++c_other[nc];
        continue;
      }
      const std::size_t w = r->outcome == Outcome::kWrap ? 1U : 0U;
      ++c_tab[nc][w];
      if (nc != w) c_exc.push_back(r);
    }
    out << "    notContinued & wrap=" << c_tab[1][1]
        << "  notContinued & break=" << c_tab[1][0]
        << "\n    continued    & wrap=" << c_tab[0][1]
        << "  continued    & break=" << c_tab[0][0]
        << "  (other outcomes: notContinued=" << c_other[1] << " continued="
        << c_other[0] << ")\n";
    out << "  first " << kListCap << " exceptions (break & not continued, or"
           " wrap & continued):\n";
    for (std::size_t i = 0U; i < std::min(c_exc.size(), kListCap); ++i)
      PrintRecLine(out, *c_exc[i]);
    out << "  gap (clock of the arc end minus c) for break & not continued:";
    for (const CombRec* r : c_exc)
      if (!r->continued) out << ' ' << r->gap;
    out << '\n';
    out << "  fresh comb ends: continued=" << cont_f << " notContinued="
        << fresh - cont_f << "; the not-continued ones (c, v, T, J, hPrev,"
           " gap to the arc end, endedEarly):\n";
    for (const CombRec* r : recs)
      if (!r->blocked && !r->continued)
        out << "    arc=" << r->arc << " c=" << r->c << " v=" << r->v << " T="
            << r->teeth << " J=" << r->j_obs << " hPrev=" << r->h_prev
            << " gap=" << r->gap << " endedEarly=" << r->ended_early << '\n';
    out << "  (their step windows are in fresh_end_windows.txt)\n";

    // (5) ratio v / h_prev.
    out << "\n(5) ratio v/hPrev at comb ends (hasRun only; bins of 0.05,"
           " bin 20 = ratio >= 1)\n";
    Nat hist_all[2][kRatioBins] = {}, hist_blk[2][kRatioBins] = {};
    Nat r_tab[2][2] = {};  // blocked: [notContinued][16v < 7h]
    Nat r_tab_all[2][2] = {};
    Nat h_zero = 0U;
    std::vector<const CombRec*> r_exc;
    for (const CombRec* r : recs) {
      if (!r->has_run) continue;
      if (r->h_prev == 0U) {
        ++h_zero;
        continue;
      }
      const double ratio = static_cast<double>(r->v) /
                           static_cast<double>(r->h_prev);
      const std::size_t bin = RatioBin(ratio);
      const std::size_t ct = r->continued ? 1U : 0U;
      ++hist_all[ct][bin];
      const std::size_t nc = r->continued ? 0U : 1U;
      const std::size_t lo = 16U * r->v < 7U * r->h_prev ? 1U : 0U;
      ++r_tab_all[nc][lo];
      if (r->blocked) {
        ++hist_blk[ct][bin];
        ++r_tab[nc][lo];
        if (nc != lo) r_exc.push_back(r);
      }
    }
    out << "  hPrev=0 skipped: " << h_zero << '\n';
    out << "  bin lo hi | all: continued notContinued | blocked: continued"
           " notContinued\n";
    for (std::size_t b = 0U; b < kRatioBins; ++b) {
      if (hist_all[0][b] + hist_all[1][b] == 0U) continue;
      out << "  " << b << ' ' << std::fixed << std::setprecision(2)
          << 0.05 * static_cast<double>(b) << ' ';
      if (b == 20U)
        out << "inf";
      else
        out << 0.05 * static_cast<double>(b + 1U);
      out << " | " << hist_all[1][b] << ' ' << hist_all[0][b] << " | "
          << hist_blk[1][b] << ' ' << hist_blk[0][b] << '\n';
    }
    out << "  blocked: notContinued vs 16v < 7hPrev (rows observed, columns"
           " rule)\n";
    out << "    notContinued & v<(7/16)h=" << r_tab[1][1]
        << "  notContinued & v>=(7/16)h=" << r_tab[1][0]
        << "\n    continued    & v<(7/16)h=" << r_tab[0][1]
        << "  continued    & v>=(7/16)h=" << r_tab[0][0] << '\n';
    out << "  all comb ends (hasRun): notContinued & v<(7/16)h="
        << r_tab_all[1][1] << "  notContinued & v>=(7/16)h=" << r_tab_all[1][0]
        << "  continued & v<(7/16)h=" << r_tab_all[0][1]
        << "  continued & v>=(7/16)h=" << r_tab_all[0][0] << '\n';
    out << "  first " << kListCap << " blocked disagreements:\n";
    for (std::size_t i = 0U; i < std::min(r_exc.size(), kListCap); ++i)
      PrintRecLine(out, *r_exc[i]);
    // Identity check hPrev == v0 + 1 + 3 J (run start height for T teeth).
    Nat id_ok = 0U, id_all = 0U;
    for (const CombRec* r : recs) {
      if (!r->has_run) continue;
      ++id_all;
      if (r->h_prev == r->v0 + 1U + 3U * r->j_obs) ++id_ok;
    }
    out << "  identity hPrev == v0 + 1 + 3*J_obs (v0 = v + T - 1): " << id_ok
        << " of " << id_all << '\n';

    out << "\nopen arc at horizon: ordinal=" << arc_.ordinal << " start="
        << arc_.start_clock << " minValue=" << arc_.min_value << " minClock="
        << arc_.min_clock << " lateTotal=" << arc_.late_total << " combEnds="
        << arc_.comb_ends << " blockedEnds=" << arc_.blocked_ends << '\n';
    if (pending_active_)
      out << "  unresolved comb end: c=" << records_[pending_index_].c
          << " v=" << records_[pending_index_].v << " blocked="
          << records_[pending_index_].blocked << '\n';
    if (lock_.active)
      out << "  lock still active: c=" << lock_.c << " v=" << lock_.v << " i="
          << lock_.i << '\n';
  }

  const Nat horizon_;
  const std::string outdir_;
  const std::chrono::steady_clock::time_point start_;
  std::ofstream arcs_, fresh_windows_, break_windows_, other_windows_;
  IntervalSet seen_;
  Nat clock_ = 1U;
  Nat value_ = 0U;
  bool in_arc_ = false;
  Nat prev_residue_ = 0U, prev_k_ = 0U;
  Arc arc_;
  Verify verify_;
  Nat verify3_checked_ = 0U, verify3_mismatch_ = 0U;
  Nat verify4_checked_ = 0U, verify4_mismatch_ = 0U;
  Nat lock_mismatch4_ = 0U, lock_index_mismatch_ = 0U,
      lock_value_mismatch_ = 0U, lock_level3_mismatch_ = 0U,
      lock_level4_mismatch_ = 0U;
  RunState run_state_ = RunState::kNone;
  Nat run_pairs_ = 0U, run_start_clock_ = 0U, run_start_height_ = 0U;
  bool run_start_sub_ = false;
  Nat last_late_clock_ = 0U, last_late_value_ = 0U;
  CombState comb_;
  LockState lock_;
  std::vector<CombRec> records_;
  std::size_t pending_index_ = 0U;
  bool pending_active_ = false;
  std::vector<Rec> window_;
  bool window_active_ = false;
  Nat break_dumped_ = 0U, other_dumped_ = 0U;
  std::vector<Landing> landings_;
  Nat blocked_total_ = 0U;
  Nat next_progress_ = kProgressStep;
};

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc < 3) throw std::invalid_argument("usage: HORIZON OUTDIR");
    const Nat horizon = std::stoull(argv[1]);
    if (horizon < 10U) throw std::invalid_argument("horizon must be >= 10");
    Probe probe(horizon, argv[2]);
    probe.Run();
    probe.WriteOutputs();
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
