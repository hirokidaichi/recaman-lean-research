// Blocker provenance probe of the canonical Recaman orbit (H-20260903-01).
//
// Two passes over the same horizon.  Pass 1 is the death-rule probe's
// simulator (experiments/arc_death_rule_probe.cpp: the interval-set history,
// the exact step rule, Chaffin's arc detector, comb / comb-end detection and
// the level-3/4 lock analysis, copied with the definitions unchanged) and
// emits one query record per value that blocks the descent:
//   test     blocked comb end (c, v): w = 2c+v+2, visited at time c;
//   lockcand a lock that breaks with i_obs > i_gen: w = 2c+v-1-3 i_gen, the
//            first level-2 candidate the generalized rule predicted fresh but
//            that was visited when it was presented (clock c+6+2 i_gen);
//   l3       a lock that ends by l3blocked: w = 3c+v+5-i_obs, the level-3
//            value that was already visited (addition at clock c+5+2 i_obs);
//   entry23  a fresh comb end whose candidate c+v-3 at clock c+5 is visited
//            (the step at c+5 is an addition, the level-2/3 ping-pong
//            starts): w = c+v-3;
//   bandexit a level-1 clock n (n <= a(n) < 2n, height h = a(n)-n with
//            2 <= h <= 10^7) followed by two additions: h-1 was visited so
//            a(n+1) = 2n+h+1, and the band value a(n)-1 (the candidate at
//            n+2) was visited so the orbit leaves the level-1/2 chain
//            upward: w = a(n)-1, c = n, v = h.  Decimated to at most 400,000
//            records (every k-th exit, k a power of two; k is reported).
// Pass 2 reruns the orbit from clock 0 with the set of queried values in an
// open-addressing hash table (behind a one-bit filter) and records the first
// visit of each value w: clock n with a(n) = w, step type, level q = w / n,
// residue w % n, arc index and arc start clock, the neighbours a(n-2),
// a(n-1), a(n+1), a(n+2) and the run flags upperRun = (a(n+2) == w+1 ||
// a(n-2) == w-1), lowerRun = (a(n+2) == w-1 || a(n-2) == w+1).  The passes
// are joined by w (each query keeps its own record, joined with the single
// first-visit record of its value).
//
// Definitions (exact, as in the death-rule probe).  a(0) = 0, history {0}.
// At clock n >= 1 the candidate is a(n-1) - n; subtract iff a(n-1) > n and
// the candidate is not in the history, else add n.  a(n) = q(n) n + r(n) with
// 0 <= r(n) < n (q = level, r = residue).  Both steps send r to r - q; a
// residue increase (wrap) ends an arc and starts the next one; the arc index
// of clock n is the number of wrap clocks <= n plus one (the first arc starts
// at clock 1).  Late landing: a(n) < n.  Comb: consecutive late landings
// v0, v0-1, ... two clocks apart.  Comb end: the last tooth (c, v), a late
// landing with v-1 visited at time c.  T = teeth.  Forced steps after a comb
// end: a(c+1) = c+v+1, a(c+2) = 2c+v+3, a(c+3) = 3c+v+6, candidate at c+4 =
// test value 2c+v+2.  Blocked = the test value is visited at time c (the
// step at c+4 is an addition).  Lock: at clock c+5+2i the orbit lands
// 3c+v+5-i (level 3), at c+6+2i the candidate is 2c+v-1-3i; visited =>
// addition (level 4), fresh => subtraction (break, i_obs = i).  Outcomes:
// break, wrap (arc ends), l3blocked (addition at c+5+2i), interrupted (a late
// landing while the lock is active; a guard, impossible by the Lean facts).
// Pre-landing run: J_obs completed L1-L2 pairs ending at c0-1, J_eff = J_obs +
// [the run started by a subtraction], i_gen = (T-1) + floor((J_eff+2)/3).
// Fresh case: a(c+4) = 2c+v+2 and the candidate at c+5 is c+v-3.
//
// Outputs (OUTDIR): pass1_summary.txt, queries.txt, records.txt (one line per
// query with the joined first-visit columns), summary.txt (the tables and the
// PASS/FAIL of the hypotheses (A) q >= 2, (B) upperRun or lowerRun, (C)
// sameArc => q = 2 and earlierArc => q >= 3, split into discovery c < 10^9
// and holdout 10^9 <= c < H).
//
// Build: c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
//          experiments/blocker_provenance_probe.cpp -o OUTDIR/provenance
// Run:   OUTDIR/provenance HORIZON OUTDIR

#include <algorithm>
#include <array>
#include <bit>
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
constexpr std::size_t kMaskBits = 64U;
constexpr Nat kBandHeightCap = 10000000ULL;
constexpr std::size_t kBandExitCap = 400000U;
constexpr Nat kDiscoveryLimit = 1000000000ULL;
constexpr std::size_t kExceptionCap = 50U;
constexpr std::size_t kQBins = 7U;      // q = 0..5, >= 6
constexpr std::size_t kRatioBins = 7U;  // n/c bins, see RatioBinName
constexpr std::size_t kLogBins = 64U;
constexpr std::size_t kFilterBits = 25U;
constexpr Nat kEmptyKey = ~Nat{0};

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

enum class Kind : unsigned char {
  kTest = 0,
  kLockCand,
  kL3,
  kEntry23,
  kBandExit
};
constexpr std::size_t kKinds = 5U;

const char* KindName(Kind k) {
  switch (k) {
    case Kind::kTest:
      return "test";
    case Kind::kLockCand:
      return "lockcand";
    case Kind::kL3:
      return "l3";
    case Kind::kEntry23:
      return "entry23";
    default:
      return "bandexit";
  }
}

// One blocking event.  For test: ex1 = i_obs (0 when the lock is still
// active at the horizon), ex2 = i_gen, outcome = the lock outcome.  For
// lockcand and l3: ex1 = i_obs, ex2 = i_gen.  For entry23: ex1 = J_obs,
// ex2 = h_prev.  For bandexit: ex1 = completed pairs of the level-1/2 run
// ending at n, ex2 = n minus the run's start clock.
struct Query {
  Kind kind = Kind::kTest;
  Nat w = 0U, c = 0U, v = 0U, teeth = 0U, arc = 0U, ex1 = 0U, ex2 = 0U;
  Nat event_clock = 0U;  // the clock at which the status of w mattered
  Outcome outcome = Outcome::kNone;
  std::size_t comb = 0U;   // index into the comb records (test only)
  std::size_t visit = 0U;  // index into the first-visit records (join)
};

// First visit of a queried value.
struct Visit {
  Nat w = 0U, n = 0U, q = 0U, r = 0U, arc = 0U, arc_start = 0U;
  Nat am2 = 0U, am1 = 0U, ap1 = 0U, ap2 = 0U;
  bool sub = false, resolved = false, has_ap1 = false, has_ap2 = false;
};

struct CombRec {
  Nat arc = 0U, c = 0U, v = 0U, teeth = 0U, c0 = 0U, v0 = 0U;
  Nat j_obs = 0U, h_prev = 0U, run_start = 0U;
  bool has_run = false, run_start_sub = false;
  bool blocked = false, arc_completed = false;
  Outcome outcome = Outcome::kNone;
  Nat i_obs = 0U, end_offset = 0U;
  Nat cand_mask = 0U;     // bit i: 2c+v-1-3i visited at time c
  bool cand_cv1 = false;  // some candidate i < 64 equals c+v+1
  std::size_t query = 0U;  // index of the test query (blocked only)
};

Nat IPred(Nat j) { return (j + 2U) / 3U; }
Nat JEff(const CombRec& r) { return r.j_obs + (r.run_start_sub ? 1U : 0U); }
Nat IGen(const CombRec& r) { return r.teeth - 1U + IPred(JEff(r)); }

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
  bool blocked = false, entry_visited = false;
  std::size_t idx = 0U;
};

struct RingRec {
  Nat value = 0U, k = 0U, arc = 0U, pairs = 0U, run_start = 0U;
  bool sub = false;
};

double Seconds(std::chrono::steady_clock::time_point start) {
  return std::chrono::duration<double>(std::chrono::steady_clock::now() - start)
      .count();
}

std::string CheckpointLine(const std::vector<Landing>& landings, bool* ok) {
  *ok = landings.size() >= kCheckpoints;
  for (std::size_t i = 0U; *ok && i < kCheckpoints; ++i)
    if (landings[i].index != kExpected[i].index ||
        landings[i].value != kExpected[i].value)
      *ok = false;
  std::string s;
  for (std::size_t i = 0U; i < std::min(landings.size(), kCheckpoints); ++i) {
    if (!s.empty()) s += ' ';
    s += std::to_string(landings[i].index) + "=" +
         std::to_string(landings[i].value);
  }
  return s;
}

// ---------------------------------------------------------------------------
// Pass 1: the death-rule probe's orbit with the query emission.
// ---------------------------------------------------------------------------
class Probe {
 public:
  explicit Probe(Nat horizon)
      : horizon_(horizon), start_(std::chrono::steady_clock::now()) {}

  void Run() {
    while (clock_ <= horizon_) Step();
    // Fill the test queries' outcomes from the comb records.
    for (Query& q : queries_) {
      if (q.kind != Kind::kTest) continue;
      const CombRec& r = records_[q.comb];
      q.outcome = r.outcome;
      q.ex1 = r.i_obs;
      q.ex2 = IGen(r);
    }
  }

  const std::vector<Query>& Queries() const { return queries_; }
  const std::vector<Query>& BandExits() const { return band_; }
  Nat BandTotal() const { return band_total_; }
  Nat BandStride() const { return band_stride_; }
  Nat BandSkippedHeight() const { return band_skipped_h_; }
  const std::vector<Landing>& Landings() const { return landings_; }
  Nat Arcs() const { return arc_ordinal_; }

  void WriteSummary(std::ostream& out) const {
    out << "pass1 horizon=" << horizon_ << " elapsed=" << Seconds(start_)
        << "s intervals=" << seen_.Count() << " mex=" << seen_.Mex()
        << " finalValue=" << value_ << '\n';
    bool ok = false;
    const std::string line = CheckpointLine(landings_, &ok);
    out << "checkpoint(first " << kCheckpoints << " landings) "
        << (ok ? "PASS" : "FAIL") << '\n';
    out << "first landings: " << line << '\n';
    out << "completed arcs=" << landings_.size() << " openArcOrdinal="
        << arc_ordinal_ << '\n';
    Nat blocked = 0U, open_ends = 0U, open_blocked = 0U;
    Nat outcome_count[5] = {};
    std::map<Nat, Nat> teeth_hist;
    for (const CombRec& r : records_) {
      if (r.blocked) ++blocked;
      if (!r.arc_completed) {
        ++open_ends;
        if (r.blocked) ++open_blocked;
      }
      if (r.blocked) ++outcome_count[static_cast<std::size_t>(r.outcome)];
      ++teeth_hist[r.teeth];
    }
    out << "comb ends total=" << records_.size() << " blocked(all)=" << blocked
        << " inOpenArc=" << open_ends << " blockedInOpenArc=" << open_blocked
        << '\n';
    Nat teeth_class[3] = {};
    std::map<std::size_t, Nat> teeth_log;  // floor(log2 T) -> count
    Nat teeth_max = 0U;
    for (const auto& kv : teeth_hist) {
      teeth_class[kv.first >= 3U ? 2U : static_cast<std::size_t>(kv.first) - 1U] +=
          kv.second;
      teeth_log[static_cast<std::size_t>(std::bit_width(kv.first)) - 1U] +=
          kv.second;
      teeth_max = std::max(teeth_max, kv.first);
    }
    out << "teeth T: T=1:" << teeth_class[0] << " T=2:" << teeth_class[1]
        << " T>=3:" << teeth_class[2] << " maxT=" << teeth_max
        << "; log2 histogram (floor(log2 T):count):";
    for (const auto& kv : teeth_log) out << ' ' << kv.first << ':' << kv.second;
    out << '\n';
    out << "lock outcomes (all blocked comb ends): break=" << outcome_count[1]
        << " wrap=" << outcome_count[2] << " l3blocked=" << outcome_count[3]
        << " interrupted=" << outcome_count[4] << " none(active at horizon)="
        << outcome_count[0] << '\n';
    out << "verification: a(c+3)=3c+v+6 checked=" << verify3_checked_
        << " mismatches=" << verify3_mismatch_
        << "; step c+4 is addition <=> blocked checked=" << verify4_checked_
        << " mismatches=" << verify4_mismatch_
        << "; fresh: step c+5 is addition <=> c+v-3 visited at c+4 checked="
        << verify5_checked_ << " mismatches=" << verify5_mismatch_ << '\n';
    out << "lock checks: step c+4 not addition=" << lock_mismatch4_
        << " pairIndexMismatch=" << lock_index_mismatch_
        << " level3ValueMismatch=" << lock_value_mismatch_
        << " level3LevelMismatch=" << lock_level3_mismatch_
        << " level4LevelMismatch=" << lock_level4_mismatch_ << '\n';
    out << "lockcand mask check (bit i_gen of the candidate mask at time c"
           " set): ok=" << lockcand_mask_ok_ << " notSet=" << lockcand_mask_bad_
        << " candEqualsC+v+1=" << lockcand_cv1_ << " iGen>=64(unchecked)="
        << lockcand_mask_unchecked_ << '\n';
    Nat breaks_gt = 0U, breaks_eq = 0U, breaks_lt = 0U;
    for (const CombRec& r : records_) {
      if (!r.blocked || r.outcome != Outcome::kBreak) continue;
      const Nat ig = IGen(r);
      if (r.i_obs > ig) ++breaks_gt;
      else if (r.i_obs == ig) ++breaks_eq;
      else ++breaks_lt;
    }
    out << "breaks: i_obs > i_gen=" << breaks_gt << " i_obs == i_gen="
        << breaks_eq << " i_obs < i_gen=" << breaks_lt << '\n';
    Nat per_kind[kKinds] = {};
    for (const Query& q : queries_) ++per_kind[static_cast<std::size_t>(q.kind)];
    out << "queries: test=" << per_kind[0] << " lockcand=" << per_kind[1]
        << " l3=" << per_kind[2] << " entry23=" << per_kind[3] << '\n';
    out << "band exits (2 <= h <= " << kBandHeightCap << "): total="
        << band_total_ << " kept=" << band_.size() << " samplingFactor="
        << band_stride_ << " (every k-th exit, ordinals 0, k, 2k, ...);"
           " level-1 clocks followed by two additions with h > cap="
        << band_skipped_h_ << " with h < 2=" << band_skipped_small_ << '\n';
    Nat band_in_run = 0U;
    for (const Query& q : band_)
      if (q.ex1 > 0U) ++band_in_run;
    out << "band exits kept with >= 1 completed pair before n=" << band_in_run
        << '\n';
  }

 private:
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

    if (verify_.active) OnVerifyStep(clock, subtract);

    const bool wrapped = in_arc_ && r > prev_residue_;
    if (wrapped) {
      FinishArc(clock);
      StartArc(clock);
    } else if (!in_arc_) {
      StartArc(clock);
    }

    if (lock_.active) OnLockStep(clock, subtract, k, r);

    if (value_ < arc_min_value_) {
      arc_min_value_ = value_;
      arc_min_clock_ = clock;
    }

    // The run state before this clock is what a late landing at this clock
    // sees (the run ends at the clock before the landing).
    const bool run_l1_before = run_state_ == RunState::kL1;
    const bool start_sub_before = run_start_sub_;
    const Nat pairs_before = run_pairs_, h_before = run_start_height_,
              start_before = run_start_clock_;

    if (late) {
      if (lock_.active)
        ResolveLock(Outcome::kInterrupted, lock_.i, clock - lock_.c);
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

    // Band exit: clock n = clock-2 was a level-1 clock and the steps at n+1
    // and n+2 were both additions (h-1 visited, then a(n)-1 visited).
    if (clock >= 3U && ring_[0].k == 1U && !ring_[1].sub && !subtract) {
      const Nat n = clock - 2U;
      const Nat h = ring_[0].value - n;
      if (h < 2U) {
        ++band_skipped_small_;
      } else if (h > kBandHeightCap) {
        ++band_skipped_h_;
      } else {
        OnBandExit(n, h, ring_[0]);
      }
    }
    ring_[0] = ring_[1];
    ring_[1] = RingRec{value_, k, arc_ordinal_, run_pairs_, run_start_clock_,
                       subtract};

    prev_residue_ = r;
    prev_k_ = k;

    if (clock == next_progress_) {
      std::cerr << "pass1 progress clock=" << clock << " value=" << value_
                << " intervals=" << seen_.Count() << " arcs="
                << landings_.size() << " combEnds=" << records_.size()
                << " blocked=" << blocked_total_ << " queries="
                << queries_.size() << " bandExits=" << band_total_
                << " elapsed=" << Seconds(start_) << "s\n";
      next_progress_ += kProgressStep;
    }
    clock_ = clock + 1U;
  }

  void OnVerifyStep(Nat clock, bool subtract) {
    const Nat c = verify_.clock, v = verify_.value;
    if (clock == c + 3U) {
      ++verify3_checked_;
      if (value_ != 3U * c + v + 6U) ++verify3_mismatch_;
    } else if (clock == c + 4U) {
      ++verify4_checked_;
      if ((!subtract) != verify_.blocked) ++verify4_mismatch_;
      if (verify_.blocked) {
        verify_.active = false;
      } else {
        // a(c+4) = 2c+v+2; the candidate at c+5 is c+v-3.
        const Nat cv = c + v;
        verify_.entry_visited =
            cv >= 3U && seen_.Contains(cv - 3U, IntervalSet::kBelow);
        if (verify_.entry_visited) {
          const CombRec& rec = records_[verify_.idx];
          Query q;
          q.kind = Kind::kEntry23;
          q.w = cv - 3U;
          q.c = c;
          q.v = v;
          q.teeth = rec.teeth;
          q.arc = rec.arc;
          q.ex1 = rec.j_obs;
          q.ex2 = rec.h_prev;
          q.event_clock = c + 5U;
          queries_.push_back(q);
        }
      }
    } else if (clock == c + 5U) {
      ++verify5_checked_;
      if ((!subtract) != verify_.entry_visited) ++verify5_mismatch_;
      verify_.active = false;
    }
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
    rec.arc = arc_ordinal_;
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
    if (rec.blocked) {
      ++blocked_total_;
      Query q;
      q.kind = Kind::kTest;
      q.w = test;
      q.c = c;
      q.v = v;
      q.teeth = rec.teeth;
      q.arc = rec.arc;
      q.event_clock = c + 4U;
      q.comb = records_.size();
      rec.query = queries_.size();
      queries_.push_back(q);
    }
    records_.push_back(rec);
    const std::size_t idx = records_.size() - 1U;
    verify_ = Verify{true, c, v, rec.blocked, false, idx};
    if (rec.blocked) {
      if (lock_.active)  // cannot happen: a late landing resolves it first
        ResolveLock(Outcome::kInterrupted, lock_.i, 0U);
      lock_ = LockState{true, c, v, 0U, idx};
    }
  }

  void OnLockStep(Nat clock, bool subtract, Nat k, Nat r) {
    (void)r;
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
        ResolveLock(Outcome::kL3Blocked, i, off);
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
      ResolveLock(Outcome::kBreak, i, off);
    }
  }

  void ResolveLock(Outcome o, Nat i, Nat end_offset) {
    CombRec& rec = records_[lock_.idx];
    rec.outcome = o;
    rec.i_obs = i;
    rec.end_offset = end_offset;
    lock_.active = false;
    const Nat ig = IGen(rec);
    if (o == Outcome::kBreak && i > ig) {
      Query q;
      q.kind = Kind::kLockCand;
      q.w = 2U * rec.c + rec.v - 1U - 3U * ig;
      q.c = rec.c;
      q.v = rec.v;
      q.teeth = rec.teeth;
      q.arc = rec.arc;
      q.ex1 = i;
      q.ex2 = ig;
      q.event_clock = rec.c + 6U + 2U * ig;
      queries_.push_back(q);
      if (q.w == rec.c + rec.v + 1U) ++lockcand_cv1_;
      if (ig >= kMaskBits) {
        ++lockcand_mask_unchecked_;
      } else if (((rec.cand_mask >> ig) & 1U) != 0U) {
        ++lockcand_mask_ok_;
      } else {
        ++lockcand_mask_bad_;
      }
    } else if (o == Outcome::kL3Blocked) {
      Query q;
      q.kind = Kind::kL3;
      q.w = 3U * rec.c + rec.v + 5U - i;
      q.c = rec.c;
      q.v = rec.v;
      q.teeth = rec.teeth;
      q.arc = rec.arc;
      q.ex1 = i;
      q.ex2 = ig;
      q.event_clock = rec.c + 5U + 2U * i;
      queries_.push_back(q);
    }
  }

  void OnBandExit(Nat n, Nat h, const RingRec& at_n) {
    const Nat ord = band_total_++;
    if (ord % band_stride_ != 0U) return;
    if (band_.size() >= kBandExitCap) {
      std::size_t j = 0U;
      for (std::size_t i = 0U; i < band_.size(); i += 2U) band_[j++] = band_[i];
      band_.resize(j);
      band_stride_ *= 2U;
      if (ord % band_stride_ != 0U) return;
    }
    Query q;
    q.kind = Kind::kBandExit;
    q.w = at_n.value - 1U;
    q.c = n;
    q.v = h;
    q.teeth = 0U;
    q.arc = at_n.arc;
    q.ex1 = at_n.pairs;
    q.ex2 = n - at_n.run_start;
    q.event_clock = n + 2U;
    band_.push_back(q);
  }

  void StartArc(Nat clock) {
    in_arc_ = true;
    arc_ordinal_ = landings_.size() + 1U;
    arc_start_ = clock;
    arc_min_value_ = value_;
    arc_min_clock_ = clock;
    arc_first_record_ = records_.size();
  }

  // The arc consists of the clocks [arc_start_, wrap_clock - 1].
  void FinishArc(Nat wrap_clock) {
    if (lock_.active)
      ResolveLock(Outcome::kWrap, lock_.i, wrap_clock - lock_.c);
    landings_.push_back(Landing{arc_min_clock_, arc_min_value_});
    for (std::size_t i = arc_first_record_; i < records_.size(); ++i)
      records_[i].arc_completed = true;
    in_arc_ = false;
  }

  const Nat horizon_;
  const std::chrono::steady_clock::time_point start_;
  IntervalSet seen_;
  Nat clock_ = 1U;
  Nat value_ = 0U;
  bool in_arc_ = false;
  Nat prev_residue_ = 0U, prev_k_ = 0U;
  Nat arc_ordinal_ = 0U, arc_start_ = 0U, arc_min_value_ = 0U,
      arc_min_clock_ = 0U;
  std::size_t arc_first_record_ = 0U;
  Verify verify_;
  Nat verify3_checked_ = 0U, verify3_mismatch_ = 0U;
  Nat verify4_checked_ = 0U, verify4_mismatch_ = 0U;
  Nat verify5_checked_ = 0U, verify5_mismatch_ = 0U;
  Nat lock_mismatch4_ = 0U, lock_index_mismatch_ = 0U,
      lock_value_mismatch_ = 0U, lock_level3_mismatch_ = 0U,
      lock_level4_mismatch_ = 0U;
  Nat lockcand_mask_ok_ = 0U, lockcand_mask_bad_ = 0U, lockcand_cv1_ = 0U,
      lockcand_mask_unchecked_ = 0U;
  RunState run_state_ = RunState::kNone;
  Nat run_pairs_ = 0U, run_start_clock_ = 0U, run_start_height_ = 0U;
  bool run_start_sub_ = false;
  Nat last_late_clock_ = 0U, last_late_value_ = 0U;
  CombState comb_;
  LockState lock_;
  std::vector<CombRec> records_;
  std::vector<Query> queries_;
  std::vector<Query> band_;
  Nat band_total_ = 0U, band_stride_ = 1U, band_skipped_h_ = 0U,
      band_skipped_small_ = 0U;
  RingRec ring_[2];
  std::vector<Landing> landings_;
  Nat blocked_total_ = 0U;
  Nat next_progress_ = kProgressStep;
};

// ---------------------------------------------------------------------------
// Pass 2: the first visits of the queried values.
// ---------------------------------------------------------------------------
Nat Mix(Nat x) {
  x ^= x >> 30;
  x *= 0xbf58476d1ce4e5b9ULL;
  x ^= x >> 27;
  x *= 0x94d049bb133111ebULL;
  x ^= x >> 31;
  return x;
}

class ValueTable {
 public:
  explicit ValueTable(const std::vector<Nat>& sorted_unique)
      : filter_((Nat{1} << kFilterBits) / 64U, 0U) {
    std::size_t cap = 1024U;
    while (cap < 2U * sorted_unique.size() + 16U) cap *= 2U;
    keys_.assign(cap, kEmptyKey);
    vals_.assign(cap, 0U);
    mask_ = cap - 1U;
    for (std::size_t i = 0U; i < sorted_unique.size(); ++i) {
      const Nat w = sorted_unique[i];
      if (w == kEmptyKey) throw std::runtime_error("key collides with sentinel");
      const Nat h = Mix(w);
      std::size_t p = static_cast<std::size_t>(h) & mask_;
      while (keys_[p] != kEmptyKey) p = (p + 1U) & mask_;
      keys_[p] = w;
      vals_[p] = static_cast<std::uint32_t>(i);
      const Nat f = h >> (64U - kFilterBits);
      filter_[f >> 6U] |= Nat{1} << (f & 63U);
    }
  }

  static constexpr std::size_t kNotFound = ~std::size_t{0};

  // Index of w in the sorted unique list, or kNotFound.
  std::size_t Find(Nat w) const {
    const Nat h = Mix(w);
    const Nat f = h >> (64U - kFilterBits);
    if (((filter_[f >> 6U] >> (f & 63U)) & 1U) == 0U) return kNotFound;
    std::size_t p = static_cast<std::size_t>(h) & mask_;
    while (keys_[p] != kEmptyKey) {
      if (keys_[p] == w) return vals_[p];
      p = (p + 1U) & mask_;
    }
    return kNotFound;
  }

  std::size_t Capacity() const { return keys_.size(); }

 private:
  std::vector<Nat> filter_;
  std::vector<Nat> keys_;
  std::vector<std::uint32_t> vals_;
  std::size_t mask_ = 0U;
};

class Replay {
 public:
  Replay(Nat horizon, const ValueTable& table, std::vector<Visit>& visits)
      : horizon_(horizon), table_(table), visits_(visits),
        start_(std::chrono::steady_clock::now()) {}

  void Run() {
    while (clock_ <= horizon_) Step();
  }

  const std::vector<Landing>& Landings() const { return landings_; }
  Nat Arcs() const { return arc_ordinal_; }
  Nat FilterHits() const { return filter_hits_; }
  Nat Resolved() const { return resolved_; }
  double Elapsed() const { return Seconds(start_); }
  Nat FinalValue() const { return value_; }
  std::size_t Intervals() const { return seen_.Count(); }

 private:
  struct Pending {
    std::size_t idx;
    Nat n;
  };

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

    const bool wrapped = in_arc_ && r > prev_residue_;
    if (wrapped) {
      landings_.push_back(Landing{arc_min_clock_, arc_min_value_});
      in_arc_ = false;
    }
    if (!in_arc_) {
      in_arc_ = true;
      arc_ordinal_ = landings_.size() + 1U;
      arc_start_ = clock;
      arc_min_value_ = value_;
      arc_min_clock_ = clock;
    }
    if (value_ < arc_min_value_) {
      arc_min_value_ = value_;
      arc_min_clock_ = clock;
    }

    if (!pending_.empty()) {
      for (std::size_t i = 0U; i < pending_.size();) {
        Visit& vis = visits_[pending_[i].idx];
        if (clock == pending_[i].n + 1U) {
          vis.ap1 = value_;
          vis.has_ap1 = true;
          ++i;
        } else if (clock == pending_[i].n + 2U) {
          vis.ap2 = value_;
          vis.has_ap2 = true;
          pending_.erase(pending_.begin() + static_cast<std::ptrdiff_t>(i));
        } else {
          ++i;
        }
      }
    }

    const std::size_t idx = table_.Find(value_);
    if (idx != ValueTable::kNotFound) {
      ++filter_hits_;
      Visit& vis = visits_[idx];
      if (!vis.resolved) {
        if (vis.w != value_) throw std::runtime_error("visit/key mismatch");
        vis.resolved = true;
        ++resolved_;
        vis.n = clock;
        vis.q = k;
        vis.r = r;
        vis.arc = arc_ordinal_;
        vis.arc_start = arc_start_;
        vis.am2 = prev2_;
        vis.am1 = prev;
        vis.sub = subtract;
        pending_.push_back(Pending{idx, clock});
      }
    }

    prev2_ = prev;
    prev_residue_ = r;
    if (clock == next_progress_) {
      std::cerr << "pass2 progress clock=" << clock << " value=" << value_
                << " intervals=" << seen_.Count() << " arcs="
                << landings_.size() << " resolved=" << resolved_ << " of "
                << visits_.size() << " elapsed=" << Seconds(start_) << "s\n";
      next_progress_ += kProgressStep;
    }
    clock_ = clock + 1U;
  }

  const Nat horizon_;
  const ValueTable& table_;
  std::vector<Visit>& visits_;
  const std::chrono::steady_clock::time_point start_;
  IntervalSet seen_;
  Nat clock_ = 1U;
  Nat value_ = 0U;
  Nat prev2_ = 0U;
  bool in_arc_ = false;
  Nat prev_residue_ = 0U;
  Nat arc_ordinal_ = 0U, arc_start_ = 0U, arc_min_value_ = 0U,
      arc_min_clock_ = 0U;
  std::vector<Landing> landings_;
  std::vector<Pending> pending_;
  Nat filter_hits_ = 0U, resolved_ = 0U;
  Nat next_progress_ = kProgressStep;
};

// ---------------------------------------------------------------------------
// Join and summary.
// ---------------------------------------------------------------------------
struct Derived {
  bool same = false, upper = false, lower = false;
  std::size_t qbin = 0U, rbin = 0U, lgbin = 0U, runclass = 0U, tclass = 0U,
              oclass = 0U;
  std::size_t dl = 0U;     // q - L_kind class: 0: q < L, 1: q = L, 2: L+1,
                           // 3: L+2, 4: >= L+3
  std::size_t adist = 0U;  // arcAtC - arcN: 0, 1, 2, >= 3
  bool n_before = false;   // first visit before the event clock
  Nat gap = 0U;            // c - n when n < c
};

// The level of the blocking value at its event: the test value 2c+v+2 and
// the lock candidate 2c+v-1-3i are level-2 values, the level-3 value
// 3c+v+5-i is level 3, the entry candidate c+v-3 and the band value a(n)-1
// are level-1 values.
Nat KindLevel(Kind k) {
  switch (k) {
    case Kind::kTest:
    case Kind::kLockCand:
      return 2U;
    case Kind::kL3:
      return 3U;
    default:
      return 1U;
  }
}
const char* DlName(std::size_t d) {
  static const char* names[5] = {"q<L", "q=L", "q=L+1", "q=L+2", "q>=L+3"};
  return names[d];
}
const char* ADistName(std::size_t d) {
  static const char* names[4] = {"same", "prev", "prev2", "older"};
  return names[d];
}

std::size_t QBin(Nat q) { return q >= 6U ? 6U : static_cast<std::size_t>(q); }
const char* QBinName(std::size_t b) {
  static const char* names[kQBins] = {"q=0", "q=1", "q=2", "q=3",
                                      "q=4", "q=5", "q>=6"};
  return names[b];
}
std::size_t RatioBin(Nat n, Nat c) {
  if (n * 8U < c) return 0U;
  if (n * 4U < c) return 1U;
  if (n * 3U < c) return 2U;
  if (n * 2U < c) return 3U;
  if (n * 3U < 2U * c) return 4U;
  if (n < c) return 5U;
  return 6U;
}
const char* RatioBinName(std::size_t b) {
  static const char* names[kRatioBins] = {
      "[0,1/8)", "[1/8,1/4)", "[1/4,1/3)", "[1/3,1/2)",
      "[1/2,2/3)", "[2/3,1)", "[1,inf)"};
  return names[b];
}
// floor(log2(c/n)) for n < c (bin 63 = n >= c).
std::size_t LogBin(Nat n, Nat c) {
  if (n == 0U || n >= c) return kLogBins - 1U;
  return static_cast<std::size_t>(std::bit_width(c / n)) - 1U;
}
std::size_t GapLogBin(Nat gap) {
  if (gap == 0U) return kLogBins - 1U;
  return static_cast<std::size_t>(std::bit_width(gap)) - 1U;
}
const char* RunClassName(std::size_t rc) {
  static const char* names[4] = {"neither", "upperOnly", "lowerOnly", "both"};
  return names[rc];
}
std::size_t TClass(Nat t) { return t >= 3U ? 2U : static_cast<std::size_t>(t) - 1U; }
const char* TClassName(std::size_t t) {
  static const char* names[3] = {"T=1", "T=2", "T>=3"};
  return names[t];
}
std::size_t OClass(Outcome o) {
  switch (o) {
    case Outcome::kBreak:
      return 0U;
    case Outcome::kWrap:
      return 1U;
    case Outcome::kL3Blocked:
      return 2U;
    default:
      return 3U;
  }
}
const char* OClassName(std::size_t o) {
  static const char* names[4] = {"break", "wrap", "l3blocked", "none/other"};
  return names[o];
}

Derived Derive(const Query& q, const Visit& v) {
  Derived d;
  d.same = v.arc == q.arc;
  d.upper = (v.has_ap2 && v.ap2 == v.w + 1U) || (v.n >= 2U && v.am2 + 1U == v.w);
  d.lower = (v.has_ap2 && v.ap2 + 1U == v.w) || (v.n >= 2U && v.am2 == v.w + 1U);
  d.qbin = QBin(v.q);
  d.rbin = RatioBin(v.n, q.c);
  d.lgbin = LogBin(v.n, q.c);
  d.runclass = (d.upper ? 1U : 0U) + (d.lower ? 2U : 0U);
  d.tclass = q.teeth >= 1U ? TClass(q.teeth) : 0U;
  d.oclass = OClass(q.outcome);
  d.n_before = v.n < q.event_clock;
  d.gap = v.n < q.c ? q.c - v.n : 0U;
  const Nat level = KindLevel(q.kind);
  if (v.q < level)
    d.dl = 0U;
  else
    d.dl = std::min<std::size_t>(static_cast<std::size_t>(v.q - level) + 1U, 4U);
  const Nat dist = q.arc >= v.arc ? q.arc - v.arc : 3U;
  d.adist = dist >= 3U ? 3U : static_cast<std::size_t>(dist);
  return d;
}

void WriteRecord(std::ostream& out, const Query& q, const Visit& v,
                 const Derived& d) {
  out << KindName(q.kind) << ' ' << q.w << ' ' << q.c << ' ' << q.v << ' '
      << q.teeth << ' ' << q.arc << ' ' << q.ex1 << ' ' << q.ex2 << ' '
      << OutcomeName(q.outcome) << ' ' << q.event_clock << " | " << v.n << ' '
      << (v.sub ? 'S' : 'A') << ' ' << v.q << ' ' << v.r << ' ' << v.arc << ' '
      << v.arc_start << ' ' << v.am2 << ' ' << v.am1 << ' ' << v.ap1 << ' '
      << v.ap2 << ' ' << d.upper << ' ' << d.lower << ' ' << d.same << ' '
      << d.gap << ' ' << std::fixed << std::setprecision(6)
      << (q.c > 0U ? static_cast<double>(v.n) / static_cast<double>(q.c) : 0.0)
      << '\n';
}

struct Tally {
  Nat count = 0U, same = 0U, before = 0U;
  std::array<Nat, kQBins> q{};
  std::array<std::array<Nat, kQBins>, 2> same_q{};  // [same][q]
  std::array<std::array<Nat, kQBins>, 2> step_q{};  // [sub][q]
  std::array<std::array<Nat, kQBins>, 4> run_q{};   // [runclass][q]
  std::array<Nat, kRatioBins> ratio{};
  std::array<Nat, kLogBins> lg{};
  std::array<std::array<Nat, kQBins>, 3> t_q{};     // [T class][q]
  std::array<std::array<Nat, 2>, 3> t_same{};       // [T class][same]
  std::array<std::array<Nat, kQBins>, 4> o_q{};     // [outcome][q]
  std::array<std::array<Nat, 2>, 4> o_same{};       // [outcome][same]
  std::array<Nat, kLogBins> gap_same2{};            // sameArc & q=2: log2 gap
  std::array<Nat, kLogBins> gap_all{};
  std::array<std::array<Nat, 5>, 2> same_dl{};      // [same][q - L class]
  std::array<std::array<Nat, kQBins>, 4> adist_q{}; // [arc distance][q]

  void Add(const Visit& v, const Derived& d) {
    ++count;
    if (d.same) ++same;
    if (d.n_before) ++before;
    ++same_dl[d.same ? 1U : 0U][d.dl];
    ++adist_q[d.adist][d.qbin];
    ++q[d.qbin];
    ++same_q[d.same ? 1U : 0U][d.qbin];
    ++step_q[v.sub ? 1U : 0U][d.qbin];
    ++run_q[d.runclass][d.qbin];
    ++ratio[d.rbin];
    ++lg[d.lgbin];
    ++t_q[d.tclass][d.qbin];
    ++t_same[d.tclass][d.same ? 1U : 0U];
    ++o_q[d.oclass][d.qbin];
    ++o_same[d.oclass][d.same ? 1U : 0U];
    ++gap_all[GapLogBin(d.gap)];
    if (d.same && v.q == 2U) ++gap_same2[GapLogBin(d.gap)];
  }
};

void WriteQRow(std::ostream& out, const char* label,
               const std::array<Nat, kQBins>& row) {
  out << "    " << std::left << std::setw(12) << label << std::right;
  Nat total = 0U;
  for (std::size_t b = 0U; b < kQBins; ++b) {
    out << ' ' << std::setw(8) << row[b];
    total += row[b];
  }
  out << ' ' << std::setw(8) << total << '\n';
}

void WriteQHeader(std::ostream& out) {
  out << "    " << std::left << std::setw(12) << "" << std::right;
  for (std::size_t b = 0U; b < kQBins; ++b) out << ' ' << std::setw(8) << QBinName(b);
  out << ' ' << std::setw(8) << "total" << '\n';
}

void WriteLogHist(std::ostream& out, const char* label,
                  const std::array<Nat, kLogBins>& h, const char* unit) {
  out << "    " << label << " (floor(log2(" << unit << ")):count):";
  bool any = false;
  for (std::size_t b = 0U; b + 1U < kLogBins; ++b) {
    if (h[b] == 0U) continue;
    out << ' ' << b << ':' << h[b];
    any = true;
  }
  if (h[kLogBins - 1U] != 0U) out << " undefined:" << h[kLogBins - 1U];
  if (!any && h[kLogBins - 1U] == 0U) out << " (none)";
  out << '\n';
}

void WriteTally(std::ostream& out, const Tally& t, bool test_extras) {
  out << "  count=" << t.count << " sameArc=" << t.same << " earlierArc="
      << t.count - t.same << " firstVisitBeforeEvent=" << t.before
      << " (must equal count)\n";
  out << "  level q at the first visit:\n";
  WriteQHeader(out);
  WriteQRow(out, "all", t.q);
  out << "  sameArc x q:\n";
  WriteQHeader(out);
  WriteQRow(out, "sameArc", t.same_q[1]);
  WriteQRow(out, "earlierArc", t.same_q[0]);
  out << "  step type x q:\n";
  WriteQHeader(out);
  WriteQRow(out, "S", t.step_q[1]);
  WriteQRow(out, "A", t.step_q[0]);
  out << "  run class x q:\n";
  WriteQHeader(out);
  for (std::size_t rc = 0U; rc < 4U; ++rc) WriteQRow(out, RunClassName(rc), t.run_q[rc]);
  out << "  arc distance (arcAtC - arcN) x q:\n";
  WriteQHeader(out);
  for (std::size_t ad = 0U; ad < 4U; ++ad) WriteQRow(out, ADistName(ad), t.adist_q[ad]);
  out << "  q relative to the event level L (L=2 test/lockcand, 3 l3, 1"
         " entry23/bandexit):\n";
  for (std::size_t s = 0U; s < 2U; ++s) {
    out << "    " << (s == 1U ? "sameArc   " : "earlierArc");
    for (std::size_t dl = 0U; dl < 5U; ++dl)
      out << ' ' << DlName(dl) << ':' << t.same_dl[s][dl];
    out << '\n';
  }
  out << "  n/c histogram:";
  for (std::size_t b = 0U; b < kRatioBins; ++b)
    out << ' ' << RatioBinName(b) << ':' << t.ratio[b];
  out << '\n';
  WriteLogHist(out, "c/n log2 histogram", t.lg, "c/n");
  WriteLogHist(out, "gap c-n log2 histogram (all)", t.gap_all, "c-n");
  if (test_extras) {
    out << "  T x q:\n";
    WriteQHeader(out);
    for (std::size_t tc = 0U; tc < 3U; ++tc) WriteQRow(out, TClassName(tc), t.t_q[tc]);
    out << "  T x arc: ";
    for (std::size_t tc = 0U; tc < 3U; ++tc)
      out << TClassName(tc) << ": sameArc=" << t.t_same[tc][1] << " earlierArc="
          << t.t_same[tc][0] << "; ";
    out << '\n';
    out << "  lock outcome x q:\n";
    WriteQHeader(out);
    for (std::size_t oc = 0U; oc < 4U; ++oc) WriteQRow(out, OClassName(oc), t.o_q[oc]);
    out << "  lock outcome x arc: ";
    for (std::size_t oc = 0U; oc < 4U; ++oc)
      out << OClassName(oc) << ": sameArc=" << t.o_same[oc][1] << " earlierArc="
          << t.o_same[oc][0] << "; ";
    out << '\n';
    WriteLogHist(out, "gap c-n log2 histogram (sameArc & q=2)", t.gap_same2,
                 "c-n");
  }
}

constexpr std::size_t kExcTypes = 5U;
const char* ExcName(std::size_t e) {
  static const char* names[kExcTypes] = {
      "q <= 1 (first visit at level 0 or 1)", "run class = neither",
      "sameArc with q != 2", "earlierArc with q <= 2",
      ("generalized (C'): sameArc with q != L_kind or earlierArc with"
       " q <= L_kind")};
  return names[e];
}

struct Split {
  std::array<Tally, kKinds> per_kind{};
  Tally all{};
  std::array<std::vector<std::size_t>, kExcTypes> exc{};
  std::array<Nat, kExcTypes> exc_count{};
  std::array<std::array<Nat, kKinds>, kExcTypes> exc_kind{};
};

void Usage() { throw std::invalid_argument("usage: HORIZON OUTDIR"); }

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc < 3) Usage();
    const Nat horizon = std::stoull(argv[1]);
    if (horizon < 10U) throw std::invalid_argument("horizon must be >= 10");
    const std::string outdir = argv[2];
    const auto t0 = std::chrono::steady_clock::now();

    // ---- pass 1 ----
    Probe probe(horizon);
    probe.Run();
    std::vector<Query> queries = probe.Queries();
    for (const Query& q : probe.BandExits()) queries.push_back(q);
    {
      std::ofstream out(outdir + "/pass1_summary.txt");
      if (!out) throw std::runtime_error("cannot open pass1_summary.txt");
      probe.WriteSummary(out);
      std::ofstream qf(outdir + "/queries.txt");
      qf << "# kind w c v T arcAtC ex1 ex2 outcome eventClock\n";
      for (const Query& q : queries)
        qf << KindName(q.kind) << ' ' << q.w << ' ' << q.c << ' ' << q.v << ' '
           << q.teeth << ' ' << q.arc << ' ' << q.ex1 << ' ' << q.ex2 << ' '
           << OutcomeName(q.outcome) << ' ' << q.event_clock << '\n';
    }
    {
      bool ok = false;
      const std::string line = CheckpointLine(probe.Landings(), &ok);
      std::cerr << "pass1 done: checkpoint " << (ok ? "PASS" : "FAIL") << ": "
                << line << "\npass1 queries=" << queries.size()
                << " (bandExits kept=" << probe.BandExits().size()
                << " of " << probe.BandTotal() << ", factor="
                << probe.BandStride() << ") elapsed=" << Seconds(t0) << "s\n";
    }

    // ---- pass 2 ----
    std::vector<Nat> keys;
    keys.reserve(queries.size());
    for (const Query& q : queries) keys.push_back(q.w);
    std::sort(keys.begin(), keys.end());
    keys.erase(std::unique(keys.begin(), keys.end()), keys.end());
    std::vector<Visit> visits(keys.size());
    for (std::size_t i = 0U; i < keys.size(); ++i) visits[i].w = keys[i];
    ValueTable table(keys);
    for (Query& q : queries) {
      q.visit = table.Find(q.w);
      if (q.visit == ValueTable::kNotFound)
        throw std::runtime_error("query value missing from the table");
    }
    Replay replay(horizon, table, visits);
    replay.Run();
    Nat unresolved = 0U, no_ap2 = 0U;
    for (const Visit& v : visits) {
      if (!v.resolved) ++unresolved;
      else if (!v.has_ap2) ++no_ap2;
    }
    bool ok2 = false;
    const std::string line2 = CheckpointLine(replay.Landings(), &ok2);
    std::cerr << "pass2 done: checkpoint " << (ok2 ? "PASS" : "FAIL")
              << " resolved=" << replay.Resolved() << " of " << visits.size()
              << " unresolved=" << unresolved << " elapsed=" << Seconds(t0)
              << "s\n";

    // ---- join ----
    std::ofstream rec(outdir + "/records.txt");
    if (!rec) throw std::runtime_error("cannot open records.txt");
    rec << "# kind w c v T arcAtC ex1 ex2 outcome eventClock | n step q r"
           " arcN arcStart a(n-2) a(n-1) a(n+1) a(n+2) upperRun lowerRun"
           " sameArc gap(c-n) n/c\n";
    std::array<Split, 2> splits{};
    std::vector<Derived> derived(queries.size());
    Nat not_before = 0U, unresolved_queries = 0U;
    for (std::size_t i = 0U; i < queries.size(); ++i) {
      const Query& q = queries[i];
      const Visit& v = visits[q.visit];
      if (!v.resolved) {
        ++unresolved_queries;
        rec << KindName(q.kind) << ' ' << q.w << ' ' << q.c << ' ' << q.v
            << " UNRESOLVED\n";
        continue;
      }
      const Derived d = Derive(q, v);
      derived[i] = d;
      if (!d.n_before) ++not_before;
      WriteRecord(rec, q, v, d);
      Split& sp = splits[q.c < kDiscoveryLimit ? 0U : 1U];
      const std::size_t kind = static_cast<std::size_t>(q.kind);
      sp.per_kind[kind].Add(v, d);
      sp.all.Add(v, d);
      const bool flags[kExcTypes] = {
          v.q <= 1U, d.runclass == 0U, d.same && v.q != 2U,
          !d.same && v.q <= 2U,
          d.same ? d.dl != 1U : d.dl <= 1U};
      for (std::size_t e = 0U; e < kExcTypes; ++e) {
        if (!flags[e]) continue;
        ++sp.exc_count[e];
        ++sp.exc_kind[e][kind];
        if (sp.exc[e].size() < kExceptionCap) sp.exc[e].push_back(i);
      }
    }

    // ---- summary ----
    std::ofstream out(outdir + "/summary.txt");
    if (!out) throw std::runtime_error("cannot open summary.txt");
    out << "blocker-provenance-probe horizon=" << horizon << " elapsed="
        << Seconds(t0) << "s\n\n";
    out << "== pass 1 ==\n";
    probe.WriteSummary(out);
    out << "\n== pass 2 ==\n";
    out << "pass2 elapsed=" << replay.Elapsed() << "s intervals="
        << replay.Intervals() << " finalValue=" << replay.FinalValue() << '\n';
    out << "checkpoint(first " << kCheckpoints << " landings) "
        << (ok2 ? "PASS" : "FAIL") << '\n';
    out << "first landings: " << line2 << '\n';
    out << "completed arcs=" << replay.Landings().size() << " openArcOrdinal="
        << replay.Arcs() << " (pass 1: " << probe.Landings().size() << ", "
        << probe.Arcs() << ")\n";
    out << "unique queried values=" << visits.size() << " tableCapacity="
        << table.Capacity() << " filterBits=" << kFilterBits
        << " filterHits(clocks whose value passed the filter and was in the"
           " table)=" << replay.FilterHits() << '\n';
    out << "resolved=" << replay.Resolved() << " unresolved(must be 0)="
        << unresolved << " resolvedWithoutA(n+2)=" << no_ap2 << '\n';
    out << "queries total=" << queries.size() << " unresolvedQueries="
        << unresolved_queries << " firstVisitNotBeforeEvent(must be 0)="
        << not_before << '\n';

    const char* split_names[2] = {"discovery (c < 10^9)",
                                  "holdout (10^9 <= c < H)"};
    for (std::size_t s = 0U; s < 2U; ++s) {
      const Split& sp = splits[s];
      if (s == 1U && horizon <= kDiscoveryLimit) continue;
      out << "\n==== " << split_names[s] << " ====\n";
      out << "queries=" << sp.all.count;
      for (std::size_t k = 0U; k < kKinds; ++k)
        out << ' ' << KindName(static_cast<Kind>(k)) << '='
            << sp.per_kind[k].count;
      out << '\n';
      for (std::size_t k = 0U; k < kKinds; ++k) {
        out << "\n-- kind=" << KindName(static_cast<Kind>(k)) << " --\n";
        WriteTally(out, sp.per_kind[k], k == 0U);
      }
      out << "\n-- all kinds --\n";
      WriteTally(out, sp.all, false);
      out << "\n-- hypotheses --\n";
      const Nat a_fail = sp.exc_count[0], b_fail = sp.exc_count[1],
                c_fail = sp.exc_count[2] + sp.exc_count[3];
      out << "(A) every blocking value first visited at level q >= 2: "
          << (a_fail == 0U ? "PASS" : "FAIL") << " (violations=" << a_fail
          << " of " << sp.all.count << ")\n";
      out << "(B) every blocking value in a ping-pong run at its first visit"
             " (upperRun or lowerRun): " << (b_fail == 0U ? "PASS" : "FAIL")
          << " (violations=" << b_fail << " of " << sp.all.count << ")\n";
      out << "(C) sameArc => q = 2 and earlierArc => q >= 3: "
          << (c_fail == 0U ? "PASS" : "FAIL") << " (sameArc & q != 2: "
          << sp.exc_count[2] << "; earlierArc & q <= 2: " << sp.exc_count[3]
          << "; of " << sp.all.count << ")\n";
      out << "(C') generalized: sameArc => q = L_kind and earlierArc => q >"
             " L_kind (L = 2 test/lockcand, 3 l3, 1 entry23/bandexit): "
          << (sp.exc_count[4] == 0U ? "PASS" : "FAIL") << " (violations="
          << sp.exc_count[4] << " of " << sp.all.count << ")\n";
      out << "    per kind violations (A / B / sameArc&q!=2 / earlierArc&q<=2"
             " / C'):";
      for (std::size_t k = 0U; k < kKinds; ++k)
        out << ' ' << KindName(static_cast<Kind>(k)) << '='
            << sp.exc_kind[0][k] << '/' << sp.exc_kind[1][k] << '/'
            << sp.exc_kind[2][k] << '/' << sp.exc_kind[3][k] << '/'
            << sp.exc_kind[4][k];
      out << '\n';
      out << "\n-- exceptions (first " << kExceptionCap
          << " each; columns as in records.txt) --\n";
      for (std::size_t e = 0U; e < kExcTypes; ++e) {
        out << "  [" << ExcName(e) << "] total=" << sp.exc_count[e] << '\n';
        for (std::size_t i : sp.exc[e]) {
          out << "    ";
          WriteRecord(out, queries[i], visits[queries[i].visit], derived[i]);
        }
      }
    }
    std::cerr << "done: elapsed=" << Seconds(t0) << "s\n";
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
