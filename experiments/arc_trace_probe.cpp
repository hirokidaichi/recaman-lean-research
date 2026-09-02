// Arc trace probe of the canonical Recaman orbit.
//
// A plain (one clock per iteration) simulator with the interval-set history
// of run_length_recaman_simulator.cpp, extended with Chaffin's arc detector
// and step-level traces of the deep arcs.
//
// Definitions (exact).  a(0) = 0, history {0}.  At clock n >= 1 the candidate
// is a(n-1) - n; subtract iff a(n-1) > n and the candidate is not in the
// history, else add n.  Write a(n) = k(n) * n + r(n) with 0 <= r(n) < n
// (k = quotient, r = residue a(n) mod n).  Both steps send r to r - k as long
// as r >= k (a(n) +- (n+1) = (k+-1)(n+1) + (r-k)), so r is nonincreasing until
// it wraps to r - k + n + 1.  An arc (Chaffin, OEIS A393814/A393815) is the
// stretch between two consecutive increases of r; the wrap clock starts the
// next arc.  The landing of an arc is its minimum value a(n), the landing
// index the (first) clock attaining it.  Height h(n) = a(n) - n (signed).
// Late landing: a(n) < n, i.e. k(n) = 0 (always a subtraction).  Band landing:
// a subtraction with a(n) >= n.  Deep arc: landing value * 10000 < index.
//
// Trace.  The trace of an arc starts at the first clock of the arc with
// r(n) * 1000 < n.  At k = 1 clocks this is exactly h(n) * 1000 < n; at k = 0
// clocks it is a(n) * 1000 < n; clocks with k >= 2 (h >= n) enter the trace
// only after it has started.  (The literal condition h < n/1000 also holds at
// every late landing, including the ones with a(n) ~ n/2 near the start of an
// arc, which would put whole arcs into the trace; the residue condition keeps
// the trace to the final descent, and r is nonincreasing so the trace never
// stops before the arc ends.)  The trace keeps the first kHead records and a
// ring of the last 2^RING_LOG2 records; if the traced part is longer, the
// middle is omitted with a count.
//
// Per traced late landing: value mod 3, whether value-1 is unvisited at that
// time, the next 8 orbit values with their step types, the first later clock
// of the same arc with 0 < h < value (if any), and the next late landing of
// the same arc (if any).
//
// Output (all in OUTDIR): arcs_all.txt (one line per completed arc),
// deep_arcs.txt (deep arcs with the last 16 records of each), trace_<index>.txt
// and lates_<index>.txt per deep arc (index = landing index), summary.txt.
//
// Build: c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
//          experiments/arc_trace_probe.cpp -o /tmp/arctrace
// Run:   /tmp/arctrace HORIZON OUTDIR [RING_LOG2=23]

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cmath>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using Nat = std::uint64_t;
using Int = std::int64_t;

class IntervalSet {
 public:
  enum Slot : std::size_t { kSub = 0, kAdd = 1 };
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
  std::size_t hint_[2] = {0U, 0U};
};

constexpr Nat kFSub = 1U, kFHasCand = 2U, kFLate = 4U, kFBelowHole = 8U;
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

// Prints one trace line.  Columns: clock a h k r step cand candState class
// [mod3= below=] [UP] [POP].  UP: k >= 2 after a record with k <= 1 (the
// height jumps from below n/1000 to at least n); POP: k >= 3 (the orbit has
// left the ping-pong band by two additions in a row).
void PrintRec(std::ostream& out, const Rec& rec, bool have_prev_k, Nat prev_k) {
  const Nat flags = rec.Flags();
  const Nat k = rec.value / rec.clock, r = rec.value % rec.clock;
  const Int h = static_cast<Int>(rec.value) - static_cast<Int>(rec.clock);
  const bool sub = (flags & kFSub) != 0U, has_cand = (flags & kFHasCand) != 0U,
             late = (flags & kFLate) != 0U;
  out << rec.clock << ' ' << rec.value << ' ' << h << ' ' << k << ' ' << r
      << ' ' << (sub ? 'S' : 'A') << ' ';
  if (has_cand)
    out << rec.Prev() - rec.clock << ' ' << (sub ? "fresh" : "blocked");
  else
    out << "- none";
  out << ' ' << (sub ? (late ? "late" : "band") : "-");
  if (late)
    out << " mod3=" << rec.value % 3U << " below="
        << (((flags & kFBelowHole) != 0U) ? "hole" : "visited");
  if (have_prev_k && k >= 2U && prev_k <= 1U) out << " UP";
  if (k >= 3U) out << " POP";
  out << '\n';
}

constexpr std::size_t kHead = 4096U;

class TraceBuffer {
 public:
  explicit TraceBuffer(std::size_t ring_log2) : ring_(std::size_t{1} << ring_log2) {}

  void Push(const Rec& rec) {
    ++total_;
    if (head_.size() < kHead) {
      head_.push_back(rec);
      return;
    }
    ring_[pos_] = rec;
    pos_ = (pos_ + 1U) % ring_.size();
    if (count_ < ring_.size()) ++count_;
  }
  void Clear() {
    head_.clear();
    total_ = count_ = pos_ = 0U;
  }
  Nat Total() const { return total_; }
  Nat Omitted() const { return total_ - head_.size() - count_; }

  // Writes every kept record; the omitted middle is marked.
  void Write(std::ostream& out) const {
    bool have_prev = false;
    Nat prev_k = 0U;
    for (const Rec& rec : head_) {
      PrintRec(out, rec, have_prev, prev_k);
      have_prev = true;
      prev_k = rec.value / rec.clock;
    }
    if (Omitted() != 0U) {
      out << "... " << Omitted() << " records omitted ...\n";
      have_prev = false;
    }
    const std::size_t start = (pos_ + ring_.size() - count_) % ring_.size();
    for (std::size_t i = 0U; i < count_; ++i) {
      const Rec& rec = ring_[(start + i) % ring_.size()];
      PrintRec(out, rec, have_prev, prev_k);
      have_prev = true;
      prev_k = rec.value / rec.clock;
    }
  }

 private:
  std::vector<Rec> head_;
  std::vector<Rec> ring_;
  std::size_t pos_ = 0U, count_ = 0U;
  Nat total_ = 0U;
};

constexpr std::size_t kTail = 16U;

struct LateInfo {
  Nat clock = 0U, value = 0U;
  bool below_hole = false;
  std::array<Nat, 8> next_value{};
  std::array<char, 8> next_type{};  // A: addition, B: band landing, L: late
  std::size_t next_filled = 0U;
  bool next_crossed_arc = false;   // the 8 steps ran into the next arc
  Nat small_clock = 0U, small_h = 0U;  // first later clock with 0 < h < value
  Nat next_late_clock = 0U, next_late_value = 0U;
};

struct Arc {
  Nat ordinal = 0U;
  Nat start_clock = 0U, start_value = 0U;
  Nat min_value = 0U, min_clock = 0U;
  Nat late_total = 0U, late_deep = 0U;
  Nat last_late_clock = 0U, last_late_value = 0U;
  Nat trace_from = 0U;
  Nat steps = 0U;
  Nat k_hist[4] = {};  // traced clocks with k = 0, 1, 2, >= 3
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

class Probe {
 public:
  Probe(Nat horizon, std::string outdir, std::size_t ring_log2)
      : horizon_(horizon), outdir_(std::move(outdir)), trace_(ring_log2),
        start_(std::chrono::steady_clock::now()) {
    all_.open(outdir_ + "/arcs_all.txt");
    deep_.open(outdir_ + "/deep_arcs.txt");
    if (!all_ || !deep_) throw std::runtime_error("cannot open output files");
    all_ << "# ordinal startClock endClock startValue landingIndex landingValue"
            " depth lateTotal lateDeep lastLateClock lastLateValue traceFrom"
            " traceLen k0 k1 k2 k3+ nextArcValue deep?\n";
    deep_ << "# deep arcs (landingValue * 10000 < landingIndex); after each"
             " header line the last " << kTail << " records of the arc and the"
             " first record of the next arc\n";
  }

  void Run() {
    while (clock_ <= horizon_) Step();
  }

  void WriteSummary() const {
    std::ofstream out(outdir_ + "/summary.txt");
    out << "arc-trace-probe horizon=" << horizon_ << " elapsed=" << Elapsed()
        << "s intervals=" << seen_.Count() << " mex=" << seen_.Mex()
        << " finalValue=" << value_ << '\n';
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
    out << "completed arcs=" << landings_.size() << " deep=" << deep_count_
        << '\n';
    out << "open arc at horizon: start=" << arc_.start_clock
        << " minValue=" << arc_.min_value << " minClock=" << arc_.min_clock
        << " lateTotal=" << arc_.late_total << " traceFrom=" << arc_.trace_from
        << '\n';
    out << "landings with value < 1e7 and index >= 1e8:\n";
    for (const Landing& l : landings_)
      if (l.index >= 100000000ULL && l.value < 10000000ULL)
        out << "  " << l.index << ' ' << l.value << " log10index="
            << std::log10(static_cast<double>(l.index)) << '\n';
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
    Nat flags = (subtract ? kFSub : 0U) | (has_cand ? kFHasCand : 0U) |
                (late ? kFLate : 0U);
    if (late && !seen_.Contains(value_ - 1U, IntervalSet::kSub))
      flags |= kFBelowHole;
    const Rec rec = MakeRec(clock, value_, prev, flags);

    if (in_arc_ && r > prev_residue_) {
      FinishArc(clock, rec);
      StartArc(clock);
    } else if (!in_arc_) {
      StartArc(clock);
    }
    prev_residue_ = r;

    ++arc_.steps;
    if (value_ < arc_.min_value) {
      arc_.min_value = value_;
      arc_.min_clock = clock;
    }
    if (late) {
      ++arc_.late_total;
      arc_.last_late_clock = clock;
      arc_.last_late_value = value_;
    }
    if (arc_.trace_from == 0U && r * 1000U < clock) arc_.trace_from = clock;
    tail_[tail_pos_] = rec;
    tail_pos_ = (tail_pos_ + 1U) % kTail;
    if (tail_count_ < kTail) ++tail_count_;

    if (arc_.trace_from != 0U) {
      trace_.Push(rec);
      ++arc_.k_hist[k >= 3U ? 3U : k];
      // Next-8 fill for earlier late landings.
      const char type = subtract ? (late ? 'L' : 'B') : 'A';
      std::size_t w = 0U;
      for (std::size_t i = 0U; i < pending_.size(); ++i) {
        LateInfo& info = lates_[pending_[i]];
        info.next_value[info.next_filled] = value_;
        info.next_type[info.next_filled] = type;
        ++info.next_filled;
        if (info.next_filled < 8U) pending_[w++] = pending_[i];
      }
      pending_.resize(w);
      // Resolution of "later clock with 0 < h < value" (k = 1, h = r > 0).
      if (k == 1U && r > 0U) {
        while (unresolved_ < lates_.size() && lates_[unresolved_].value > r) {
          lates_[unresolved_].small_clock = clock;
          lates_[unresolved_].small_h = r;
          ++unresolved_;
        }
      }
      if (late) {
        ++arc_.late_deep;
        if (!lates_.empty()) {
          lates_.back().next_late_clock = clock;
          lates_.back().next_late_value = value_;
        }
        if (lates_.size() < kMaxLates) {
          LateInfo info;
          info.clock = clock;
          info.value = value_;
          info.below_hole = (flags & kFBelowHole) != 0U;
          lates_.push_back(info);
          pending_.push_back(lates_.size() - 1U);
        } else {
          ++lates_dropped_;
        }
      }
    }
    if (clock == next_progress_) {
      std::cerr << "progress clock=" << clock << " value=" << value_
                << " intervals=" << seen_.Count() << " arcs="
                << landings_.size() << " deep=" << deep_count_
                << " elapsed=" << Elapsed() << "s\n";
      next_progress_ += kProgressStep;
    }
    clock_ = clock + 1U;
  }

  void StartArc(Nat clock) {
    in_arc_ = true;
    arc_ = Arc{};
    arc_.ordinal = landings_.size() + 1U;
    arc_.start_clock = clock;
    arc_.start_value = value_;
    arc_.min_value = value_;
    arc_.min_clock = clock;
    tail_count_ = tail_pos_ = 0U;
  }

  // The arc consists of the clocks [arc_.start_clock, wrap_clock - 1];
  // `next` is the record of the wrap clock (first clock of the next arc).
  void FinishArc(Nat wrap_clock, const Rec& next) {
    const Nat index = arc_.min_clock, value = arc_.min_value;
    const bool deep = value * 10000U < index;
    const double depth = std::log10(static_cast<double>(index)) -
                         std::log10(static_cast<double>(value));
    landings_.push_back(Landing{index, value});
    all_ << arc_.ordinal << ' ' << arc_.start_clock << ' ' << wrap_clock - 1U
         << ' ' << arc_.start_value << ' ' << index << ' ' << value << ' '
         << depth << ' ' << arc_.late_total << ' ' << arc_.late_deep << ' '
         << arc_.last_late_clock << ' ' << arc_.last_late_value << ' '
         << arc_.trace_from << ' ' << trace_.Total() << ' ' << arc_.k_hist[0]
         << ' ' << arc_.k_hist[1] << ' ' << arc_.k_hist[2] << ' '
         << arc_.k_hist[3] << ' ' << next.value << ' '
         << (deep ? "DEEP" : "-") << '\n';
    all_.flush();
    if (deep) {
      ++deep_count_;
      deep_ << "arc " << arc_.ordinal << " start=" << arc_.start_clock
            << " end=" << wrap_clock - 1U << " startValue=" << arc_.start_value
            << " landing=" << index << '=' << value << " depth=" << depth
            << " lateTotal=" << arc_.late_total << " lateDeep="
            << arc_.late_deep << " traceFrom=" << arc_.trace_from
            << " traceLen=" << trace_.Total() << " omitted=" << trace_.Omitted()
            << " k0=" << arc_.k_hist[0] << " k1=" << arc_.k_hist[1]
            << " k2=" << arc_.k_hist[2] << " k3+=" << arc_.k_hist[3]
            << " stepsAfterLanding=" << wrap_clock - 1U - index
            << " latesDropped=" << lates_dropped_ << '\n';
      const std::size_t start = (tail_pos_ + kTail - tail_count_) % kTail;
      bool have_prev = false;
      Nat prev_k = 0U;
      for (std::size_t i = 0U; i < tail_count_; ++i) {
        const Rec& rec = tail_[(start + i) % kTail];
        deep_ << "  end ";
        PrintRec(deep_, rec, have_prev, prev_k);
        have_prev = true;
        prev_k = rec.value / rec.clock;
      }
      deep_ << "  next ";
      PrintRec(deep_, next, have_prev, prev_k);
      deep_.flush();

      std::ofstream tr(outdir_ + "/trace_" + std::to_string(index) + ".txt");
      tr << "# arc " << arc_.ordinal << " clocks " << arc_.start_clock << ".."
         << wrap_clock - 1U << " landing " << index << '=' << value
         << " depth " << depth << " traceFrom " << arc_.trace_from << '\n';
      tr << "# clock a h k r step cand candState class [mod3= below=] [UP]"
            " [POP]\n";
      trace_.Write(tr);
      tr << "# next arc starts: ";
      PrintRec(tr, next, false, 0U);

      std::ofstream lt(outdir_ + "/lates_" + std::to_string(index) + ".txt");
      lt << "# late landings in the traced part of arc " << arc_.ordinal
         << " (landing " << index << '=' << value << "); " << lates_.size()
         << " listed, " << lates_dropped_ << " dropped\n";
      lt << "# clock value mod3 below next8(value:type A=add B=band L=late)"
            " small(first later clock of the arc with 0<h<value: clock:h or"
            " none) nextLate(clock:value or none)\n";
      for (const LateInfo& info : lates_) {
        lt << info.clock << ' ' << info.value << ' ' << info.value % 3U << ' '
           << (info.below_hole ? "hole" : "visited") << " next8=";
        for (std::size_t i = 0U; i < info.next_filled; ++i)
          lt << (i == 0U ? "" : ",") << info.next_value[i] << ':'
             << info.next_type[i];
        if (info.next_filled < 8U) lt << ",|arcEnd";
        lt << " small=";
        if (info.small_clock != 0U)
          lt << info.small_clock << ':' << info.small_h;
        else
          lt << "none";
        lt << " nextLate=";
        if (info.next_late_clock != 0U)
          lt << info.next_late_clock << ':' << info.next_late_value;
        else
          lt << "none";
        lt << '\n';
      }
    }
    trace_.Clear();
    lates_.clear();
    pending_.clear();
    unresolved_ = 0U;
    lates_dropped_ = 0U;
    in_arc_ = false;
  }

  static constexpr std::size_t kMaxLates = 4000000U;

  const Nat horizon_;
  const std::string outdir_;
  TraceBuffer trace_;
  const std::chrono::steady_clock::time_point start_;
  std::ofstream all_, deep_;
  IntervalSet seen_;
  Nat clock_ = 1U;
  Nat value_ = 0U;
  bool in_arc_ = false;
  Nat prev_residue_ = 0U;
  Arc arc_;
  std::array<Rec, kTail> tail_{};
  std::size_t tail_pos_ = 0U, tail_count_ = 0U;
  std::vector<LateInfo> lates_;
  std::vector<std::size_t> pending_;
  std::size_t unresolved_ = 0U;
  Nat lates_dropped_ = 0U;
  std::vector<Landing> landings_;
  Nat deep_count_ = 0U;
  Nat next_progress_ = kProgressStep;
};

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc < 3) throw std::invalid_argument("usage: HORIZON OUTDIR [RING_LOG2]");
    const Nat horizon = std::stoull(argv[1]);
    if (horizon < 10U) throw std::invalid_argument("horizon must be >= 10");
    const std::string outdir = argv[2];
    const std::size_t ring_log2 = argc >= 4 ? std::stoul(argv[3]) : 23U;
    if (ring_log2 > 27U) throw std::invalid_argument("RING_LOG2 must be <= 27");
    Probe probe(horizon, outdir, ring_log2);
    probe.Run();
    probe.WriteSummary();
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
