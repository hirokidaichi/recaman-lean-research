// H-20260906-05: independent one-step orbit generator and arc/run detector.
// No initial blockers other than {0,z}; no history intervention after clock 0.
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Nat = std::uint64_t;
using Clock = std::chrono::steady_clock;

class Seen {
 public:
  bool Contains(Nat x) const {
    const Nat i = x / 64;
    return i < bits_.size() && ((bits_[i] >> (x % 64)) & 1U) != 0;
  }
  void Insert(Nat x) {
    const Nat i = x / 64;
    if (i >= bits_.size()) bits_.resize(2 * (i + 1), 0);
    bits_[i] |= Nat{1} << (x % 64);
  }
 private:
  std::vector<Nat> bits_{0};
};

struct Record {
  Nat c = 0, v = 0, teeth = 0, j = 0, h = 0, run_start = 0, next = 0;
  bool has_run = false, blocked = false;
};

struct Census {
  Nat eligible = 0, violations = 0, identity_failures = 0, arcs = 0;
  bool finished = false;
  Record witness;
  Nat witness_wrap = 0;
};

Census Run(Nat z, Nat horizon, Clock::time_point deadline, std::ostream* dump) {
  Seen seen;
  seen.Insert(0);
  seen.Insert(z);
  Nat value = z, previous_residue = 0;
  // run=1: at level one; run=2: its following addition at level two.
  unsigned run = 0;
  Nat run_pairs = 0, run_height = 0, run_start = 0;
  Nat last_late_clock = 0, last_late_value = 0;
  Record comb, pending;
  bool has_pending = false;
  std::vector<Record> continued_in_arc;
  Census census;
  for (Nat t = 1; t <= horizon; ++t) {
    if ((t & 32767U) == 0 && Clock::now() >= deadline) return census;
    const bool subtract = value > t && !seen.Contains(value - t);
    value = subtract ? value - t : value + t;
    seen.Insert(value);
    const Nat q = value / t, r = value % t;
    if (t > 1 && r > previous_residue) {
      ++census.arcs;
      for (const Record& rec : continued_in_arc) {
        if (!(rec.has_run && rec.blocked && rec.teeth == 1)) continue;
        ++census.eligible;
        census.identity_failures += rec.h != rec.v + 1 + 3 * rec.j;
        if (dump) *dump << rec.c << ' ' << rec.v << ' ' << rec.j << ' '
                        << rec.h << ' ' << rec.next << '\n';
        if (16 * rec.v < 7 * rec.h) {
          ++census.violations;
          census.witness = rec;
          census.witness_wrap = t;
        }
      }
      continued_in_arc.clear();
      has_pending = false;
      if (census.violations != 0) return census;
    }
    if (value < t) {
      if (has_pending) {
        pending.next = t;
        continued_in_arc.push_back(pending);
        has_pending = false;
      }
      if (t >= 2 && last_late_clock == t - 2 && last_late_value == value + 1) {
        ++comb.teeth;
      } else {
        comb = Record{t, value, 1, run_pairs, run_height, run_start, 0,
                      run == 1, false};
      }
      last_late_clock = t;
      last_late_value = value;
      if (seen.Contains(value - 1)) {
        pending = comb;
        pending.c = t;
        pending.v = value;
        pending.blocked = seen.Contains(2 * t + value + 2);
        has_pending = true;
      }
    }
    if (q == 1) {
      if (subtract && run == 2) {
        ++run_pairs;
      } else {
        run_pairs = 0;
        run_height = value - t;
        run_start = t;
      }
      run = 1;
    } else if (q == 2 && !subtract && run == 1) {
      run = 2;
    } else {
      run = 0;
    }
    previous_residue = r;
  }
  census.finished = true;
  return census;
}

int main(int argc, char** argv) {
  try {
    if (argc != 5) throw std::invalid_argument(
      "usage: HORIZON MAX_INITIAL SECONDS CANONICAL_RECORDS");
    const Nat horizon = std::stoull(argv[1]);
    const Nat max_initial = std::stoull(argv[2]);
    const Nat seconds = std::stoull(argv[3]);
    if (horizon > 2000000 || max_initial > 20000 || seconds > 900)
      throw std::invalid_argument("arguments exceed frozen protocol");
    const auto start = Clock::now(), deadline = start + std::chrono::seconds(seconds);
    std::ofstream dump(argv[4]);
    if (!dump) throw std::runtime_error("cannot open canonical record output");
    Nat orbits[2] = {}, eligible[2] = {}, arcs[2] = {};
    std::cout << "protocol=H-20260906-05 horizon=" << horizon
              << " max_initial=" << max_initial << " seconds=" << seconds << '\n';
    for (Nat z = 0; z <= max_initial; ++z) {
      const Census c = Run(z, horizon, deadline, z == 0 ? &dump : nullptr);
      if (c.identity_failures != 0) throw std::runtime_error("run identity mismatch");
      if (c.violations != 0) {
        const Record& r = c.witness;
        std::cout << "REFUTED initial=" << z << " c=" << r.c << " v=" << r.v
                  << " T=" << r.teeth << " J=" << r.j << " hPrev=" << r.h
                  << " runStart=" << r.run_start << " nextLanding=" << r.next
                  << " wrap=" << c.witness_wrap << " lhs=" << 7 * r.h
                  << " rhs=" << 16 * r.v << std::endl;
        return 0;
      }
      if (!c.finished) {
        std::cout << "TIME_CAP unfinished_initial=" << z << std::endl;
        break;
      }
      const unsigned split = z <= 1000 ? 0 : 1;
      ++orbits[split];
      eligible[split] += c.eligible;
      arcs[split] += c.arcs;
      if (z % 100 == 0) std::cout << "progress initial=" << z
        << " eligible=" << c.eligible << " arcs=" << c.arcs << " elapsed="
        << std::chrono::duration<double>(Clock::now() - start).count() << std::endl;
    }
    for (unsigned split = 0; split < 2; ++split)
      std::cout << (split == 0 ? "discovery" : "holdout")
                << " completed_orbits=" << orbits[split]
                << " eligible_records=" << eligible[split]
                << " completed_arcs=" << arcs[split]
                << " violations=0 identity_failures=0\n";
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << '\n';
    return 1;
  }
}
