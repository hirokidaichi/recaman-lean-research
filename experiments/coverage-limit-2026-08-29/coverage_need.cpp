// Independent re-implementation and asymptotic probe for
// ReplayPrefixSuccessorCoverage.
//
//   ReplayPrefixSuccessorCoverage clock cutoff :=
//     forall time < clock, a clock < a time ->
//       exists w <= cutoff, a w = a time + 1 /\ a w <= cutoff
//
// Reframing used here.  The minimal witness for a successor value s is
// first[s], so coverage at `clock` for a given `cutoff` holds iff
//
//   Need(clock) := max over v in {a t : t < clock, v > a clock}
//                    of  max(v + 1, first[v + 1])          <= cutoff
//
// (first[s] = +inf when s has not occurred inside the generation horizon).
// Need(clock) is therefore cutoff-independent and lets us read off
//   C(cutoff) = (least eligible clock >= clockMin with Need > cutoff) - 1
// for every cutoff at once.
//
// Phase A  build the prefix orbit up to Cmax (cheap).
// Phase B  stream the orbit to N steps with an exact-history bitset, recording
//          first occurrences only for values <= maxPrefixValue + 1.
// Phase C  segment tree over value keys, suffix-max query per eligible clock.
//
// Output (stdout): CSV rows for every eligible clock.
// Output (stderr): summary + record table.
//
// Usage: coverage_need [Cmax=100000] [N=100000000] [clockMin=112]
//                      [outRecords=path] [outClocks=path]

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

using u64 = std::uint64_t;
using u32 = std::uint32_t;

static const u64 INF = ~0ULL;

struct BitSet {
  std::vector<u64> w;
  explicit BitSet(u64 bits) : w((bits >> 6) + 2, 0ULL) {}
  inline bool get(u64 v) const {
    u64 i = v >> 6;
    if (i >= w.size()) return false;
    return (w[i] >> (v & 63)) & 1ULL;
  }
  inline void set(u64 v) {
    u64 i = v >> 6;
    if (i >= w.size()) w.resize(i + 1 + (w.size() >> 1), 0ULL);
    w[i] |= 1ULL << (v & 63);
  }
};

// suffix-max segment tree over value keys 0..size-1
struct SegTree {
  u64 n;
  std::vector<u64> t;  // 0 = "no value present"
  explicit SegTree(u64 size) {
    n = 1;
    while (n < size) n <<= 1;
    t.assign(2 * n, 0ULL);
  }
  void update(u64 pos, u64 val) {
    u64 i = pos + n;
    if (t[i] >= val) return;
    t[i] = val;
    for (i >>= 1; i >= 1; i >>= 1) {
      u64 nv = std::max(t[2 * i], t[2 * i + 1]);
      if (t[i] == nv) break;
      t[i] = nv;
      if (i == 1) break;
    }
  }
  // max over [l, n)
  u64 querySuffix(u64 l) const {
    if (l >= n) return 0;
    u64 res = 0, lo = l + n, hi = 2 * n - 1;
    while (lo <= hi) {
      if (lo & 1) res = std::max(res, t[lo++]);
      if (!(hi & 1)) res = std::max(res, t[hi--]);
      if (lo > hi) break;
      lo >>= 1;
      hi >>= 1;
    }
    return res;
  }
};

int main(int argc, char** argv) {
  const u64 Cmax = argc > 1 ? std::stoull(argv[1]) : 100000ULL;
  const u64 N = argc > 2 ? std::stoull(argv[2]) : 100000000ULL;
  const u64 clockMin = argc > 3 ? std::stoull(argv[3]) : 112ULL;
  const char* outRecords = argc > 4 ? argv[4] : nullptr;
  const char* outClocks = argc > 5 ? argv[5] : nullptr;

  // ---------------- Phase A: prefix orbit -------------------------------
  std::vector<u64> orbit(Cmax + 2, 0);
  {
    BitSet seen(8ULL * (Cmax + 4));
    seen.set(0);
    u64 v = 0;
    for (u64 s = 1; s <= Cmax + 1; ++s) {
      bool sub = v > s && !seen.get(v - s);
      v = sub ? v - s : v + s;
      orbit[s] = v;
      seen.set(v);
    }
  }
  u64 maxPrefix = 0;
  for (u64 s = 0; s <= Cmax + 1; ++s) maxPrefix = std::max(maxPrefix, orbit[s]);
  const u64 maxTarget = maxPrefix + 1;
  std::fprintf(stderr, "[A] Cmax=%llu maxPrefixValue=%llu a(Cmax)=%llu\n",
               (unsigned long long)Cmax, (unsigned long long)maxPrefix,
               (unsigned long long)orbit[Cmax]);

  // ---------------- Phase B: deep first-occurrence scan -----------------
  std::vector<u64> first(maxTarget + 2, INF);
  {
    // generous initial bitset; grows if needed
    BitSet seen(4ULL * N + 64);
    seen.set(0);
    first[0] = 0;
    u64 v = 0;
    u64 remaining = maxTarget + 1;  // values 0..maxTarget
    --remaining;                    // 0 done
    for (u64 s = 1; s <= N; ++s) {
      bool sub = v > s && !seen.get(v - s);
      v = sub ? v - s : v + s;
      if (!seen.get(v)) {
        seen.set(v);
        if (v <= maxTarget && first[v] == INF) {
          first[v] = s;
          if (--remaining == 0) {
            std::fprintf(stderr,
                         "[B] all values <= %llu first-seen by step %llu\n",
                         (unsigned long long)maxTarget,
                         (unsigned long long)s);
            break;
          }
        }
      }
      if ((s & 0xFFFFFFFULL) == 0)
        std::fprintf(stderr, "[B] step %llu val %llu remaining %llu\n",
                     (unsigned long long)s, (unsigned long long)v,
                     (unsigned long long)remaining);
    }
    if (remaining)
      std::fprintf(stderr, "[B] horizon N=%llu reached, %llu values unseen\n",
                   (unsigned long long)N, (unsigned long long)remaining);
  }

  // deepest first occurrence among all targets (informational)
  {
    u64 deep = 0, arg = 0, unseen = 0;
    for (u64 x = 0; x <= maxTarget; ++x) {
      if (first[x] == INF) { ++unseen; continue; }
      if (first[x] > deep) { deep = first[x]; arg = x; }
    }
    std::fprintf(stderr, "[B] deepest first occurrence <= %llu : value %llu at t=%llu (unseen=%llu)\n",
                 (unsigned long long)maxTarget, (unsigned long long)arg,
                 (unsigned long long)deep, (unsigned long long)unseen);
  }

  // ---------------- Phase C: Need(clock) --------------------------------
  auto g = [&](u64 v) -> u64 {
    u64 s = v + 1;
    u64 f = (s <= maxTarget) ? first[s] : INF;
    if (f == INF) return INF;
    return std::max(s, f);
  };

  SegTree st(maxPrefix + 2);
  std::FILE* fc = outClocks ? std::fopen(outClocks, "w") : nullptr;
  if (fc) std::fprintf(fc, "clock,anchor,need,worstValue,worstSuccessor,worstFirst\n");
  std::FILE* fr = outRecords ? std::fopen(outRecords, "w") : nullptr;
  if (fr) std::fprintf(fr, "recordIndex,clock,anchor,need,worstValue,worstSuccessor,worstFirst,coveredUpTo\n");

  u64 runMax = 0;
  u64 records = 0;
  u64 eligible = 0;
  u64 prevRecordClock = clockMin - 1;
  std::fprintf(stderr,
               "[C] record table: each row is a new running max of Need\n");
  std::fprintf(stderr,
               "idx,clock,anchor,need,worstValue,worstSucc,worstFirst,C(cutoff<need)\n");

  for (u64 c = 1; c <= Cmax; ++c) {
    // insert value a(c-1) into the structure (prefix = times < c)
    u64 pv = orbit[c - 1];
    u64 gv = g(pv);
    st.update(pv, gv == INF ? INF : gv);
    if (c < clockMin) continue;
    bool elig = (c + 1 < orbit[c]) && (orbit[c + 1] == orbit[c] + (c + 1));
    if (!elig) continue;
    ++eligible;
    u64 anchor = orbit[c];
    u64 need = st.querySuffix(anchor + 1);
    // recover the argmax lazily only when needed (record rows / csv)
    u64 wv = 0, ws = 0, wf = 0;
    bool wantDetail = (need > runMax) || fc;
    if (wantDetail && need > 0) {
      for (u64 t = 0; t < c; ++t) {
        if (orbit[t] <= anchor) continue;
        if (g(orbit[t]) == need) { wv = orbit[t]; ws = wv + 1; wf = (ws <= maxTarget) ? first[ws] : INF; break; }
      }
    }
    if (fc)
      std::fprintf(fc, "%llu,%llu,%s,%llu,%llu,%s\n",
                   (unsigned long long)c, (unsigned long long)anchor,
                   need == INF ? "inf" : std::to_string(need).c_str(),
                   (unsigned long long)wv, (unsigned long long)ws,
                   wf == INF ? "unseen" : std::to_string(wf).c_str());
    if (need > runMax) {
      // C(cutoff) for any cutoff in [runMax, need-1] is c-1
      std::fprintf(stderr, "%llu,%llu,%llu,%s,%llu,%llu,%s,%llu\n",
                   (unsigned long long)records, (unsigned long long)c,
                   (unsigned long long)anchor,
                   need == INF ? "inf" : std::to_string(need).c_str(),
                   (unsigned long long)wv, (unsigned long long)ws,
                   wf == INF ? "unseen" : std::to_string(wf).c_str(),
                   (unsigned long long)(c - 1));
      if (fr)
        std::fprintf(fr, "%llu,%llu,%llu,%s,%llu,%llu,%s,%llu\n",
                     (unsigned long long)records, (unsigned long long)c,
                     (unsigned long long)anchor,
                     need == INF ? "inf" : std::to_string(need).c_str(),
                     (unsigned long long)wv, (unsigned long long)ws,
                     wf == INF ? "unseen" : std::to_string(wf).c_str(),
                     (unsigned long long)(c - 1));
      runMax = need;
      ++records;
      prevRecordClock = c;
      if (need == INF) {
        std::fprintf(stderr,
                     "[C] clock %llu needs an unseen successor: no finite cutoff works beyond here\n",
                     (unsigned long long)c);
        break;
      }
    }
  }
  (void)prevRecordClock;
  if (fc) std::fclose(fc);
  if (fr) std::fclose(fr);
  std::fprintf(stderr, "[C] eligible clocks in [%llu,%llu] = %llu, records = %llu\n",
               (unsigned long long)clockMin, (unsigned long long)Cmax,
               (unsigned long long)eligible, (unsigned long long)records);
  return 0;
}
