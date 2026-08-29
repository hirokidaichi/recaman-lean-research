// Asymptotic probe for ReplayPrefixSuccessorCoverage.
//
// Loads a deep first-occurrence table (produced by deep_first) and computes,
// for every numerically eligible replay clock,
//
//   Need(clock) = max over v in {a t : t < clock, v > a clock}
//                   of  max(v + 1, first[v + 1])
//
// so that coverage at `clock` holds for cutoff X iff Need(clock) <= X, and
//   C(X) = (least eligible clock >= clockMin with Need > X) - 1.
//
// Usage: coverage_scan firstTable M Cmax clockMin outPrefix
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
using u64 = std::uint64_t;
using u32 = std::uint32_t;
static const u64 INF = ~0ULL;

struct BitSet {
  std::vector<u64> w;
  explicit BitSet(u64 bits) : w((bits >> 6) + 4, 0ULL) {}
  bool get(u64 v) const { u64 i = v >> 6; return i < w.size() && ((w[i] >> (v & 63)) & 1ULL); }
  void set(u64 v) { u64 i = v >> 6; if (i >= w.size()) w.resize(i + 1 + (w.size() >> 1), 0ULL); w[i] |= 1ULL << (v & 63); }
};

struct Fenwick {
  u64 n; std::vector<u32> t;
  explicit Fenwick(u64 size) : n(size + 1), t(size + 2, 0) {}
  void add(u64 i) { for (u64 x = i + 1; x < t.size(); x += x & (~x + 1)) ++t[x]; }
  u64 sum(u64 i) const { u64 r = 0; for (u64 x = i + 1; x > 0; x -= x & (~x + 1)) r += t[x]; return r; }
};

struct SegTree {
  u64 n; std::vector<u64> t;
  explicit SegTree(u64 size) { n = 1; while (n < size) n <<= 1; t.assign(2 * n, 0ULL); }
  void update(u64 pos, u64 val) {
    u64 i = pos + n; if (t[i] >= val) return; t[i] = val;
    while (i > 1) { i >>= 1; u64 nv = std::max(t[2 * i], t[2 * i + 1]); if (t[i] == nv) break; t[i] = nv; }
  }
  u64 querySuffix(u64 l) const {
    if (l >= n) return 0; u64 res = 0, lo = l + n, hi = 2 * n - 1;
    while (lo <= hi) { if (lo & 1) res = std::max(res, t[lo++]); if (!(hi & 1)) res = std::max(res, t[hi--]);
      if (lo > hi) break; lo >>= 1; hi >>= 1; }
    return res;
  }
};

int main(int argc, char** argv) {
  if (argc < 6) { std::fprintf(stderr, "usage: coverage_scan firstTable M Cmax clockMin outPrefix\n"); return 2; }
  const char* tablePath = argv[1];
  const u64 M = std::strtoull(argv[2], 0, 10);
  const u64 Cmax = std::strtoull(argv[3], 0, 10);
  const u64 clockMin = std::strtoull(argv[4], 0, 10);
  const std::string outPrefix = argv[5];

  std::vector<u64> first(M + 1, INF);
  { std::FILE* f = std::fopen(tablePath, "rb");
    if (!f) { std::fprintf(stderr, "cannot open %s\n", tablePath); return 2; }
    if (std::fread(first.data(), sizeof(u64), M + 1, f) != M + 1) { std::fprintf(stderr, "short table\n"); return 2; }
    std::fclose(f); }

  std::vector<u64> orbit(Cmax + 2, 0);
  { BitSet seen(8ULL * (Cmax + 8)); seen.set(0); u64 v = 0;
    for (u64 s = 1; s <= Cmax + 1; ++s) { bool sub = v > s && !seen.get(v - s); v = sub ? v - s : v + s; orbit[s] = v; seen.set(v); } }
  u64 maxPrefix = 0; for (u64 s = 0; s <= Cmax + 1; ++s) maxPrefix = std::max(maxPrefix, orbit[s]);
  if (maxPrefix + 1 > M) { std::fprintf(stderr, "table too small: need M >= %llu\n", (unsigned long long)(maxPrefix + 1)); return 2; }
  std::fprintf(stderr, "Cmax=%llu maxPrefixValue=%llu\n", (unsigned long long)Cmax, (unsigned long long)maxPrefix);

  auto g = [&](u64 v) -> u64 { u64 s = v + 1; u64 f = first[s]; return f == INF ? INF : std::max(s, f); };

  SegTree st(maxPrefix + 2);
  Fenwick fw(maxPrefix + 2);
  u64 inserted = 0;
  std::FILE* fr = std::fopen((outPrefix + "_records.csv").c_str(), "w");
  std::fprintf(fr, "recordIndex,blockingClock,anchor,need,worstValue,worstSuccessor,worstFirst,"
                   "coveredUpTo,prefixAboveAnchor,uncoveredAtPrevCutoff,prevCutoff\n");
  std::FILE* fa = std::fopen((outPrefix + "_all.csv").c_str(), "w");
  std::fprintf(fa, "clock,anchor,isRecordCrossing,prefixAboveAnchor,need,worstSuccessor\n");

  u64 runMax = 0, records = 0, eligible = 0, recordCrossings = 0;
  u64 runningMaxValue = 0;  // max a(t) for t < clock
  for (u64 c = 1; c <= Cmax; ++c) {
    u64 pv = orbit[c - 1];
    st.update(pv, g(pv));
    fw.add(pv); ++inserted;
    runningMaxValue = std::max(runningMaxValue, pv);
    if (c < clockMin) continue;
    if (!((c + 1 < orbit[c]) && (orbit[c + 1] == orbit[c] + (c + 1)))) continue;
    ++eligible;
    const u64 anchor = orbit[c];
    const bool isRecord = anchor > runningMaxValue;
    if (isRecord) ++recordCrossings;
    const u64 need = st.querySuffix(anchor + 1);
    const u64 above = inserted - fw.sum(anchor);
    u64 argSucc = 0;
    if (need > 0) {
      for (u64 t = 0; t < c; ++t) { if (orbit[t] <= anchor) continue; if (g(orbit[t]) == need) { argSucc = orbit[t] + 1; break; } }
    }
    std::fprintf(fa, "%llu,%llu,%d,%llu,%s,%llu\n", (unsigned long long)c, (unsigned long long)anchor,
                 isRecord ? 1 : 0, (unsigned long long)above,
                 need == INF ? "inf" : (need == 0 ? "0" : std::to_string(need).c_str()),
                 (unsigned long long)argSucc);
    if (need > runMax) {
      u64 wv = 0, ws = 0, wf = 0, unc = 0;
      for (u64 t = 0; t < c; ++t) {
        if (orbit[t] <= anchor) continue;
        u64 gg = g(orbit[t]);
        if (gg > runMax) ++unc;
        if (gg == need && wv == 0) { wv = orbit[t]; ws = wv + 1; wf = first[ws]; }
      }
      std::fprintf(fr, "%llu,%llu,%llu,%s,%llu,%llu,%s,%llu,%llu,%llu,%llu\n",
                   (unsigned long long)records, (unsigned long long)c, (unsigned long long)anchor,
                   need == INF ? "inf" : std::to_string(need).c_str(),
                   (unsigned long long)wv, (unsigned long long)ws,
                   wf == INF ? "unseen" : std::to_string(wf).c_str(),
                   (unsigned long long)(c - 1), (unsigned long long)above,
                   (unsigned long long)unc, (unsigned long long)runMax);
      std::fflush(fr);
      std::fprintf(stderr, "record %llu: clock=%llu anchor=%llu need=%s succ=%llu first=%s C(cutoff in [%llu,need))=%llu above=%llu uncovered=%llu\n",
                   (unsigned long long)records, (unsigned long long)c, (unsigned long long)anchor,
                   need == INF ? "inf" : std::to_string(need).c_str(), (unsigned long long)ws,
                   wf == INF ? "unseen" : std::to_string(wf).c_str(),
                   (unsigned long long)runMax, (unsigned long long)(c - 1),
                   (unsigned long long)above, (unsigned long long)unc);
      runMax = need; ++records;
      if (need == INF) std::fprintf(stderr, "HARD WALL at clock %llu: successor %llu never occurs inside the table horizon\n",
                                    (unsigned long long)c, (unsigned long long)ws);
    }
  }
  std::fclose(fr); std::fclose(fa);
  std::fprintf(stderr, "eligible=%llu recordCrossings=%llu records=%llu finalRunMax=%s\n",
               (unsigned long long)eligible, (unsigned long long)recordCrossings, (unsigned long long)records,
               runMax == INF ? "inf" : std::to_string(runMax).c_str());
  return 0;
}
