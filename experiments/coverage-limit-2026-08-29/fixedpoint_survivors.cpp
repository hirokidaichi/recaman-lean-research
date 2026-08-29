// Replay fixed-point survivor census against the real orbit.
//
// Necessary conditions for an exact replay fixed point at crossing clock C
// with missing target T (as used by the Lean development):
//   (2) C + 1 < a(C)
//   (3) a(C+1) = a(C) + (C+1)            forced addition
//   (4) a(C) < T <= a(C+1)               band straddles the target
//   (5) T never occurs in the orbit      (proxy: unseen inside the horizon)
//   (6) a(C) is not an orbit record      (a record crossing has empty prefix
//                                         above the anchor)
// This program counts, for every clock up to Cmax, how many band targets are
// still "never seen" inside the deep first-occurrence horizon, and crosses the
// result with the prefix-successor coverage verdict.
//
// Usage: fixedpoint_survivors firstTable M Cmax outCsv
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
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

int main(int argc, char** argv) {
  if (argc < 5) { std::fprintf(stderr, "usage: fixedpoint_survivors firstTable M Cmax outCsv\n"); return 2; }
  const char* tablePath = argv[1];
  const u64 M = std::strtoull(argv[2], 0, 10);
  const u64 Cmax = std::strtoull(argv[3], 0, 10);
  const char* outCsv = argv[4];

  std::vector<u64> first(M + 1, INF);
  { std::FILE* f = std::fopen(tablePath, "rb");
    if (!f || std::fread(first.data(), sizeof(u64), M + 1, f) != M + 1) { std::fprintf(stderr, "table read failed\n"); return 2; }
    std::fclose(f); }

  // prefix count of "never seen inside horizon" values
  std::vector<u32> unseenPrefix(M + 2, 0);
  for (u64 v = 0; v <= M; ++v) unseenPrefix[v + 1] = unseenPrefix[v] + (first[v] == INF ? 1u : 0u);

  std::vector<u64> orbit(Cmax + 2, 0);
  { BitSet seen(8ULL * (Cmax + 8)); seen.set(0); u64 v = 0;
    for (u64 s = 1; s <= Cmax + 1; ++s) { bool sub = v > s && !seen.get(v - s); v = sub ? v - s : v + s; orbit[s] = v; seen.set(v); } }
  u64 maxPrefix = 0; for (u64 s = 0; s <= Cmax + 1; ++s) maxPrefix = std::max(maxPrefix, orbit[s]);
  if (maxPrefix > M) { std::fprintf(stderr, "table too small (need %llu)\n", (unsigned long long)maxPrefix); return 2; }

  std::FILE* fo = std::fopen(outCsv, "w");
  std::fprintf(fo, "clock,anchor,bandWidth,unseenTargetsInBand,isRecordCrossing\n");
  u64 cond2 = 0, cond23 = 0, withUnseen = 0, pairs = 0, nonRecordWithUnseen = 0;
  u64 runningMax = 0;
  std::vector<u64> decadeClocks(8, 0), decadePairs(8, 0);
  for (u64 c = 1; c <= Cmax; ++c) {
    runningMax = std::max(runningMax, orbit[c - 1]);
    if (!(c + 1 < orbit[c])) continue;
    ++cond2;
    if (orbit[c + 1] != orbit[c] + (c + 1)) continue;
    ++cond23;
    const u64 lo = orbit[c], hi = orbit[c + 1];
    const u64 nUnseen = unseenPrefix[hi + 1] - unseenPrefix[lo + 1];
    const bool isRecord = orbit[c] > runningMax;
    if (nUnseen) { ++withUnseen; pairs += nUnseen; if (!isRecord) ++nonRecordWithUnseen; }
    std::fprintf(fo, "%llu,%llu,%llu,%llu,%d\n", (unsigned long long)c, (unsigned long long)lo,
                 (unsigned long long)(c + 1), (unsigned long long)nUnseen, isRecord ? 1 : 0);
    u64 d = 0, x = c; while (x >= 10) { x /= 10; ++d; } if (d > 7) d = 7;
    decadeClocks[d]++; decadePairs[d] += nUnseen;
  }
  std::fclose(fo);
  std::fprintf(stderr, "Cmax=%llu  cond(2)=%llu  cond(2,3)=%llu  clocksWithUnseenTarget=%llu (non-record %llu)  (C,T) pairs=%llu\n",
               (unsigned long long)Cmax, (unsigned long long)cond2, (unsigned long long)cond23,
               (unsigned long long)withUnseen, (unsigned long long)nonRecordWithUnseen, (unsigned long long)pairs);
  std::fprintf(stderr, "decade,eligibleClocks,unseenTargetPairs\n");
  for (u64 d = 0; d < 8; ++d) if (decadeClocks[d])
    std::fprintf(stderr, "1e%llu,%llu,%llu\n", (unsigned long long)d, (unsigned long long)decadeClocks[d], (unsigned long long)decadePairs[d]);
  return 0;
}
