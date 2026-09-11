// Protocol H-20260911-07..08: the charge on the extremal boundary is forced.
//
// On a positive-sign-sum periodic word, build the bipartite graph
//     supplied addition phase  ->  subtraction phases inside its MINIMAL supply window.
// A saturating matching of this graph is exactly the Hall condition H-20260907-09.
// Restricted to the TIGHT words (those attaining |U| = |D|) this measures
//   (1) how many perfect matchings the graph has, and
//   (2) whether the forced matching agrees with the oldest-S rule of E-069,
//       which is REFUTED as a general rule.
// A count of 1 everywhere means the charge on the extremal boundary is not a
// design choice: it is determined, and any correct general charge must agree with it.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
using I = std::int64_t;
static int p; static int sgn[64]; static int Gmin;
static bool isMinRotation(uint64_t w) {
  for (int r = 1; r < p; ++r) { uint64_t x = ((w >> r) | (w << (p - r))) & ((1ULL << p) - 1); if (x < w) return false; }
  return true;
}
static std::vector<uint64_t> nb; static int nU; static std::vector<int> sol;
static I countPM(int i, uint64_t used, std::vector<int> &cur) {
  if (i == nU) { sol = cur; return 1; }
  I t = 0; uint64_t av = nb[i] & ~used;
  while (av) { uint64_t b = av & (-(int64_t)av); av ^= b; cur[i] = __builtin_ctzll(b);
    t += countPM(i + 1, used | b, cur); if (t > 1) return t; }
  return t;
}
int main(int argc, char **argv) {
  int plo = atoi(argv[1]), phi = atoi(argv[2]);
  printf("protocol=H-20260911-07..08 forced charge on the extremal boundary\n");
  I totEdges = 0, oldestOK = 0, endOK = 0, totTight = 0, totUniq = 0;
  for (p = plo; p <= phi; ++p) {
    uint64_t full = (1ULL << p) - 1; I tight = 0, uniq = 0, maxPM = 0;
    for (uint64_t w = 0; w <= full; ++w) {
      int pc = __builtin_popcountll(w); int sigma = 2 * pc - p, nS = p - pc;
      if (sigma <= 0 || !isMinRotation(w)) continue;
      for (int i = 0; i < p; ++i) sgn[i] = ((w >> i) & 1) ? 1 : -1;
      Gmin = 0;
      for (int s = 0; s < p; ++s) { int acc = 0; for (int l = 1; l <= p; ++l) { acc += sgn[((s - l) % p + p) % p]; if (acc < Gmin) Gmin = acc; } }
      int stopS = 1 - Gmin; nb.clear(); std::vector<int> Uph, dl;
      for (int i = 0; i < p; ++i) {
        if (sgn[i] < 0) continue;
        int S = 0, idx = i; I M = 0; uint64_t cover = 0; bool ok = false; I dd = 0;
        for (I d = 1;; ++d) {
          idx = (idx - 1 + p) % p; int v = sgn[idx]; if (v < 0) cover |= 1ULL << idx;
          S += v; M += d * v;
          if (S == 1 && M == 0) { ok = true; dd = d; break; }
          if (S > stopS) break;
        }
        if (ok) { nb.push_back(cover); Uph.push_back(i); dl.push_back((int)dd); }
      }
      nU = (int)nb.size();
      if (nU != nS || nS == 0) continue;
      ++tight;
      std::vector<int> cur(nU, -1);
      if (countPM(0, 0, cur) != 1) { if (2 > maxPM) maxPM = 2; continue; }
      ++uniq; if (maxPM < 1) maxPM = 1;
      for (int a = 0; a < nU; ++a) {
        ++totEdges;
        int i = Uph[a], s = sol[a], d = dl[a];
        int off = ((i - s) % p + p) % p;
        int oldest = -1;
        for (I k = 1; k <= d && k <= (I)p; ++k) { int q = ((i - k) % p + p) % p; if (sgn[q] < 0) oldest = (int)k; }
        if (off == oldest) ++oldestOK;
        if (off == d) ++endOK;
      }
    }
    totTight += tight; totUniq += uniq;
    printf("p=%2d tight=%lld uniquePerfectMatching=%lld maxPM=%lld\n", p, (long long)tight, (long long)uniq, (long long)maxPM);
    fflush(stdout);
  }
  printf("TOTAL tight=%lld unique=%lld forcedEdges=%lld matchesOldestS=%lld (%.2f%%) windowEndIsS=%lld (%.2f%%)\n",
         (long long)totTight, (long long)totUniq, (long long)totEdges, (long long)oldestOK,
         totEdges ? 100.0 * oldestOK / totEdges : 0.0, (long long)endOK, totEdges ? 100.0 * endOK / totEdges : 0.0);
  if (totUniq != totTight) { printf("NOTE some tight words have more than one perfect matching\n"); }
  printf("OK\n");
  return 0;
}
