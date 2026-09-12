// Protocol H-20260912-01: the lifetime of the counting argument behind Gate T6.
//
// E-230/E-231 close Gate T6 unconditionally for p <= 10. The hinge is
// `TightComponentSlackBound.tight_avoiding_size_le_two_of_p10`, whose proof is pure
// counting:
//
//     |A| <= |U| - 1      (u0 in U, u0 not in A)
//     |U| <= |D| - 1      (positive slack)
//     |D| <= 4            (p <= 10 and positive signSum)
//     ==> |A| <= 2
//
// A lag 7 window covers at least 3 distinct subtraction phases (E-229/E-230), so a tight
// subset (|N(A)| = |A|) containing one needs |A| >= 3. At p <= 10 that is impossible and
// lag 7 is excluded, forcing every member to lag 3 AAS. At p = 11 the same counting gives
// only |D| <= 5, hence |A| <= 3, and the exclusion disappears.
//
// This probe measures whether the CONCLUSION survives where the PROOF dies, i.e. whether
// tight avoiding subsets carrying a lag >= 7 window actually exist for p >= 11.
//   - if none exist, `lag = 3` forcing is still true and needs a non-counting proof;
//   - if they exist, the theorem shape itself breaks at p = 11 and Gate T6 needs a route
//     that does not pass through lag 3 forcing.
//
// Faithfulness to the Lean statements (TenGateT6Resolution, TwoSSTightDisjoint):
//   - the theorems quantify over an ARBITRARY lag assignment satisfying P2, not over the
//     minimal one, so this probe enumerates every P2 window of every addition phase;
//   - N(A) is the set of subtraction PHASES covered by the windows of A, matching
//     `isCoveredByWindow`: phases of u-1, ..., u-d that carry S, taken mod p;
//   - A is tight iff |N(A)| = |A|, avoiding iff it misses the donor u0, and the size cap
//     |A| <= |D| - 2 is exactly the counting chain above;
//   - a word admits a Gate T6 donor iff some addition phase carries a window with
//     ssCount = 2 and lag < 15 (hypotheses hss0 and hd_lt of the deletability theorem).
//
// The `avoiding` condition (u0 not in A) is part of every Lean statement measured here, so
// the search runs per donor u0 and excludes the donor phase from A. Dropping it measures a
// strictly larger family and reports a break one period too early (lag 7 at p = 13 instead
// of p = 15), so the donor loop is not an optimisation but part of the specification.
//
// Self-checks (abort on mismatch):
//   - period 19..22 positive-sum word count reproduces E-081's 3,487,066
//   - the backward scan never exceeds the p*(p+3) safety bound
//   - the measured max tight avoiding size never exceeds the counting cap |D| - 2
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
#include <algorithm>
using I = std::int64_t;

static int p;
static int sgn[64];

static bool isMinRotation(uint64_t w) {
  for (int r = 1; r < p; ++r) {
    uint64_t x = ((w >> r) | (w << (p - r))) & ((1ULL << p) - 1);
    if (x < w) return false;
  }
  return true;
}

static int rotOrder(uint64_t w) {
  for (int r = 1; r < p; ++r) {
    uint64_t x = ((w >> r) | (w << (p - r))) & ((1ULL << p) - 1);
    if (x == w) return r;
  }
  return p;
}

struct Win { int phase; uint64_t cover; int lag; int ss; };

static std::vector<Win> wins;
static int sizeCap;
static int donorPhase;
static int bestSize;
static int bestLag;
static int bestLagSize;
static int bestLagSS;
static std::vector<int> chosen;
static std::vector<int> bestLagWitness;

static void dfs(int start, int count, uint64_t cover, int maxLagSoFar, int ssOfMaxLag) {
  if (count > 0 && (int)__builtin_popcountll(cover) == count) {
    if (count > bestSize) bestSize = count;
    if (maxLagSoFar > bestLag) {
      bestLag = maxLagSoFar;
      bestLagSize = count;
      bestLagSS = ssOfMaxLag;
      bestLagWitness = chosen;
    }
  }
  if (count == sizeCap) return;
  for (int k = start; k < (int)wins.size(); ++k) {
    const Win &w = wins[k];
    if (w.phase == donorPhase) continue;            // avoiding: u0 not in A
    bool clash = false;
    for (int c : chosen)
      if (wins[c].phase == w.phase) { clash = true; break; }
    if (clash) continue;
    uint64_t nc = cover | w.cover;
    if ((int)__builtin_popcountll(nc) > sizeCap) continue;  // N(A) can only grow
    chosen.push_back(k);
    if (w.lag > maxLagSoFar) dfs(k + 1, count + 1, nc, w.lag, w.ss);
    else dfs(k + 1, count + 1, nc, maxLagSoFar, ssOfMaxLag);
    chosen.pop_back();
  }
}

int main(int argc, char **argv) {
  int plo = argc > 1 ? atoi(argv[1]) : 4;
  int phi = argc > 2 ? atoi(argv[2]) : 20;
  printf("protocol=H-20260912-01 lifetime of the Gate T6 counting argument\n");
  printf("# columns: p, necklaces with a Gate T6 donor, counting cap max(|D|-2),\n");
  printf("#   measured max |A| over tight avoiding subsets, max lag inside one, verdict\n");
  I posWords19_22 = 0;
  for (p = plo; p <= phi; ++p) {
    uint64_t full = (1ULL << p) - 1;
    I necklaces = 0, withDonor = 0;
    int capMax = 0, sizeMax = 0, lagMax = 0, lagMaxSize = 0, lagMaxSS = 0;
    std::string lagWitnessWord, sizeWitnessWord;
    std::vector<int> lagWitnessSet;
    for (uint64_t w = 0; w <= full; ++w) {
      int pc = __builtin_popcountll(w);
      int sigma = 2 * pc - p, nS = p - pc;
      if (sigma <= 0) continue;
      if (!isMinRotation(w)) continue;
      ++necklaces;
      if (p >= 19 && p <= 22) posWords19_22 += rotOrder(w);
      const int cap = nS - 2;                 // |A| <= |U|-1 <= |D|-2
      if (cap < 1) continue;
      for (int i = 0; i < p; ++i) sgn[i] = ((w >> i) & 1) ? 1 : -1;
      int Gmin = 0;
      for (int s = 0; s < p; ++s) {
        int acc = 0;
        for (int l = 1; l <= p; ++l) { acc += sgn[((s - l) % p + p) % p]; if (acc < Gmin) Gmin = acc; }
      }
      const int stopS = 1 - Gmin;
      // enumerate every P2 window of every addition phase, and every Gate T6 donor
      std::vector<Win> all, donors;
      for (int i = 0; i < p; ++i) {
        if (sgn[i] < 0) continue;
        int S = 0, ss = 0, idx = i; I M = 0; bool prevS = false;
        uint64_t cover = 0;
        for (I d = 1;; ++d) {
          idx = (idx - 1 + p) % p;
          int v = sgn[idx]; bool isS = v < 0;
          if (isS && prevS) ++ss;
          prevS = isS;
          if (isS) cover |= 1ULL << idx;
          S += v; M += d * v;
          if (S == 1 && M == 0) {
            all.push_back({i, cover, (int)d, ss});
            if (ss == 2 && d < 15 && sgn[((i - (int)d) % p + p) % p] < 0)
              donors.push_back({i, cover, (int)d, ss});
          }
          if (S > stopS) break;
          if (d > (I)p * (p + 3)) { printf("FAIL scan overrun p=%d\n", p); return 1; }
        }
      }
      if (donors.empty()) continue;   // Gate T6 hypotheses need an ssCount=2 donor, lag < 15
      ++withDonor;
      if (cap > capMax) capMax = cap;
      wins.clear();
      for (const Win &e : all)
        if ((int)__builtin_popcountll(e.cover) <= cap) wins.push_back(e);
      sizeCap = cap;
      bestSize = 0; bestLag = 0; bestLagSize = 0; bestLagSS = 0;
      chosen.clear(); bestLagWitness.clear();
      for (const Win &donor : donors) {
        donorPhase = donor.phase;
        dfs(0, 0, 0, 0, 0);
      }
      if (bestSize > sizeCap) { printf("FAIL size exceeds counting cap p=%d\n", p); return 1; }
      std::string word(p, 'S');
      for (int i = 0; i < p; ++i) if ((w >> i) & 1) word[i] = 'A';
      if (bestSize > sizeMax) { sizeMax = bestSize; sizeWitnessWord = word; }
      if (bestLag > lagMax) {
        lagMax = bestLag; lagMaxSize = bestLagSize; lagMaxSS = bestLagSS;
        lagWitnessWord = word;
        lagWitnessSet.clear();
        for (int c : bestLagWitness) lagWitnessSet.push_back(wins[c].phase);
      }
    }
    const char *verdict = lagMax <= 3 ? "lag3-forced" : "LAG3 FORCING BREAKS";
    printf("p=%2d necklaces=%lld withDonor=%lld countingCap=%d maxTightAvoidSize=%d maxLagInTight=%d  %s\n",
           p, (long long)necklaces, (long long)withDonor, capMax, sizeMax, lagMax, verdict);
    if (lagMax > 3) {
      std::sort(lagWitnessSet.begin(), lagWitnessSet.end());
      printf("   WITNESS p=%d word=%s |A|=%d lag=%d ssCount=%d A-phases={",
             p, lagWitnessWord.c_str(), lagMaxSize, lagMax, lagMaxSS);
      for (size_t i = 0; i < lagWitnessSet.size(); ++i)
        printf("%s%d", i ? "," : "", lagWitnessSet[i]);
      printf("}\n");
    }
    fflush(stdout);
  }
  if (plo <= 19 && phi >= 22) {
    printf("CHECK positive-sum words p=19..22: %lld (E-081 recorded 3487066)\n", (long long)posWords19_22);
    if (posWords19_22 != 3487066) { printf("FAIL E-081 cross-check\n"); return 1; }
  }
  printf("OK\n");
  return 0;
}
