// Protocol H-20260911-01..06: the extremal boundary of the periodic supply capacity.
//
// For a periodic sign word of period p (bit i set = addition A at phase i, clear =
// subtraction S) with positive sign sum sigma = 2*popcount - p > 0:
//
//   U = addition phases admitting a P2 supplier, i.e. some d >= 1 with
//         sum_{j=1..d} sign(w[(i-j) mod p]) = 1  and  sum_{j=1..d} j*sign(...) = 0.
//   D = subtraction phases.
//   U_low  = phases of U whose MINIMAL supply window has ssCount <= 1   (class of E-128)
//   U_high = phases of U whose MINIMAL supply window has ssCount >= 2   (uncovered remainder)
//
// Measured here, exhaustively over necklace representatives (|U|, |D| and ssCount are
// rotation invariant, so one representative per rotation class suffices):
//   (1) E-070  |U| <= |D|                       -- violations
//   (2) E-067  U != A                           -- violations
//   (3) sharpness: is |U| = |D| attained?
//   (4) the ssCount profile of the words attaining |U| = |D|
//   (5) min slack |D| - |U| as a function of |U_high|
//
// Termination of the backward scan is rigorous rather than capped. For a fixed start
// position let g(l) be the backward sign sum of length l. Since g(l) = g(l-p) + sigma
// with sigma > 0, min over all l >= 1 of g(l) equals min over 1 <= l <= p. Writing
// Gmin for the minimum of that quantity over all start positions, once the running
// sum S_d exceeds 1 - Gmin no larger d can return S_d to 1, so the phase is unsupplied.
//
// Self-checks (abort on mismatch):
//   - period 19..22 positive-sum word count reproduces E-081's 3,487,066
//   - E-070 and E-067 hold with no violation on every period scanned
//   - the scan never exceeds the p*(p+3) safety bound
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
using I = std::int64_t;

static int p;
static int sgn[64];
static int Gmin;

static bool isMinRotation(uint64_t w) {
  for (int r = 1; r < p; ++r) {
    uint64_t x = ((w >> r) | (w << (p - r))) & ((1ULL << p) - 1);
    if (x < w) return false;
  }
  return true;
}

// order of a necklace representative = number of distinct rotations
static int rotOrder(uint64_t w) {
  for (int r = 1; r < p; ++r) {
    uint64_t x = ((w >> r) | (w << (p - r))) & ((1ULL << p) - 1);
    if (x == w) return r;
  }
  return p;
}

static uint64_t adj[64];
static int matchS[64];
static bool usedS[64];
static bool augment(int a) {
  for (int s = 0; s < p; ++s) {
    if (!((adj[a] >> s) & 1) || usedS[s]) continue;
    usedS[s] = true;
    if (matchS[s] < 0 || augment(matchS[s])) { matchS[s] = a; return true; }
  }
  return false;
}

int main(int argc, char **argv) {
  int plo = argc > 1 ? atoi(argv[1]) : 2;
  int phi = argc > 2 ? atoi(argv[2]) : 22;
  bool doMatch = argc > 3 ? atoi(argv[3]) != 0 : true;
  printf("protocol=H-20260911-01..06 periodic capacity extremal boundary\n");
  I posWords19_22 = 0;
  for (p = plo; p <= phi; ++p) {
    uint64_t full = (1ULL << p) - 1;
    I necklaces = 0, e070 = 0, e067 = 0, tight = 0, tightHigh = 0, matchFail = 0;
    int tightMaxSS = -1;
    std::vector<int> minSlack(p + 2, 9999), minLowSlack(p + 2, 9999);
    std::string tightWitness;
    for (uint64_t w = 0; w <= full; ++w) {
      int pc = __builtin_popcountll(w);
      int sigma = 2 * pc - p, nS = p - pc;
      if (sigma <= 0) continue;
      if (!isMinRotation(w)) continue;
      ++necklaces;
      if (p >= 19 && p <= 22) posWords19_22 += rotOrder(w);
      for (int i = 0; i < p; ++i) sgn[i] = ((w >> i) & 1) ? 1 : -1;
      Gmin = 0;
      for (int s = 0; s < p; ++s) {
        int acc = 0;
        for (int l = 1; l <= p; ++l) { acc += sgn[((s - l) % p + p) % p]; if (acc < Gmin) Gmin = acc; }
      }
      const int stopS = 1 - Gmin;
      int nLow = 0, nHigh = 0, wordMaxSS = 0;
      std::vector<int> Us;
      for (int i = 0; i < p; ++i) adj[i] = 0;
      for (int i = 0; i < p; ++i) {
        if (sgn[i] < 0) continue;
        int S = 0, ss = 0, idx = i; I M = 0; bool prevS = false, ok = false;
        uint64_t cover = 0;
        for (I d = 1;; ++d) {
          idx = (idx - 1 + p) % p;
          int v = sgn[idx]; bool isS = v < 0;
          if (isS && prevS) ++ss;
          prevS = isS;
          if (isS) cover |= 1ULL << idx;
          S += v; M += d * v;
          if (S == 1 && M == 0) { ok = true; adj[i] = cover; break; }
          if (S > stopS) break;
          if (d > (I)p * (p + 3)) { printf("FAIL scan overrun p=%d\n", p); return 1; }
        }
        if (!ok) continue;
        Us.push_back(i);
        if (ss <= 1) ++nLow; else ++nHigh;
        if (ss > wordMaxSS) wordMaxSS = ss;
      }
      const int nU = nLow + nHigh;
      if (nU > nS) ++e070;
      if (nU == pc) ++e067;
      const int slack = nS - nU, k = nHigh > p ? p : nHigh;
      if (slack < minSlack[k]) minSlack[k] = slack;
      if (nS - nLow < minLowSlack[k]) minLowSlack[k] = nS - nLow;
      if (nU == nS && nS > 0) {
        ++tight;
        if (nHigh > 0) ++tightHigh;
        if (wordMaxSS > tightMaxSS) {
          tightMaxSS = wordMaxSS;
          std::string s(p, 'S');
          for (int i = 0; i < p; ++i) if ((w >> i) & 1) s[i] = 'A';
          tightWitness = s;
        }
      }
      if (doMatch) {
        for (int s = 0; s < p; ++s) matchS[s] = -1;
        int m = 0;
        for (int a : Us) { memset(usedS, 0, sizeof(usedS)); if (augment(a)) ++m; }
        if (m < nU) ++matchFail;
      }
    }
    if (e070 || e067) { printf("FAIL p=%d e070=%lld e067=%lld\n", p, (long long)e070, (long long)e067); return 1; }
    char hall[32];
    if (doMatch) snprintf(hall, sizeof(hall), "%lld", (long long)matchFail);
    else snprintf(hall, sizeof(hall), "not-run");
    printf("p=%2d necklaces=%lld e070viol=0 e067viol=0 hallFail=%s tight=%lld tightWithHighSS=%lld tightMaxSS=%d witness=%s\n",
           p, (long long)necklaces, hall, (long long)tight,
           (long long)tightHigh, tightMaxSS, tightWitness.c_str());
    printf("   SLACK p=%d", p);
    for (int k = 0; k <= p; ++k)
      if (minSlack[k] < 9999) printf(" high=%d:(slack>=%d,lowSlack>=%d)", k, minSlack[k], minLowSlack[k]);
    printf("\n");
    fflush(stdout);
  }
  if (plo <= 19 && phi >= 22) {
    printf("CHECK positive-sum words p=19..22: %lld (E-081 recorded 3487066)\n", (long long)posWords19_22);
    if (posWords19_22 != 3487066) { printf("FAIL E-081 cross-check\n"); return 1; }
  }
  printf("OK\n");
  return 0;
}
