// Protocol H-20260912-02: does Gate T6 survive where the lag 3 route dies?
//
// H-20260912-01 showed the `lag = 3` forcing of E-230/E-231 is true only for p <= 12 and
// false from p = 13 (witness AAAASAAASSASS, |A| = 3, lag 7). But lag 3 forcing is only a
// SUFFICIENT condition inside the current proof: Gate T6 itself asserts deletability of
// the donated subtraction s*(u0), and Hall preservation after that deletion.
//
// Reduction used here (exact, not heuristic). Write s* = s*(u0). Hall on U survives the
// deletion of s* iff no sublist A of U has |A| > |N(A) \ {s*}|. Given Hall on U, that can
// only fail when |A| = |N(A)| and s* in N(A). So Gate T6 fails exactly when some TIGHT
// sublist covers s*. Two cases:
//   - u0 in A: handled by slack compensation (E-224); such an A is never tight at
//     positive slack, and this probe records any counterexample separately;
//   - u0 not in A: a TIGHT AVOIDING subset covering s*. This is the case the lag 3
//     forcing was introduced to kill, via `s* disjoint from N(A)`.
// So the decisive measurement is: does a tight avoiding subset ever cover s*?
//
// Witness admissibility. A counterexample must satisfy the hypotheses of
// `p10_universal_gate_t6_deletability_unconditional`, so this probe takes the minimal
// U = A u {u0}, and requires: positive signSum, |U| < |D| (slack), the donor carries
// ssCount = 2 with lag < 15, every member of U is an addition phase with a P2 window at
// its assigned lag, and Hall holds on U before deletion (checked on every sublist).
// Only then is a covering tight avoiding subset a genuine Gate T6 counterexample.
//
// Also reports the (lag, ssCount) histogram of windows appearing in tight avoiding subsets,
// which is what a replacement theorem has to quantify over: if every lag 7 member carries
// ssCount <= 1 it lives inside the already-proved low-SS class of E-128.
//
// Self-checks: E-081 word count, p*(p+3) scan bound, counting cap |A| <= |D|-2.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
#include <map>
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

static std::vector<Win> wins;          // candidate windows, one entry per (phase, cover)
static int sizeCap;
static int donorPhase, sStar;
static std::map<int, I> *lagHist;
static bool foundCover;                // a tight avoiding subset covering s*
static std::vector<int> chosen, coverWitness;

// Hall check on U = A u {u0}: every subset B of U has |B| <= |N(B)|
static bool hallOnU(const std::vector<Win> &U) {
  const int n = (int)U.size();
  for (int m = 1; m < (1 << n); ++m) {
    uint64_t cov = 0; int cnt = 0;
    for (int i = 0; i < n; ++i)
      if ((m >> i) & 1) { cov |= U[i].cover; ++cnt; }
    if (cnt > (int)__builtin_popcountll(cov)) return false;
  }
  return true;
}

static void dfs(int start, int count, uint64_t cover, const Win &donor) {
  if (count > 0 && (int)__builtin_popcountll(cover) == count) {
    for (int c : chosen) (*lagHist)[wins[c].lag * 100 + wins[c].ss]++;
    if ((cover >> sStar) & 1) {
      // candidate Gate T6 counterexample: verify the full hypothesis set on U = A u {u0}
      std::vector<Win> U;
      for (int c : chosen) U.push_back(wins[c]);
      U.push_back(donor);
      if (hallOnU(U)) { foundCover = true; coverWitness = chosen; }
    }
  }
  if (count == sizeCap) return;
  for (int k = start; k < (int)wins.size(); ++k) {
    const Win &w = wins[k];
    if (w.phase == donorPhase) continue;              // avoiding: u0 not in A
    bool clash = false;
    for (int c : chosen) if (wins[c].phase == w.phase) { clash = true; break; }
    if (clash) continue;
    uint64_t nc = cover | w.cover;
    if ((int)__builtin_popcountll(nc) > sizeCap) continue;
    chosen.push_back(k);
    dfs(k + 1, count + 1, nc, donor);
    chosen.pop_back();
  }
}

int main(int argc, char **argv) {
  int plo = argc > 1 ? atoi(argv[1]) : 4;
  int phi = argc > 2 ? atoi(argv[2]) : 22;
  printf("protocol=H-20260912-02 Gate T6 core: can a tight avoiding subset cover s*(u0)?\n");
  I posWords19_22 = 0;
  for (p = plo; p <= phi; ++p) {
    uint64_t full = (1ULL << p) - 1;
    I necklaces = 0, donorCases = 0, coverCases = 0;
    std::map<int, I> hist;
    std::string coverWitnessWord;
    for (uint64_t w = 0; w <= full; ++w) {
      int pc = __builtin_popcountll(w);
      int sigma = 2 * pc - p, nS = p - pc;
      if (sigma <= 0) continue;
      if (!isMinRotation(w)) continue;
      ++necklaces;
      if (p >= 19 && p <= 22) posWords19_22 += rotOrder(w);
      const int cap = nS - 2;
      if (cap < 1) continue;
      for (int i = 0; i < p; ++i) sgn[i] = ((w >> i) & 1) ? 1 : -1;
      int Gmin = 0;
      for (int s = 0; s < p; ++s) {
        int acc = 0;
        for (int l = 1; l <= p; ++l) { acc += sgn[((s - l) % p + p) % p]; if (acc < Gmin) Gmin = acc; }
      }
      const int stopS = 1 - Gmin;
      // all P2 windows; keep every (phase, cover) pair and every donor candidate
      std::vector<Win> all;
      std::vector<Win> donors;
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
      if (donors.empty()) continue;
      std::string word(p, 'S');
      for (int i = 0; i < p; ++i) if ((w >> i) & 1) word[i] = 'A';
      for (const Win &donor : donors) {
        ++donorCases;
        donorPhase = donor.phase;
        sStar = ((donor.phase - donor.lag) % p + p) % p;
        wins.clear();
        for (const Win &e : all)
          if ((int)__builtin_popcountll(e.cover) <= cap) wins.push_back(e);
        sizeCap = cap;
        foundCover = false; chosen.clear(); lagHist = &hist;
        dfs(0, 0, 0, donor);
        if (foundCover) {
          ++coverCases;
          if (coverWitnessWord.empty()) coverWitnessWord = word;
        }
      }
    }
    printf("p=%2d necklaces=%lld donorCases=%lld tightAvoidCoveringSStar=%lld  lagHist={",
           p, (long long)necklaces, (long long)donorCases, (long long)coverCases);
    bool first = true;
    for (auto &kv : hist) { printf("%slag%d/ss%d:%lld", first ? "" : ",", kv.first / 100, kv.first % 100, (long long)kv.second); first = false; }
    printf("}%s\n", coverCases ? "  GATE T6 COUNTEREXAMPLE" : "");
    if (coverCases) printf("   WITNESS p=%d word=%s\n", p, coverWitnessWord.c_str());
    fflush(stdout);
  }
  if (plo <= 19 && phi >= 22) {
    printf("CHECK positive-sum words p=19..22: %lld (E-081 recorded 3487066)\n", (long long)posWords19_22);
    if (posWords19_22 != 3487066) { printf("FAIL E-081 cross-check\n"); return 1; }
  }
  printf("OK\n");
  return 0;
}
