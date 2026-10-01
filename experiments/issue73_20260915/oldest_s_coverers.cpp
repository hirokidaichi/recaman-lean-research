// Protocol H-20260915-19: who covers the oldest subtraction s* of an SS=2 lag-11 donor?
// Extension of tight_nonaas_census.cpp (same enumeration, same E-179 cross-check). For every
// ssCount=2, lag-11 donor u0 it counts the other supplied phases u with s*(u0) in N([u]) by lag(u),
// and for lag-7 coverers whether some phase of N([u]) is covered by no other member of U \ {u0}
// ("private phase"). Registry E-347.
// Protocol H-20260915-18: how common are tight avoiding subsets with a non-AAS member?
//
// Setting (same as local_surplus.cpp / E-179): positive-sum periodic word of period p,
// U = supplied addition phases with their minimal P2 window (lag d_t, subtraction cover),
// a donor u0 is a supplied phase whose minimal window has ssCount >= 2, and
// s*(u0) = oldest subtraction phase of the donor window.
// For each donor, enumerate every nonempty B subset of U \ {u0} and call B
//   tight avoiding   iff |N(B)| = |B|   (N(B) = union of the covers of its members),
//   non-AAS          iff some member of B has lag != 3 (a lag-3 P2 window is exactly AAS).
// E-240 (Lean, decide) exhibits such a B at p = 18. The pure-AAS proof route
// (E-297..E-317) needs them to be absent; this census measures how absent they are.
// Cross-check: wordsWithHighSS per period must reproduce E-179 (local_surplus.txt).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
using I = std::int64_t;
static int p; static int sgn[64]; static int Gmin;
static const long long E179[23] = {0,0,0,0,0,0,0,0,1,3,1,20,17,75,67,315,344,1231,1380,4773,5748,18286,22935};
static bool isMinRotation(uint64_t w) {
  for (int r = 1; r < p; ++r) { uint64_t x = ((w >> r) | (w << (p - r))) & ((1ULL << p) - 1); if (x < w) return false; }
  return true;
}
static std::vector<uint64_t> nb; static int matchS[64]; static bool usedS[64]; static uint64_t banned = 0;
static bool augment(int a) {
  for (int s = 0; s < p; ++s) {
    if (!((nb[a] >> s) & 1) || usedS[s] || ((banned >> s) & 1)) continue;
    usedS[s] = true;
    if (matchS[s] < 0 || augment(matchS[s])) { matchS[s] = a; return true; }
  }
  return false;
}
static int maxMatch() {
  for (int s = 0; s < p; ++s) matchS[s] = -1;
  int m = 0;
  for (size_t a = 0; a < nb.size(); ++a) { memset(usedS, 0, sizeof(usedS)); if (augment((int)a)) ++m; }
  return m;
}
int main(int argc, char **argv) {
  int plo = atoi(argv[1]), phi = atoi(argv[2]);
  printf("protocol=H-20260915-19 coverers of the oldest subtraction of SS=2 lag-11 donors (census H-20260915-18 columns retained)\n");
  for (p = plo; p <= phi; ++p) {
    uint64_t full = (1ULL << p) - 1;
    I withHigh = 0, hallOK = 0, donors = 0, donorsTight = 0, donorsNonAAS = 0, wordsNonAAS = 0, t6fail = 0;
    // donor classes: [0] ssCount==2 && lag==11, [1] ssCount==2 any lag, [2] ssCount>=2 any lag
    I cls[3] = {0,0,0}, clsOldestCovered[3] = {0,0,0}, clsOldestHallFail[3] = {0,0,0}, clsSomeDeletable[3] = {0,0,0}, clsNonAAS[3] = {0,0,0};
    std::string firstFail[3], firstNonAASCls[3];
    I coverByLag[64]; memset(coverByLag, 0, sizeof(coverByLag)); I donors11 = 0, coverers7 = 0, coverers7_privatePhase = 0, coverers7_inTight = 0; std::string firstCover7;
    I tightSets = 0, nonAASSets = 0; int maxLagTight = 0, maxSizeNonAAS = 0;
    std::string firstNonAAS; I lagHist[64]; memset(lagHist, 0, sizeof(lagHist));
    for (uint64_t w = 0; w <= full; ++w) {
      int pc = __builtin_popcountll(w); int sigma = 2 * pc - p;
      if (sigma <= 0 || !isMinRotation(w)) continue;
      for (int i = 0; i < p; ++i) sgn[i] = ((w >> i) & 1) ? 1 : -1;
      Gmin = 0;
      for (int s = 0; s < p; ++s) { int acc = 0; for (int l = 1; l <= p; ++l) { acc += sgn[((s - l) % p + p) % p]; if (acc < Gmin) Gmin = acc; } }
      int stopS = 1 - Gmin; nb.clear();
      std::vector<int> lag, ssc, sstar, phase;
      for (int i = 0; i < p; ++i) {
        if (sgn[i] < 0) continue;
        int S = 0, idx = i, ss = 0, oldestS = -1; I M = 0; bool prevS = false, ok = false; uint64_t cover = 0; I dfin = 0;
        for (I d = 1;; ++d) {
          idx = (idx - 1 + p) % p; int v = sgn[idx]; bool isS = v < 0;
          if (isS && prevS) ++ss; prevS = isS;
          if (isS) { cover |= 1ULL << idx; oldestS = idx; }
          S += v; M += d * v;
          if (S == 1 && M == 0) { ok = true; dfin = d; break; }
          if (S > stopS) break;
        }
        if (!ok) continue;
        nb.push_back(cover); lag.push_back((int)dfin); ssc.push_back(ss); sstar.push_back(oldestS); phase.push_back(i);
      }
      bool anyHigh = false; for (int s : ssc) if (s >= 2) anyHigh = true;
      if (!anyHigh) continue;
      ++withHigh;
      const int nU = (int)nb.size();
      banned = 0;
      if (maxMatch() < nU) continue;   // Hall fails: outside the T6 setting (never happens per E-179)
      ++hallOK;
      bool wordNonAAS = false;
      for (int a = 0; a < nU; ++a) {
        if (ssc[a] < 2) continue;
        ++donors;
        if (ssc[a] == 2 && lag[a] == 11) {
          ++donors11;
          for (int b = 0; b < nU; ++b) {
            if (b == a || !((nb[b] >> sstar[a]) & 1)) continue;
            ++coverByLag[lag[b] < 64 ? lag[b] : 63];
            if (lag[b] == 7) {
              ++coverers7;
              // private phase: some phase of N([b]) covered by no other member of U \ {u0}
              bool priv = false; uint64_t c = nb[b];
              while (c) { uint64_t bit = c & (-(int64_t)c); c ^= bit; bool covered = false;
                for (int d = 0; d < nU; ++d) if (d != b && d != a && (nb[d] & bit)) covered = true;
                if (!covered) priv = true; }
              if (priv) ++coverers7_privatePhase;
              if (firstCover7.empty()) { std::string t(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) t[i] = 'A'; char buf[96]; snprintf(buf, sizeof buf, " donor=%d s*=%d lag7=%d priv=%d", phase[a], sstar[a], phase[b], (int)priv); firstCover7 = t + buf; }
            }
          }
        }
        bool dTight = false, dNonAAS = false;
        for (uint32_t m = 1; m < (1u << nU); ++m) {
          if ((m >> a) & 1) continue;                        // avoiding: u0 not in B
          uint64_t N = 0; int sz = 0; bool nonAAS = false; int mx = 0;
          for (int b = 0; b < nU; ++b) if ((m >> b) & 1) { N |= nb[b]; ++sz; if (lag[b] != 3) nonAAS = true; if (lag[b] > mx) mx = lag[b]; }
          if (__builtin_popcountll(N) != sz) continue;       // not tight
          ++tightSets; dTight = true; if (mx > maxLagTight) maxLagTight = mx;
          if ((N >> sstar[a]) & 1) ++t6fail;                 // donated subtraction covered by a tight avoiding B
          if (nonAAS) {
            ++nonAASSets; dNonAAS = true; if (sz > maxSizeNonAAS) maxSizeNonAAS = sz;
            for (int b = 0; b < nU; ++b) if (((m >> b) & 1) && lag[b] != 3) ++lagHist[lag[b]];
            if (firstNonAAS.empty()) {
              std::string s(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) s[i] = 'A';
              char buf[256]; snprintf(buf, sizeof buf, " donor=%d lag=%d s*=%d B=", phase[a], lag[a], sstar[a]);
              firstNonAAS = s + buf;
              for (int b = 0; b < nU; ++b) if ((m >> b) & 1) { char t[32]; snprintf(t, sizeof t, "%d(l%d)", phase[b], lag[b]); firstNonAAS += t; firstNonAAS += ","; }
            }
          }
        }
        if (dTight) ++donorsTight;
        if (dNonAAS) { ++donorsNonAAS; wordNonAAS = true; }
        // independent check via matching: is the oldest S deletable? is some S of the window deletable?
        bool oldestCovered = false;
        for (uint32_t m = 1; m < (1u << nU); ++m) {
          if ((m >> a) & 1) continue;
          uint64_t N = 0; int sz = 0;
          for (int b = 0; b < nU; ++b) if ((m >> b) & 1) { N |= nb[b]; ++sz; }
          if (__builtin_popcountll(N) == sz && ((N >> sstar[a]) & 1)) { oldestCovered = true; break; }
        }
        banned = 1ULL << sstar[a]; bool oldestHallFail = maxMatch() < nU;
        bool someDeletable = false; { uint64_t c = nb[a]; while (c) { uint64_t b = c & (-(int64_t)c); c ^= b; banned = b; if (maxMatch() == nU) { someDeletable = true; break; } } }
        banned = 0;
        if (oldestCovered != oldestHallFail) { fprintf(stderr, "INCONSISTENT subset/matching at p=%d\n", p); return 2; }
        for (int k = 0; k < 3; ++k) {
          bool in = (k == 0) ? (ssc[a] == 2 && lag[a] == 11) : (k == 1) ? (ssc[a] == 2) : true;
          if (!in) continue;
          ++cls[k]; if (oldestCovered) ++clsOldestCovered[k]; if (oldestHallFail) ++clsOldestHallFail[k]; if (someDeletable) ++clsSomeDeletable[k];
          if (dNonAAS) { ++clsNonAAS[k]; if (firstNonAASCls[k].empty()) { std::string t(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) t[i] = 'A'; char buf[96]; snprintf(buf, sizeof buf, " donor=%d lag=%d ss=%d s*=%d", phase[a], lag[a], ssc[a], sstar[a]); firstNonAASCls[k] = t + buf; } }
          if (oldestCovered && firstFail[k].empty()) {
            std::string t(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) t[i] = 'A';
            char buf[128]; snprintf(buf, sizeof buf, " donor=%d lag=%d ss=%d s*=%d", phase[a], lag[a], ssc[a], sstar[a]);
            firstFail[k] = t + buf;
          }
        }
      }
      if (wordNonAAS) ++wordsNonAAS;
    }
    if (p <= 22 && withHigh != E179[p]) { fprintf(stderr, "cross-check FAILED at p=%d: wordsWithHighSS=%lld expected %lld\n", p, (long long)withHigh, E179[p]); return 1; }
    printf("p=%2d wordsWithHighSS=%lld hallOK=%lld donors=%lld donorsWithTightAvoiding=%lld donorsWithNonAASTightAvoiding=%lld wordsWithNonAASTightAvoiding=%lld tightSets=%lld nonAASSets=%lld maxLagInTight=%d maxSizeNonAAS=%d t6failures=%lld\n",
           p, (long long)withHigh, (long long)hallOK, (long long)donors, (long long)donorsTight, (long long)donorsNonAAS, (long long)wordsNonAAS,
           (long long)tightSets, (long long)nonAASSets, maxLagTight, maxSizeNonAAS, (long long)t6fail);
    printf("   nonAAS member lag histogram:"); for (int l = 0; l < 64; ++l) if (lagHist[l]) printf(" lag%d:%lld", l, (long long)lagHist[l]); printf("\n");
    if (!firstNonAAS.empty()) printf("   FIRST nonAAS tight avoiding: %s\n", firstNonAAS.c_str());
    printf("   ss2lag11 donors=%lld s*-coverers by lag:", (long long)donors11); for (int l = 0; l < 64; ++l) if (coverByLag[l]) printf(" lag%d:%lld", l, (long long)coverByLag[l]); printf("  lag7coverers=%lld withPrivatePhase=%lld %s%s\n", (long long)coverers7, (long long)coverers7_privatePhase, firstCover7.empty() ? "" : "FIRST ", firstCover7.c_str());
    const char *cname[3] = {"ss=2,lag=11", "ss=2,anyLag", "ss>=2,anyLag"};
    for (int k = 0; k < 3; ++k) {
      printf("   class[%s] donors=%lld oldestS_notDeletable=%lld (hall=%lld) someS_deletable=%lld donorsWithNonAASTightAvoiding=%lld%s%s%s%s\n", cname[k],
             (long long)cls[k], (long long)clsOldestCovered[k], (long long)clsOldestHallFail[k], (long long)clsSomeDeletable[k], (long long)clsNonAAS[k],
             firstFail[k].empty() ? "" : " FIRST_FAIL ", firstFail[k].c_str(),
             firstNonAASCls[k].empty() ? "" : " FIRST_NONAAS ", firstNonAASCls[k].c_str());
    }
    fflush(stdout);
  }
  return 0;
}
