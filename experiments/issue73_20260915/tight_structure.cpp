// Protocol H-20260915-20: structure of ALL tight subsets B of U (Hall-OK positive-sum words, necklace
// representatives, same enumeration as tight_nonaas_census.cpp). For every tight B it records the lags
// present, the oldest subtraction of every member, whether the oldest subtractions are pairwise distinct
// and exhaust N(B) (the "OS characterization"), and for lag-7 members which phase is private to them and
// who owns their newest subtraction. Registry E-349.
// G1 structure probe: over ALL tight subsets B of U (not only donor-avoiding), what lags occur,
// and for lag-7 members, are their phases covered by lag-3 siblings inside B?
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
using I = std::int64_t;
static int p; static int sgn[64]; static int Gmin;
static bool isMinRotation(uint64_t w) {
  for (int r = 1; r < p; ++r) { uint64_t x = ((w >> r) | (w << (p - r))) & ((1ULL << p) - 1); if (x < w) return false; }
  return true;
}
static std::vector<uint64_t> nb; static int matchS[64]; static bool usedS[64];
static bool augment(int a) {
  for (int s = 0; s < p; ++s) { if (!((nb[a] >> s) & 1) || usedS[s]) continue; usedS[s] = true;
    if (matchS[s] < 0 || augment(matchS[s])) { matchS[s] = a; return true; } }
  return false;
}
static int maxMatch() { for (int s = 0; s < p; ++s) matchS[s] = -1; int m = 0;
  for (size_t a = 0; a < nb.size(); ++a) { memset(usedS, 0, sizeof(usedS)); if (augment((int)a)) ++m; } return m; }
int main(int argc, char **argv) {
  int plo = atoi(argv[1]), phi = atoi(argv[2]);
  for (p = plo; p <= phi; ++p) {
    uint64_t full = (1ULL << p) - 1;
    I words = 0, tightSets = 0, withLag7 = 0, withLagGe11 = 0, lag7_w1 = 0, lag7_w2 = 0, w1_sibling_in_B = 0, w2_sibling_in_B = 0;
    I lag7_phase_uncovered_by_others = 0, lag7_all3_covered = 0; I sizeHist[16]; memset(sizeHist, 0, sizeof(sizeHist));
    I maxU = 0; std::string firstGe11, firstLag7NoSib; I osDistinct = 0, osEqualsN = 0, priv_u1 = 0, priv_u7 = 0, priv_u6 = 0; std::string firstOSfail; I hasLag3 = 0, w1_u1_isOldestOfMember = 0, w1_u1_owner_lag3 = 0;
    for (uint64_t w = 0; w <= full; ++w) {
      int pc = __builtin_popcountll(w); int sigma = 2 * pc - p;
      if (sigma <= 0 || !isMinRotation(w)) continue;
      for (int i = 0; i < p; ++i) sgn[i] = ((w >> i) & 1) ? 1 : -1;
      Gmin = 0;
      for (int s = 0; s < p; ++s) { int acc = 0; for (int l = 1; l <= p; ++l) { acc += sgn[((s - l) % p + p) % p]; if (acc < Gmin) Gmin = acc; } }
      int stopS = 1 - Gmin; nb.clear(); std::vector<int> lag, phase, w1flag, oldS;
      for (int i = 0; i < p; ++i) {
        if (sgn[i] < 0) continue;
        int S = 0, idx = i; I M = 0; bool ok = false; uint64_t cover = 0; I dfin = 0; int first = 0; int os = -1;
        for (I d = 1;; ++d) { idx = (idx - 1 + p) % p; int v = sgn[idx]; if (d == 1) first = v;
          if (v < 0) { cover |= 1ULL << idx; os = idx; } S += v; M += d * v;
          if (S == 1 && M == 0) { ok = true; dfin = d; break; } if (S > stopS) break; }
        if (!ok) continue;
        nb.push_back(cover); lag.push_back((int)dfin); phase.push_back(i); w1flag.push_back(dfin == 7 && first < 0 ? 1 : (dfin == 7 ? 2 : 0)); oldS.push_back(os);
      }
      ++words; const int nU = (int)nb.size(); if (nU > maxU) maxU = nU;
      if (maxMatch() < nU) continue;
      for (uint32_t m = 1; m < (1u << nU); ++m) {
        uint64_t N = 0; int sz = 0; int mx = 0;
        for (int b = 0; b < nU; ++b) if ((m >> b) & 1) { N |= nb[b]; ++sz; if (lag[b] > mx) mx = lag[b]; }
        if (__builtin_popcountll(N) != sz) continue;
        ++tightSets; if (sz < 16) ++sizeHist[sz];
        { uint64_t osSet = 0; bool distinct = true; for (int b = 0; b < nU; ++b) if ((m >> b) & 1) { uint64_t bit = 1ULL << oldS[b]; if (osSet & bit) distinct = false; osSet |= bit; }
          if (distinct) ++osDistinct; if (osSet == N) ++osEqualsN;
          { bool l3 = false; for (int b = 0; b < nU; ++b) if (((m >> b) & 1) && lag[b] == 3) l3 = true; if (l3) ++hasLag3; }
          for (int b = 0; b < nU; ++b) if (((m >> b) & 1) && w1flag[b] == 1) { int u1 = ((phase[b] - 1) % p + p) % p; for (int c = 0; c < nU; ++c) if (((m >> c) & 1) && c != b && oldS[c] == u1) { ++w1_u1_isOldestOfMember; if (lag[c] == 3) ++w1_u1_owner_lag3; } }
          if (!(distinct && osSet == N) && firstOSfail.empty()) { std::string t(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) t[i] = 'A'; char buf[128]; snprintf(buf, sizeof buf, " B="); firstOSfail = t + buf; for (int b = 0; b < nU; ++b) if ((m >> b) & 1) { char x[32]; snprintf(x, sizeof x, "%d(l%d,os%d)", phase[b], lag[b], oldS[b]); firstOSfail += x; firstOSfail += ","; } } }
        if (mx >= 11) { ++withLagGe11; if (firstGe11.empty()) { std::string t(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) t[i] = 'A'; firstGe11 = t; } }
        if (mx == 7) {
          ++withLag7;
          for (int b = 0; b < nU; ++b) if (((m >> b) & 1) && lag[b] == 7) {
            int u = phase[b]; bool w1 = w1flag[b] == 1; if (w1) ++lag7_w1; else ++lag7_w2;
            int sib = w1 ? ((u - 3) % p + p) % p : (u + 1) % p; // w1: AAS at u-3 covers u-6 ; w2: AAS at u+1 covers u-2
            bool sibIn = false; for (int c = 0; c < nU; ++c) if (((m >> c) & 1) && phase[c] == sib && lag[c] == 3) sibIn = true;
            if (sibIn) { if (w1) ++w1_sibling_in_B; else ++w2_sibling_in_B; }
            // are all 3 phases of u covered by OTHER members of B?
            uint64_t others = 0; for (int c = 0; c < nU; ++c) if (((m >> c) & 1) && c != b) others |= nb[c];
            int cov = __builtin_popcountll(nb[b] & others);
            if (w1) { uint64_t privm = nb[b] & ~others; if (privm & (1ULL << ((u - 1 + p) % p))) ++priv_u1; if (privm & (1ULL << ((u - 7 + p) % p))) ++priv_u7; if (privm & (1ULL << ((u - 6 + p) % p))) ++priv_u6; }
            if (cov == 3) ++lag7_all3_covered; if (cov < 2) ++lag7_phase_uncovered_by_others;
            if (!sibIn && firstLag7NoSib.empty()) { std::string t(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) t[i] = 'A'; char buf[64]; snprintf(buf, sizeof buf, " u=%d %s cov=%d", u, w1 ? "w1" : "w2", cov); firstLag7NoSib = t + buf; }
          }
        }
      }
    }
    printf("p=%2d words=%lld maxU=%lld tightSets=%lld withLag7=%lld withLagGe11=%lld lag7members: w1=%lld (sib u-3 in B: %lld) w2=%lld (sib u+1 in B: %lld) cov<2:%lld cov=3:%lld %s%s\n",
           p, (long long)words, (long long)maxU, (long long)tightSets, (long long)withLag7, (long long)withLagGe11, (long long)lag7_w1, (long long)w1_sibling_in_B,
           (long long)lag7_w2, (long long)w2_sibling_in_B, (long long)lag7_phase_uncovered_by_others, (long long)lag7_all3_covered,
           firstGe11.empty() ? "" : ("FIRST_GE11 " + firstGe11 + " ").c_str(), firstLag7NoSib.empty() ? "" : ("FIRST_NOSIB " + firstLag7NoSib).c_str());
    printf("   OS-characterization: oldestS distinct=%lld  N(B)==oldestS set=%lld  (of %lld tight sets) %s\n   w1 private phase within B: u-1:%lld u-7:%lld u-6:%lld\n", (long long)osDistinct, (long long)osEqualsN, (long long)tightSets, firstOSfail.empty() ? "" : ("FIRST_FAIL " + firstOSfail).c_str(), (long long)priv_u1, (long long)priv_u7, (long long)priv_u6);
    printf("   every tight set has a lag-3 member: %lld/%lld ; w1 phase u-1 is the oldest S of another member: %lld (owner lag 3: %lld)\n", (long long)hasLag3, (long long)tightSets, (long long)w1_u1_isOldestOfMember, (long long)w1_u1_owner_lag3);
    printf("   tight size histogram:"); for (int k = 1; k < 16; ++k) if (sizeHist[k]) printf(" %d:%lld", k, (long long)sizeHist[k]); printf("\n");
    fflush(stdout);
  }
  return 0;
}
