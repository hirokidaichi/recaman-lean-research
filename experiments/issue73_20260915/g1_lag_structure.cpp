// Protocol H-20260915-20: why does no member of lag >= 11 ever sit in a tight avoiding subset? (G1)
//
// Setting identical to tight_nonaas_census.cpp (E-345) and local_surplus (E-179): positive-sum
// periodic word of period p (necklace representatives), U = supplied addition phases with their
// minimal P2 window (lag d, subtraction cover N([u])), N(B) = union of covers, Hall holds on U.
// E-345 observed that every tight avoiding subset (|N(B)| = |B|, B excluding a high-SS donor) has
// all member lags in {3, 7} for p <= 26.  This probe measures WHY, member by member.
//
// Frozen questions (decided before running):
//   Q1  G1-strong.  For every B subset of U that contains a member v with lag(v) >= 11 (no avoiding
//       condition at all), is |N(B)| >= |B| + 1 ?  Count violating (word, v) pairs; separately count
//       violations where B avoids at least one high-SS donor (= G1 proper, expected 0 by E-345).
//   Q2  Private subtractions.  priv(v) = number of S in v's window covered by no other member of U.
//       Since N(B) contains N(B\{v}) and the private S of v disjointly, Hall on U gives
//       |N(B)| >= |B| - 1 + priv(v); so priv(v) >= 2 already proves G1-strong for that v.
//       Histogram of priv(v) by lag(v).  The members with priv(v) <= 1 are the ones a proof must handle.
//   Q3  For members with priv(v) <= 1: minSlack(v) = min over B containing v of |N(B)| - |B|, and the
//       lag composition of a B attaining it.  First witness per p and per lag.
//   Q4  Which S of a lag >= 11 window are covered by others: for each such v, classify its S positions
//       (offset from v) as private / covered only by lag-3 members / covered by some lag-7 member /
//       covered by some lag >= 11 member.  Aggregated by (lag(v), offset).
//   Q5  Cross-check: wordsWithHighSS must reproduce E-179 for p <= 22.
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
static std::vector<uint64_t> nb; static int matchS[64]; static bool usedS[64];
static bool augment(int a) {
  for (int s = 0; s < p; ++s) {
    if (!((nb[a] >> s) & 1) || usedS[s]) continue;
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
static std::string wordStr(uint64_t w) { std::string s(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) s[i] = 'A'; return s; }
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s plo phi\n", argv[0]); return 1; }
  int plo = atoi(argv[1]), phi = atoi(argv[2]);
  const bool allWords = (argc >= 4 && strcmp(argv[3], "--all") == 0);
  printf("protocol=H-20260915-20 lag>=11 members of U: private subtractions and minimal slack of subsets containing them%s\n",
         allWords ? " [ALL positive-sum words, including those without a high-SS window]" : "");
  std::vector<uint64_t> Nof;
  for (p = plo; p <= phi; ++p) {
    uint64_t full = (1ULL << p) - 1;
    I withHigh = 0, withoutHigh = 0, hallOK = 0, longMembers = 0, q1viol = 0, q1violAvoid = 0;
    I violNoHigh = 0, violBisU = 0, violEquality = 0, violTightBisU_eq = 0;
    I privHist[64][8]; memset(privHist, 0, sizeof(privHist));          // [lag][priv]
    I slackHist[64][8]; memset(slackHist, 0, sizeof(slackHist));        // [lag][minSlack] for priv<=1 members
    I slackHistAvoid[64][8]; memset(slackHistAvoid, 0, sizeof(slackHistAvoid));
    I offClass[64][64][4]; memset(offClass, 0, sizeof(offClass));      // [lag][offset][class]
    std::string firstSlack1[64]; std::string firstViol, firstViolAvoid;
    int maxU = 0;
    for (uint64_t w = 0; w <= full; ++w) {
      int pc = __builtin_popcountll(w); int sigma = 2 * pc - p;
      if (sigma <= 0 || !isMinRotation(w)) continue;
      for (int i = 0; i < p; ++i) sgn[i] = ((w >> i) & 1) ? 1 : -1;
      Gmin = 0;
      for (int s = 0; s < p; ++s) { int acc = 0; for (int l = 1; l <= p; ++l) { acc += sgn[((s - l) % p + p) % p]; if (acc < Gmin) Gmin = acc; } }
      int stopS = 1 - Gmin; nb.clear();
      std::vector<int> lag, ssc, phase;
      for (int i = 0; i < p; ++i) {
        if (sgn[i] < 0) continue;
        int S = 0, idx = i, ss = 0; I M = 0; bool prevS = false, ok = false; uint64_t cover = 0; I dfin = 0;
        for (I d = 1;; ++d) {
          idx = (idx - 1 + p) % p; int v = sgn[idx]; bool isS = v < 0;
          if (isS && prevS) ++ss; prevS = isS;
          if (isS) cover |= 1ULL << idx;
          S += v; M += d * v;
          if (S == 1 && M == 0) { ok = true; dfin = d; break; }
          if (S > stopS) break;
        }
        if (!ok) continue;
        nb.push_back(cover); lag.push_back((int)dfin); ssc.push_back(ss); phase.push_back(i);
      }
      bool anyHigh = false; for (int s : ssc) if (s >= 2) anyHigh = true;
      if (!anyHigh && !allWords) continue;
      if (anyHigh) ++withHigh; else ++withoutHigh;
      const int nU = (int)nb.size();
      if (nU > maxU) maxU = nU;
      if (maxMatch() < nU) continue;
      ++hallOK;
      uint32_t donorMask = 0; for (int a = 0; a < nU; ++a) if (ssc[a] >= 2) donorMask |= 1u << a;
      // N(B) for every mask, by DP on the lowest bit
      const uint32_t nMask = 1u << nU;
      if (Nof.size() < nMask) Nof.resize(nMask);
      Nof[0] = 0;
      for (uint32_t m = 1; m < nMask; ++m) { int b = __builtin_ctz(m); Nof[m] = Nof[m & (m - 1)] | nb[b]; }
      for (int v = 0; v < nU; ++v) {
        if (lag[v] < 11) continue;
        ++longMembers;
        uint64_t others = 0; for (int b = 0; b < nU; ++b) if (b != v) others |= nb[b];
        uint64_t privBits = nb[v] & ~others;
        int priv = __builtin_popcountll(privBits);
        if (priv > 7) priv = 7;
        privHist[lag[v] < 63 ? lag[v] : 63][priv]++;
        // Q4: classify every S of v's window by offset
        for (int off = 1; off <= lag[v] && off < 64; ++off) {
          int pos = ((phase[v] - off) % p + p) % p;
          if (!((nb[v] >> pos) & 1)) continue;
          int cls = 0; // 0 private, 1 only lag-3 others, 2 some lag-7 other (no lag>=11), 3 some lag>=11 other
          bool any = false, l7 = false, lL = false;
          for (int b = 0; b < nU; ++b) if (b != v && ((nb[b] >> pos) & 1)) { any = true; if (lag[b] == 7) l7 = true; if (lag[b] >= 11) lL = true; }
          if (!any) cls = 0; else if (lL) cls = 3; else if (l7) cls = 2; else cls = 1;
          offClass[lag[v] < 63 ? lag[v] : 63][off][cls]++;
        }
        // Q1/Q3: minimal slack over subsets containing v
        int minSlack = 99, minSlackAvoid = 99; uint32_t argAll = 0, argAvoid = 0;
        const uint32_t vb = 1u << v;
        for (uint32_t m = vb; m < nMask; ++m) {
          if (!(m & vb)) continue;
          int sl = __builtin_popcountll(Nof[m]) - __builtin_popcount(m);
          if (sl < minSlack) { minSlack = sl; argAll = m; }
          if ((m & donorMask) != donorMask && sl < minSlackAvoid) { minSlackAvoid = sl; argAvoid = m; }
        }
        if (minSlack < 0) { fprintf(stderr, "Hall violated inside a Hall-OK word at p=%d\n", p); return 2; }
        if (minSlack == 0) {
          ++q1viol;
          int nD = p - pc;
          if (!anyHigh) ++violNoHigh;
          if (argAll == nMask - 1) ++violBisU;
          if (nU == nD) ++violEquality;
          if (argAll == nMask - 1 && nU == nD) ++violTightBisU_eq;
          if (firstViol.empty()) { firstViol = wordStr(w); char buf[96]; snprintf(buf, sizeof buf, " highSS=%d |U|=%d |D|=%d v=%d lag=%d ss=%d priv=%d B=", (int)anyHigh, nU, nD, phase[v], lag[v], ssc[v], priv); firstViol += buf; for (int b = 0; b < nU; ++b) if ((argAll >> b) & 1) { char t[32]; snprintf(t, sizeof t, "%d(l%d)", phase[b], lag[b]); firstViol += t; firstViol += ","; } }
        }
        if (minSlackAvoid == 0) { ++q1violAvoid; if (firstViolAvoid.empty()) { firstViolAvoid = wordStr(w); char buf[64]; snprintf(buf, sizeof buf, " v=%d lag=%d ss=%d B=", phase[v], lag[v], ssc[v]); firstViolAvoid += buf; for (int b = 0; b < nU; ++b) if ((argAvoid >> b) & 1) { char t[32]; snprintf(t, sizeof t, "%d(l%d)", phase[b], lag[b]); firstViolAvoid += t; firstViolAvoid += ","; } } }
        if (priv <= 1) {
          int L = lag[v] < 63 ? lag[v] : 63;
          slackHist[L][minSlack < 7 ? minSlack : 7]++;
          if (minSlackAvoid < 99) slackHistAvoid[L][minSlackAvoid < 7 ? minSlackAvoid : 7]++;
          if (minSlack == 1 && firstSlack1[L].empty()) {
            firstSlack1[L] = wordStr(w); char buf[96]; snprintf(buf, sizeof buf, " v=%d lag=%d ss=%d priv=%d B=", phase[v], lag[v], ssc[v], priv); firstSlack1[L] += buf;
            for (int b = 0; b < nU; ++b) if ((argAll >> b) & 1) { char t[32]; snprintf(t, sizeof t, "%d(l%d)", phase[b], lag[b]); firstSlack1[L] += t; firstSlack1[L] += ","; }
            firstSlack1[L] += " N(B)="; for (int s = 0; s < p; ++s) if ((Nof[argAll] >> s) & 1) { char t[8]; snprintf(t, sizeof t, "%d,", s); firstSlack1[L] += t; }
          }
        }
      }
    }
    if (p <= 22 && withHigh != E179[p]) { fprintf(stderr, "cross-check FAILED at p=%d: wordsWithHighSS=%lld expected %lld\n", p, (long long)withHigh, E179[p]); return 1; }
    printf("p=%2d wordsWithHighSS=%lld wordsWithoutHighSS=%lld hallOK=%lld maxU=%d lagGe11Members=%lld Q1violations(anyB)=%lld Q1violations(avoidingB)=%lld [violations: inWordsWithoutHighSS=%lld argminB=U=%lld |U|=|D|=%lld both=%lld]\n",
           p, (long long)withHigh, (long long)withoutHigh, (long long)hallOK, maxU, (long long)longMembers, (long long)q1viol, (long long)q1violAvoid,
           (long long)violNoHigh, (long long)violBisU, (long long)violEquality, (long long)violTightBisU_eq);
    if (!firstViol.empty()) printf("   FIRST Q1 violation (any B): %s\n", firstViol.c_str());
    if (!firstViolAvoid.empty()) printf("   FIRST Q1 violation (avoiding B): %s\n", firstViolAvoid.c_str());
    for (int L = 11; L < 64; ++L) {
      I tot = 0; for (int k = 0; k < 8; ++k) tot += privHist[L][k];
      if (!tot) continue;
      printf("   lag%2d members=%lld priv:", L, (long long)tot); for (int k = 0; k < 8; ++k) if (privHist[L][k]) printf(" %d:%lld", k, (long long)privHist[L][k]);
      printf(" | priv<=1 minSlack(anyB):"); for (int k = 0; k < 8; ++k) if (slackHist[L][k]) printf(" %d:%lld", k, (long long)slackHist[L][k]);
      printf(" minSlack(avoidingB):"); for (int k = 0; k < 8; ++k) if (slackHistAvoid[L][k]) printf(" %d:%lld", k, (long long)slackHistAvoid[L][k]);
      printf("\n");
      if (!firstSlack1[L].empty()) printf("      first minSlack=1 with priv<=1: %s\n", firstSlack1[L].c_str());
    }
    for (int L = 11; L <= 19; L += 4) {
      bool any = false; for (int off = 1; off <= L; ++off) for (int c = 0; c < 4; ++c) if (offClass[L][off][c]) any = true;
      if (!any) continue;
      printf("   lag%d S-offset classes (priv/only3/some7/someLong):", L);
      for (int off = 1; off <= L; ++off) { I t = 0; for (int c = 0; c < 4; ++c) t += offClass[L][off][c]; if (!t) continue; printf(" off%d=%lld/%lld/%lld/%lld", off, (long long)offClass[L][off][0], (long long)offClass[L][off][1], (long long)offClass[L][off][2], (long long)offClass[L][off][3]); }
      printf("\n");
    }
    fflush(stdout);
  }
  return 0;
}
