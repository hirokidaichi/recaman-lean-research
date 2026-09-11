// Protocol H-20260911-12: is the strict slack of T3 produced LOCALLY?
//
// T3 says: if some minimal window has ssCount >= 2 then |U| <= |D| - 1.
// A proof would want the spare subtraction to be exhibited, not merely counted.
// Test the strongest local form:
//   for every word with a high-SS window, and for EVERY high-SS window w_t in it,
//   there is a subtraction s inside w_t such that the local Hall matching
//   (supplied phase -> subtractions of its own minimal window) still saturates U
//   after deleting s.
// "each high-SS window donates a spare subtraction from inside itself."
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
static std::vector<uint64_t> nb; static int matchS[64]; static bool usedS[64]; static uint64_t banned;
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
  printf("protocol=H-20260911-12 local surplus from a high-SS window\n");
  for (p = plo; p <= phi; ++p) {
    uint64_t full = (1ULL << p) - 1;
    I withHigh = 0, localOK = 0, allWindowsOK = 0; std::string firstBad;
    for (uint64_t w = 0; w <= full; ++w) {
      int pc = __builtin_popcountll(w); int sigma = 2 * pc - p;
      if (sigma <= 0 || !isMinRotation(w)) continue;
      for (int i = 0; i < p; ++i) sgn[i] = ((w >> i) & 1) ? 1 : -1;
      Gmin = 0;
      for (int s = 0; s < p; ++s) { int acc = 0; for (int l = 1; l <= p; ++l) { acc += sgn[((s - l) % p + p) % p]; if (acc < Gmin) Gmin = acc; } }
      int stopS = 1 - Gmin; nb.clear(); std::vector<uint64_t> highCover;
      for (int i = 0; i < p; ++i) {
        if (sgn[i] < 0) continue;
        int S = 0, idx = i, ss = 0; I M = 0; bool prevS = false, ok = false; uint64_t cover = 0;
        for (I d = 1;; ++d) {
          idx = (idx - 1 + p) % p; int v = sgn[idx]; bool isS = v < 0;
          if (isS && prevS) ++ss; prevS = isS;
          if (isS) cover |= 1ULL << idx;
          S += v; M += d * v;
          if (S == 1 && M == 0) { ok = true; break; }
          if (S > stopS) break;
        }
        if (!ok) continue;
        nb.push_back(cover);
        if (ss >= 2) highCover.push_back(cover);
      }
      if (highCover.empty()) continue;
      ++withHigh;
      const int nU = (int)nb.size();
      banned = 0;
      if (maxMatch() < nU) continue;              // Hall already fails; T3 is not the issue
      bool everyWindowDonates = true, someWindowDonates = false;
      for (uint64_t cov : highCover) {
        bool donates = false;
        uint64_t c = cov;
        while (c) { uint64_t b = c & (-(int64_t)c); c ^= b;
          banned = b; if (maxMatch() == nU) { donates = true; break; } }
        banned = 0;
        if (donates) someWindowDonates = true; else everyWindowDonates = false;
      }
      if (someWindowDonates) ++localOK;
      else if (firstBad.empty()) { std::string s(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) s[i] = 'A'; firstBad = s; }
      if (everyWindowDonates) ++allWindowsOK;
    }
    printf("p=%2d wordsWithHighSS=%lld someHighWindowDonates=%lld everyHighWindowDonates=%lld %s\n",
           p, (long long)withHigh, (long long)localOK, (long long)allWindowsOK,
           firstBad.empty() ? "" : ("FIRST FAILURE " + firstBad).c_str());
    fflush(stdout);
  }
  return 0;
}
