// Protocol H-20260911-10: can concatenating saturated blocks create net surplus?
//
// net(word) = |U| - |D| for the word read as a period.  Exhaustive search found
// max net = 0 for every period <= 31, attained on a structured "tight" family.
// If net were superadditive across a seam, gluing two tight blocks could push net
// above 0 and refute E-070 at a period far beyond exhaustive reach.  This probe
// builds the library of tight blocks (all rotations, since the seam is not
// rotation invariant) and evaluates every concatenation of two and of three.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
using I = std::int64_t;

static int netOf(const std::vector<int> &s) {
  const int p = (int)s.size();
  int sigma = 0; for (int v : s) sigma += v;
  if (sigma <= 0) return -1000;                 // only positive-sum words are in scope
  int Gmin = 0;
  for (int st = 0; st < p; ++st) { int acc = 0;
    for (int l = 1; l <= p; ++l) { acc += s[((st - l) % p + p) % p]; if (acc < Gmin) Gmin = acc; } }
  const int stopS = 1 - Gmin;
  int nU = 0, nS = 0;
  for (int i = 0; i < p; ++i) if (s[i] < 0) ++nS;
  for (int i = 0; i < p; ++i) {
    if (s[i] < 0) continue;
    int S = 0, idx = i; I M = 0;
    for (I d = 1;; ++d) {
      idx = (idx - 1 + p) % p; int v = s[idx]; S += v; M += d * v;
      if (S == 1 && M == 0) { ++nU; break; }
      if (S > stopS) break;
    }
  }
  return nU - nS;
}
static std::vector<int> toVec(const std::string &w) {
  std::vector<int> s; for (char c : w) s.push_back(c == 'A' ? 1 : -1); return s;
}
int main(int argc, char **argv) {
  int pmax = argc > 1 ? atoi(argv[1]) : 16;
  printf("protocol=H-20260911-10 seam pumping over tight blocks (block period <= %d)\n", pmax);
  // build the tight library
  std::vector<std::string> lib;
  for (int p = 2; p <= pmax; ++p) {
    for (uint64_t w = 0; w < (1ULL << p); ++w) {
      int pc = __builtin_popcountll(w); if (2 * pc - p <= 0) continue;
      std::string t(p, 'S'); for (int i = 0; i < p; ++i) if ((w >> i) & 1) t[i] = 'A';
      if (netOf(toVec(t)) == 0) {
        int nS = p - pc; if (nS == 0) continue;          // all-A blocks are trivially net 0
        lib.push_back(t);
      }
    }
  }
  printf("tight blocks (all rotations, |D|>=1): %zu\n", lib.size());
  int best = -1000; std::string bestW; I pairs = 0, positives = 0;
  for (size_t a = 0; a < lib.size(); ++a)
    for (size_t b = 0; b < lib.size(); ++b) {
      std::string g = lib[a] + lib[b];
      if (g.size() > 40) continue;
      ++pairs;
      int n = netOf(toVec(g));
      if (n > best) { best = n; bestW = g; }
      if (n > 0) ++positives;
    }
  printf("pairs=%lld  maxNet=%d  netPositive=%lld  witness=%s\n",
         (long long)pairs, best, (long long)positives, bestW.c_str());
  // triples, restricted to the shortest blocks to stay in budget
  std::vector<std::string> small;
  for (auto &t : lib) if (t.size() <= 12) small.push_back(t);
  printf("small blocks for triples: %zu\n", small.size());
  int best3 = -1000; std::string best3W; I triples = 0, pos3 = 0;
  for (size_t a = 0; a < small.size(); ++a)
    for (size_t b = 0; b < small.size(); ++b)
      for (size_t c = 0; c < small.size(); ++c) {
        std::string g = small[a] + small[b] + small[c];
        if (g.size() > 36) continue;
        ++triples;
        int n = netOf(toVec(g));
        if (n > best3) { best3 = n; best3W = g; }
        if (n > 0) ++pos3;
      }
  printf("triples=%lld  maxNet=%d  netPositive=%lld  witness=%s\n",
         (long long)triples, best3, (long long)pos3, best3W.c_str());
  printf("%s\n", (positives || pos3) ? "REFUTATION FOUND" : "no seam surplus");
  return 0;
}
