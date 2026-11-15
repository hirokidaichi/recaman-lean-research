// Complete enumeration of source-relative words of length n.
// Reports min(F-2D) and min(F-D) over D>=1, and every word with F<2D.
#include <cstdint>
#include <iostream>
#include <string>
using namespace std;

int main(int argc, char** argv) {
  int nmax = argc > 1 ? atoi(argv[1]) : 20;
  for (int n = 4; n <= nmax; ++n) {
    uint64_t lim = 1ull << (n - 1);
    int bestSlack = 1 << 28, bestSur = 1 << 28;
    int negSlack = 0, negSur = 0;
    uint64_t slackMask = 0, surMask = 0;
    int slackD = 0, slackF = 0, surD = 0, surF = 0;
    for (uint64_t m = 0; m < lim; ++m) {
      int Hs[40], Bs[40];
      Hs[0] = Bs[0] = 0;
      int H = 0, B = 0, D = 0, F = 0, zeros = 1;
      for (int i = 0; i < n; ++i) {
        bool isA = i && ((m >> (i - 1)) & 1ull);
        if (isA) {
          int hs = H - 1;
          bool sup = false;
          for (int j = 0; j < i; ++j) {
            if (Hs[j] != hs) continue;
            if (B - Bs[j] == (i - j) * hs) {
              sup = true;
              break;
            }
          }
          if (!sup) ++F;
          if (H == 1 && B == 0 && zeros == 1) ++D;
        }
        H += isA ? 1 : -1;
        B += H;
        if (H == 0 && B == 0) ++zeros;
        Hs[i + 1] = H;
        Bs[i + 1] = B;
      }
      if (D < 1) continue;
      int slack = F - 2 * D;
      int sur = F - D;
      if (slack < 0) ++negSlack;
      if (sur < 0) ++negSur;
      if (slack < bestSlack) {
        bestSlack = slack;
        slackMask = m;
        slackD = D;
        slackF = F;
      }
      if (sur < bestSur) {
        bestSur = sur;
        surMask = m;
        surD = D;
        surF = F;
      }
    }
    auto show = [&](uint64_t m) {
      string s(n, 'S');
      for (int i = 1; i < n; ++i)
        if ((m >> (i - 1)) & 1ull) s[i] = 'A';
      return s;
    };
    cout << "n=" << n << " negSlack=" << negSlack << " negSur=" << negSur
         << " bestSlack=" << bestSlack << " D=" << slackD << " F=" << slackF
         << " " << show(slackMask) << " | bestSur=" << bestSur
         << " D=" << surD << " F=" << surF << " " << show(surMask) << "\n";
  }
  return 0;
}
