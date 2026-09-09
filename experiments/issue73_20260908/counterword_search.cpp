// H-20260908-03 fast exhaustive U=A search.
// Positive-sum cyclic ±1 words; P2 via the closed-form one-period unfold.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

static bool all_supplied(int p, uint32_t mask, std::vector<int> *lags_out) {
  std::vector<int> w(p);
  int S = 0;
  for (int i = 0; i < p; ++i) {
    w[i] = (mask >> i) & 1 ? 1 : -1;
    S += w[i];
  }
  if (S <= 0) return false;
  if (lags_out) lags_out->clear();
  for (int t = 0; t < p; ++t) {
    if (w[t] < 0) continue;
    std::vector<int> back(p);
    long long weight = 0;
    for (int i = 0; i < p; ++i) {
      int e = w[(t - (i + 1) % p + p) % p];
      // back[r] = sign at offset r+1
      back[i] = e;
      weight += (long long)(i + 1) * e;
    }
    long long prefix = 0, moment = 0;
    bool hit = false;
    int first_d = -1;
    for (int r = 0; r < p; ++r) {
      if (S != 0) {
        long long need = 1 - prefix;
        if (need % S == 0) {
          long long quot = need / S;
          long long d = quot * p + r;
          if (quot >= 0 && d > 0) {
            long long value = quot * weight +
                              (long long)p * S * quot * (quot - 1) / 2 +
                              quot * p * prefix + moment;
            if (value == 0) {
              hit = true;
              first_d = (int)d;
              break;
            }
          }
        }
      }
      prefix += back[r];
      moment += (long long)(r + 1) * back[r];
    }
    if (!hit) return false;
    if (lags_out) lags_out->push_back(first_d);
  }
  return true;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    std::fprintf(stderr, "usage: %s min_period max_period\n", argv[0]);
    return 2;
  }
  int minp = std::atoi(argv[1]);
  int maxp = std::atoi(argv[2]);
  std::printf("protocol=H-20260908-03 exhaustive U=A C++\n");
  std::fflush(stdout);
  // control
  {
    // SSSSAAAASAAA = S=0,A=1 bits from LSB=phase0
    // word newest encoding: phase i is bit i. SSSS AAAAS AAA
    uint32_t ctrl = 0;
    const char *s = "SSSSAAAASAAA";
    int p = 12;
    for (int i = 0; i < p; ++i) if (s[i] == 'A') ctrl |= (1u << i);
    if (all_supplied(p, ctrl, nullptr)) {
      std::printf("control_failed\n");
      return 1;
    }
    std::printf("control_SSSSAAAASAAA_UA=false\n");
  }
  uint64_t total_pos = 0;
  for (int p = minp; p <= maxp; ++p) {
    if (p > 31) {
      std::fprintf(stderr, "p>31 not supported in this binary\n");
      return 2;
    }
    uint64_t npos = 0, nua = 0;
    uint64_t limit = 1ull << p;
    for (uint64_t mask = 0; mask < limit; ++mask) {
      int S = 0;
      for (int i = 0; i < p; ++i) S += ((mask >> i) & 1) ? 1 : -1;
      if (S <= 0) continue;
      ++npos;
      std::vector<int> lags;
      if (all_supplied(p, (uint32_t)mask, &lags)) {
        ++nua;
        std::string word;
        word.resize(p);
        for (int i = 0; i < p; ++i) word[i] = ((mask >> i) & 1) ? 'A' : 'S';
        std::printf("COUNTEREXAMPLE={\"period\":%d,\"word\":\"%s\",\"sign_sum\":%d,\"mask\":%llu}\n",
                    p, word.c_str(), S, (unsigned long long)mask);
        std::fflush(stdout);
        return 0;
      }
    }
    total_pos += npos;
    std::printf("{\"period\":%d,\"positive_words\":%llu,\"U_eq_A\":%llu}\n",
                p, (unsigned long long)npos, (unsigned long long)nua);
    std::fflush(stdout);
  }
  std::printf("NO_COUNTEREXAMPLE={\"min_period\":%d,\"max_period\":%d,\"positive_words\":%llu,\"U_eq_A\":0}\n",
              minp, maxp, (unsigned long long)total_pos);
  std::printf("COMPLETE: exhaustive clean range is COMPUTED, not a proof\n");
  return 0;
}
