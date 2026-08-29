// Deep first-occurrence table for Recaman values.
//
// Streams the Recaman orbit with an exact-history bitset up to N steps and
// records, for every value v <= M, the first time it occurs.  The table is
// dumped as a raw little-endian uint64 array of length M+1 (UINT64_MAX means
// "not yet seen inside the horizon").  Checkpoints are written periodically so
// a long run can be interrupted and still be useful.
//
// Usage: deep_first M N outpath [checkpointEvery=1000000000]
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <chrono>
#include <vector>
using u64 = std::uint64_t;
static const u64 INF = ~0ULL;

int main(int argc, char** argv) {
  if (argc < 4) { std::fprintf(stderr, "usage: deep_first M N out [ckptEvery]\n"); return 2; }
  const u64 M = std::strtoull(argv[1], 0, 10);
  const u64 N = std::strtoull(argv[2], 0, 10);
  const char* out = argv[3];
  const u64 ckpt = argc > 4 ? std::strtoull(argv[4], 0, 10) : 1000000000ULL;

  std::vector<u64> first(M + 1, INF);
  // empirical: max value over N steps is < 7.5*N (measured 6.7*N at N=1e9)
  u64 bits = (u64)(7.5 * (double)N) + 1024;
  std::vector<u64> w((bits >> 6) + 64, 0ULL);
  u64 cap = (u64)w.size() << 6;
  auto get = [&](u64 v) { return v < cap ? ((w[v >> 6] >> (v & 63)) & 1ULL) : 0ULL; };
  auto set = [&](u64 v) {
    if (v >= cap) { w.resize((v >> 6) + 1 + (w.size() >> 2), 0ULL); cap = (u64)w.size() << 6; }
    w[v >> 6] |= 1ULL << (v & 63);
  };
  set(0); first[0] = 0;
  u64 v = 0, remaining = M, maxval = 0, lastStep = 0;
  auto t0 = std::chrono::steady_clock::now();
  auto dump = [&](u64 step) {
    std::FILE* f = std::fopen(out, "wb");
    std::fwrite(first.data(), sizeof(u64), M + 1, f);
    std::fclose(f);
    std::FILE* m = std::fopen((std::string(out) + ".meta").c_str(), "w");
    std::fprintf(m, "M=%llu horizon=%llu remaining=%llu maxval=%llu\n",
                 (unsigned long long)M, (unsigned long long)step,
                 (unsigned long long)remaining, (unsigned long long)maxval);
    std::fclose(m);
  };
  for (u64 s = 1; s <= N; ++s) {
    bool sub = v > s && !get(v - s);
    v = sub ? v - s : v + s;
    if (!get(v)) {
      set(v);
      if (v > maxval) maxval = v;
      if (v <= M && first[v] == INF) {
        first[v] = s; lastStep = s;
        if (--remaining == 0) {
          std::fprintf(stderr, "[done] all values <= %llu seen by step %llu\n",
                       (unsigned long long)M, (unsigned long long)s);
          dump(s); return 0;
        }
      }
    }
    if (s % ckpt == 0) {
      double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
      std::fprintf(stderr, "[ckpt] step=%llu remaining=%llu deepestNewSoFar=%llu maxval=%llu %.1fs\n",
                   (unsigned long long)s, (unsigned long long)remaining,
                   (unsigned long long)lastStep, (unsigned long long)maxval, sec);
      std::fflush(stderr);
      dump(s);
    }
  }
  std::fprintf(stderr, "[end] horizon %llu reached, remaining=%llu\n",
               (unsigned long long)N, (unsigned long long)remaining);
  dump(N);
  return 0;
}
