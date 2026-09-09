// H-20260908-02: bounded-lag shift-graph. No positive cycle ⇒ |U_L|≤|D|.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <deque>
#include <string>
#include <vector>

static bool is_supplied(uint32_t mask, int L) {
  for (int d = 3; d <= L; d += 4) {
    uint32_t bits = mask & ((1u << d) - 1u);
    int ac = __builtin_popcount(bits);
    if (ac != (d + 1) / 2) continue;
    int moment = 0;
    uint32_t b = bits;
    while (b) {
      uint32_t low = b & -b;
      moment += 32 - __builtin_clz(low);
      b -= low;
    }
    if (moment == d * (d + 1) / 4) return true;
  }
  return false;
}

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  int L = std::atoi(argv[1]);
  if (L < 3 || L > 27 || L % 4 != 3) {
    std::fprintf(stderr, "L must be 3 mod 4, <=27\n");
    return 2;
  }
  const int size = 1 << L;
  const int bound = size - 1;
  std::vector<uint8_t> sup(size);
  int nsup = 0;
  for (int m = 0; m < size; ++m) {
    sup[m] = is_supplied((uint32_t)m, L);
    nsup += sup[m];
  }
  std::printf("{\"phase\":\"built\",\"L\":%d,\"states\":%d,\"supplied\":%d}\n", L, size, nsup);
  std::fflush(stdout);
  std::vector<int> pot(size, 0), parent(size, -1), depth(size, 0);
  std::deque<int> q;
  std::vector<uint8_t> inq(size, 1);
  for (int i = 0; i < size; ++i) q.push_back(i);
  long long relax = 0;
  while (!q.empty()) {
    int u = q.front();
    q.pop_front();
    inq[u] = 0;
    for (int bit = 0; bit < 2; ++bit) {
      int w = bit ? (int)sup[u] : -1;
      int v = ((u << 1) | bit) & bound;
      int cand = pot[u] + w;
      if (cand <= pot[v]) continue;
      pot[v] = cand;
      parent[v] = u;
      depth[v] = depth[u] + 1;
      ++relax;
      if (depth[v] >= size) {
        std::printf("CAPACITY_COUNTEREXAMPLE={\"L\":%d,\"depth\":%d}\n", L, depth[v]);
        return 0;
      }
      if (!inq[v]) {
        inq[v] = 1;
        q.push_back(v);
      }
    }
    if ((relax & 0xFFFFF) == 0) {
      std::printf("{\"phase\":\"progress\",\"relax\":%lld,\"q\":%zu}\n", relax, q.size());
      std::fflush(stdout);
    }
  }
  int vmax = 0;
  long long viol = 0;
  for (int u = 0; u < size; ++u) {
    if (pot[u] > vmax) vmax = pot[u];
    if (pot[(u << 1) & bound] < pot[u] - 1) ++viol;
    if (pot[((u << 1) | 1) & bound] < pot[u] + (int)sup[u]) ++viol;
  }
  std::printf("NO_POSITIVE_CYCLE={\"L\":%d,\"states\":%d,\"supplied\":%d,\"relax\":%lld,\"maxP\":%d,\"violations\":%lld}\n",
              L, size, nsup, relax, vmax, viol);
  if (viol) {
    std::printf("FAILED: potential inequalities after empty queue\n");
    return 1;
  }
  std::printf("COMPLETE: no positive cycle at this L; not an all-L proof\n");
  return 0;
}
