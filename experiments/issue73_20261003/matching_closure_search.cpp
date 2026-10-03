// C++ port of experiments/issue73_20260916/matching_closure_search.py, mode: Lv memberCap nodeCap --mrv --noaas
// Exact semantics of the Python reference (rec/consistent/MRV via first-min/need list order/node counting/span).
// Usage: mcs Lv memberCap nodeCap shard nshard [--brutecheck]
//   prints Python-format output on stdout, per-word progress (with seconds) on stderr.
// Speed-up (semantics-preserving): the set of fixed bits is always a contiguous interval [lo,hi]
// (v's window [-Lv,0]; every owner window [u-L,u] contains the needed S sc, which lies in [lo,hi]).
// A placement (w,k) at sc touches [u-L,u], u=sc+k, |[u-L,u]| = L+1 <= Lv+1 <= hi-lo+1, so the known part
// of the owner window is the whole window, a prefix part [lo,u] or a suffix part [u-L,hi].  Each case is a
// range query on words of group (L,k) sorted by position-code (numeric or bit-reversed).
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>
#include <map>

struct Word { int L; uint32_t idxkey; uint32_t code; std::vector<int> soff; std::string str; };
static std::vector<Word> OWN;          // owner words, Python OWNERS order
static long long NPLACE = 0;
struct Group { int L, k; std::vector<uint32_t> codes; std::vector<int> cidx; std::vector<uint32_t> revs; std::vector<int> ridx; };
static std::vector<Group> GROUPS;

static int Lv, memberCap; static long long nodeCap;
static bool BRUTE = false;

// ---------- minimal word enumeration (DFS on the backward walk) ----------
// y0 = 1, A: y-1, S: y+1, area += y before the step; P2 prefix at d iff y_d = 0 and area_d = 0.
static int MAXL = 64;
static std::vector<std::vector<int>> minA, maxA; // [r][y+MAXL]
static void initDP(int Lmax) {
    minA.assign(Lmax + 1, std::vector<int>(2 * MAXL + 1, 0)); maxA = minA;
    std::vector<std::vector<char>> ok(Lmax + 1, std::vector<char>(2 * MAXL + 1, 0));
    ok[0][MAXL] = 1;
    for (int r = 1; r <= Lmax; r++)
        for (int y = -r; y <= r; y++) {
            int mn = 1 << 30, mx = -(1 << 30); bool any = false;
            for (int d : {-1, 1}) {
                int y2 = y + d; if (y2 < -(r - 1) || y2 > r - 1) continue;
                if (!ok[r - 1][y2 + MAXL]) continue;
                any = true; mn = std::min(mn, y + minA[r - 1][y2 + MAXL]); mx = std::max(mx, y + maxA[r - 1][y2 + MAXL]);
            }
            if (any) { ok[r][y + MAXL] = 1; minA[r][y + MAXL] = mn; maxA[r][y + MAXL] = mx; }
            else { minA[r][y + MAXL] = 1 << 29; maxA[r][y + MAXL] = -(1 << 29); }
        }
}
static void dfsWords(int L, int d, int y, int area, uint32_t key, std::vector<uint32_t>& out) {
    if (d == L) { if (y == 0 && area == 0) out.push_back(key); return; }
    if (d >= 1 && y == 0 && area == 0) return;            // proper P2 prefix: not minimal
    int r = L - d;
    if (y < -r || y > r) return;
    int need = -area;
    if (need < minA[r][y + MAXL] || need > maxA[r][y + MAXL]) return;
    // letter w_{d+1}: A (bit 1) -> y-1 ; S (bit 0) -> y+1 ; area += y before the step
    dfsWords(L, d + 1, y - 1, area + y, key | (1u << d), out);
    dfsWords(L, d + 1, y + 1, area + y, key, out);
}
static bool isMinimalKey(uint32_t key, int L) { // brute definition (mass/moment), used only for checks
    auto p2 = [&](int d) { int mass = 0, mom = 0; for (int i = 1; i <= d; i++) { int s = (key >> (i - 1)) & 1 ? 1 : -1; mass += s; mom += i * s; } return mass == 1 && mom == 0; };
    if (!p2(L)) return false;
    for (int d = 1; d < L; d++) if (p2(d)) return false;
    return true;
}
static std::vector<uint32_t> minimalWords(int L) {
    std::vector<uint32_t> out; dfsWords(L, 0, 1, 0, 0u, out);
    std::sort(out.begin(), out.end());   // Python bit_words order == ascending integer with w_1 as LSB
    return out;
}

// ---------- search state ----------
static int OFF, SIZE, NW;
static std::vector<uint64_t> vals;
static std::vector<int> memberWord;   // owner index of member at position, -1 if none
static std::vector<int> ownerOf;      // owner position of owned S, INT32_MIN if none
static const int NONE = INT32_MIN;
static int lo, hi, nMembers;
static long long nodes; static bool capHit, found; static int spanLo, spanHi;
static bool capConfigSet; static std::string capConfigStr;
static std::string foundStr, foundOwnStr; static int foundCount;

static inline uint32_t ext(int p, int len) { // p: absolute index
    int w = p >> 6, b = p & 63;
    uint64_t x = vals[w] >> b;
    if (b + len > 64) x |= vals[w + 1] << (64 - b);
    return (uint32_t)(x & ((1ull << len) - 1));
}
static inline void setbit(int p, uint32_t v) {
    int w = p >> 6, b = p & 63;
    vals[w] = (vals[w] & ~(1ull << b)) | ((uint64_t)(v & 1) << b);
}
static inline bool knownS(int pos) { return pos >= lo && pos <= hi && !((vals[(pos + OFF) >> 6] >> ((pos + OFF) & 63)) & 1); }

// range of consistent words of group g for needed S at sc: returns via begin/end and which array (0 codes, 1 revs)
static inline int groupRange(const Group& g, int sc, int& b, int& e) {
    int u = sc + g.k;
    if (memberWord[u + OFF] >= 0) { b = e = 0; return 0; }
    int t = u - g.L;
    if (t >= lo && u <= hi) {
        uint32_t key = ext(t + OFF, g.L + 1);
        auto p = std::equal_range(g.codes.begin(), g.codes.end(), key);
        b = p.first - g.codes.begin(); e = p.second - g.codes.begin(); return 0;
    } else if (t < lo && u <= hi) {
        int s = lo - t; uint32_t key = ext(lo + OFF, u - lo + 1);
        uint64_t a0 = (uint64_t)key << s, a1 = (uint64_t)(key + 1) << s;
        b = std::lower_bound(g.codes.begin(), g.codes.end(), (uint32_t)a0) - g.codes.begin();
        e = (a1 > 0xffffffffull) ? (int)g.codes.size() : (int)(std::lower_bound(g.codes.begin(), g.codes.end(), (uint32_t)a1) - g.codes.begin());
        return 0;
    } else if (t >= lo && u > hi) {
        int m = hi - t + 1; uint32_t key = ext(t + OFF, m);
        uint32_t rk = __builtin_bitreverse32(key) >> (32 - m);
        int sh = g.L + 1 - m;
        uint64_t a0 = (uint64_t)rk << sh, a1 = (uint64_t)(rk + 1) << sh;
        b = std::lower_bound(g.revs.begin(), g.revs.end(), (uint32_t)a0) - g.revs.begin();
        e = (a1 > 0xffffffffull) ? (int)g.revs.size() : (int)(std::lower_bound(g.revs.begin(), g.revs.end(), (uint32_t)a1) - g.revs.begin());
        return 1;
    } else { fprintf(stderr, "impossible: window sticks out on both sides\n"); abort(); }
}
// brute-force consistency (Python `consistent`), used for --brutecheck
static bool consistentBrute(int wi, int k, int sc) {
    const Word& w = OWN[wi]; int u = sc + k;
    if (memberWord[u + OFF] >= 0) return false;
    if (knownS(u)) return false;
    for (int i = 1; i <= w.L; i++) {
        int c = u - i;
        if (c >= lo && c <= hi) {
            uint32_t bit = (vals[(c + OFF) >> 6] >> ((c + OFF) & 63)) & 1;
            uint32_t wb = (w.idxkey >> (i - 1)) & 1;
            if (bit != wb) return false;
        }
    }
    return true;
}
static long long countCons(int sc) {
    long long n = 0; int b, e;
    for (const Group& g : GROUPS) { groupRange(g, sc, b, e); n += e - b; }
    if (BRUTE) {
        long long m = 0;
        for (int wi = 0; wi < (int)OWN.size(); wi++) for (int k : OWN[wi].soff) if (consistentBrute(wi, k, sc)) m++;
        if (m != n) { fprintf(stderr, "BRUTE MISMATCH count sc=%d fast=%lld brute=%lld\n", sc, n, m); abort(); }
    }
    return n;
}
static void listCons(int sc, std::vector<std::pair<int, int>>& out) { // (owner idx, k) in PLACEMENTS order
    out.clear(); int b, e;
    for (const Group& g : GROUPS) {
        int which = groupRange(g, sc, b, e);
        const std::vector<int>& ix = which ? g.ridx : g.cidx;
        for (int j = b; j < e; j++) out.push_back({ix[j], g.k});
    }
    std::sort(out.begin(), out.end());
}

static std::string membersStr() {
    std::string s; bool first = true;
    for (int p = lo; p <= hi; p++) if (memberWord[p + OFF] >= 0) {
        if (!first) s += ' '; first = false;
        s += std::to_string(p) + ":" + OWN[memberWord[p + OFF]].str;
    }
    return s;
}

// returns true iff excluded (Python returns a tree)
static bool rec(const std::vector<int>& need) {
    nodes++;
    spanLo = std::min(spanLo, lo); spanHi = std::max(spanHi, hi);
    if (nodes > nodeCap) { capHit = true; return false; }
    if (need.empty()) {
        found = true; foundCount = nMembers; foundStr = membersStr();
        foundOwnStr.clear();
        for (int p = lo; p <= hi; p++) if (ownerOf[p + OFF] != NONE) foundOwnStr += " " + std::to_string(p) + "->" + std::to_string(ownerOf[p + OFF]);
        return false;
    }
    if (nMembers >= memberCap) {
        capHit = true;
        if (!capConfigSet) {
            capConfigSet = true;
            std::vector<int> n2 = need; std::sort(n2.begin(), n2.end());
            std::string ns = "[";
            for (size_t i = 0; i < n2.size(); i++) { if (i) ns += ", "; ns += std::to_string(n2[i]); }
            ns += "]";
            capConfigStr = membersStr() + " | need " + ns;
        }
        return false;
    }
    // MRV: first need clock with the minimum number of consistent placements (Python min(), first minimum)
    int sc = need[0]; long long best = -1;
    for (int c : need) {
        long long n = countCons(c);
        if (best < 0 || n < best) { best = n; sc = c; if (n == 0 && !BRUTE) break; }
    }
    std::vector<int> rest; rest.reserve(need.size());
    for (int c : need) if (c != sc) rest.push_back(c);
    std::vector<std::pair<int, int>> pl; listCons(sc, pl);
    if ((long long)pl.size() != best) { fprintf(stderr, "internal count mismatch\n"); abort(); }
    if (BRUTE) {
        std::vector<std::pair<int, int>> bl;
        for (int wi = 0; wi < (int)OWN.size(); wi++) for (int k : OWN[wi].soff) if (consistentBrute(wi, k, sc)) bl.push_back({wi, k});
        if (bl != pl) { fprintf(stderr, "BRUTE MISMATCH list\n"); abort(); }
    }
    bool allExcluded = true;
    std::vector<int> need2;
    for (auto& pk : pl) {
        const Word& w = OWN[pk.first]; int k = pk.second; int u = sc + k, t = u - w.L;
        int olo = lo, ohi = hi;
        for (int p = t; p <= u; p++) if (p < lo || p > hi) setbit(p + OFF, w.code >> (p - t));
        lo = std::min(lo, t); hi = std::max(hi, u);
        memberWord[u + OFF] = pk.first; nMembers++;
        ownerOf[sc + OFF] = u;
        need2 = rest;
        size_t restN = rest.size();
        for (int kk : w.soff) {
            int c = u - kk;
            if (ownerOf[c + OFF] != NONE) continue;
            bool inRest = false;
            for (size_t j = 0; j < restN; j++) if (rest[j] == c) { inRest = true; break; }
            if (!inRest) need2.push_back(c);
        }
        bool sub = rec(need2);
        ownerOf[sc + OFF] = NONE; memberWord[u + OFF] = -1; nMembers--; lo = olo; hi = ohi;
        if (!sub) allExcluded = false;
        if (found || capHit) return false;
    }
    return allExcluded;
}

int main(int argc, char** argv) {
    std::vector<std::string> args, flags;
    for (int i = 1; i < argc; i++) { std::string a = argv[i]; if (a.rfind("--", 0) == 0) flags.push_back(a); else args.push_back(a); }
    for (auto& f : flags) if (f == "--brutecheck") BRUTE = true;
    std::string vsel; for (auto& f : flags) if (f.rfind("--v=", 0) == 0) vsel = f.substr(4);
    Lv = std::atoi(args.at(0).c_str()); memberCap = args.size() > 1 ? std::atoi(args[1].c_str()) : 14;
    nodeCap = args.size() > 2 ? std::atoll(args[2].c_str()) : 2000000;
    int shard = args.size() > 3 ? std::atoi(args[3].c_str()) : 0, nshard = args.size() > 4 ? std::atoi(args[4].c_str()) : 1;
    initDP(Lv);
    std::map<int, std::vector<uint32_t>> MW;
    for (int L = 3; L <= Lv; L += 4) {
        MW[L] = minimalWords(L);
        if (BRUTE && L <= 23) { // brute-force cross-check of the enumeration (count and order)
            std::vector<uint32_t> bf;
            for (uint32_t key = 0; key < (1u << L); key++) if (isMinimalKey(key, L)) bf.push_back(key);
            if (bf != MW[L]) { fprintf(stderr, "enumeration mismatch at L=%d\n", L); abort(); }
            fprintf(stderr, "enumeration check L=%d ok (%zu words)\n", L, bf.size());
        }
        for (uint32_t key : MW[L]) {
            Word w; w.L = L; w.idxkey = key; w.code = 1u << L;
            for (int i = 1; i <= L; i++) {
                int b = (key >> (i - 1)) & 1;
                if (b) w.code |= 1u << (L - i); else w.soff.push_back(i);
                w.str += b ? 'A' : 'S';
            }
            NPLACE += w.soff.size();
            OWN.push_back(w);
        }
    }
    // groups (L,k)
    for (int L = 3; L <= Lv; L += 4)
        for (int k = 1; k <= L; k++) {
            Group g; g.L = L; g.k = k;
            std::vector<std::pair<uint32_t, int>> a, r;
            for (int wi = 0; wi < (int)OWN.size(); wi++) if (OWN[wi].L == L && !((OWN[wi].idxkey >> (k - 1)) & 1)) {
                a.push_back({OWN[wi].code, wi});
                r.push_back({__builtin_bitreverse32(OWN[wi].code) >> (32 - (L + 1)), wi});
            }
            if (a.empty()) continue;
            std::sort(a.begin(), a.end()); std::sort(r.begin(), r.end());
            for (auto& p : a) { g.codes.push_back(p.first); g.cidx.push_back(p.second); }
            for (auto& p : r) { g.revs.push_back(p.first); g.ridx.push_back(p.second); }
            GROUPS.push_back(g);
        }
    OFF = (memberCap + 2) * (Lv + 1) + 64; OFF = (OFF + 63) & ~63; SIZE = 2 * OFF + 128; NW = SIZE / 64 + 2;
    vals.assign(NW, 0); memberWord.assign(SIZE, -1); ownerOf.assign(SIZE, NONE);
    std::vector<int> Vidx;
    int base = 0; for (int L = 3; L < Lv; L += 4) base += MW[L].size();
    for (int j = 0; j < (int)MW[Lv].size(); j++) if (j % nshard == shard) Vidx.push_back(base + j);
    if (!vsel.empty()) { Vidx.clear(); for (int j = 0; j < (int)OWN.size(); j++) if (OWN[j].str == vsel) Vidx.push_back(j); }
    printf("lag-max %d: %zu words v, %zu owner words (lag <= %d), %lld placements, memberCap=%d, nodeCap=%lld, LA-AAS=off, order=MRV\n",
           Lv, Vidx.size(), OWN.size(), Lv, NPLACE, memberCap, nodeCap);
    fflush(stdout);
    int excluded = 0, open_ = 0, capped = 0;
    auto T0 = std::chrono::steady_clock::now();
    for (int vi : Vidx) {
        auto t0 = std::chrono::steady_clock::now();
        const Word& v = OWN[vi];
        spanLo = spanHi = 0; capConfigSet = false; capConfigStr.clear();
        bool anyfound = false, anycap = false; long long tot = 0; std::vector<std::string> res;
        for (int k0 : v.soff) {
            // init: bits[0]=A, bits[-i]=v_i
            lo = -v.L; hi = 0;
            for (int p = lo; p <= hi; p++) setbit(p + OFF, v.code >> (p - lo));
            memberWord[0 + OFF] = vi; nMembers = 1; ownerOf[-k0 + OFF] = 0;
            std::vector<int> need; for (int k : v.soff) if (k != k0) need.push_back(-k);
            nodes = 0; found = false; capHit = false;
            rec(need);
            memberWord[0 + OFF] = -1; ownerOf[-k0 + OFF] = NONE; nMembers = 0;
            tot += nodes;
            if (found && !capHit) {
                anyfound = true;
                res.push_back("own offset " + std::to_string(k0) + ": CONSISTENT (" + std::to_string(foundCount) + " members, " + std::to_string(nodes) + " nodes): " + foundStr);
                res.push_back("        own map (S->owner):" + foundOwnStr);
            } else if (capHit) {
                anycap = true; res.push_back("own offset " + std::to_string(k0) + ": cap (" + std::to_string(nodes) + " nodes)");
                if (capConfigSet) res.push_back("        cap config: " + capConfigStr);
            } else res.push_back("own offset " + std::to_string(k0) + ": excluded (" + std::to_string(nodes) + " nodes)");
        }
        const char* tag;
        if (anyfound) { open_++; tag = "CONSISTENT"; } else if (anycap) { capped++; tag = "CAP"; } else { excluded++; tag = "excluded"; }
        printf("  %s: %s (total %lld nodes, span %d..%d)\n", v.str.c_str(), tag, tot, spanLo, spanHi);
        if (std::string(tag) != "excluded") for (auto& r : res) printf("     %s\n", r.c_str());
        fflush(stdout);
        double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        fprintf(stderr, "%d %s %s %lld %.3f\n", vi - base, v.str.c_str(), tag, tot, dt);
    }
    printf("=> excluded %d/%zu, consistent closure %d, cap hit %d\n", excluded, Vidx.size(), open_, capped);
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - T0).count();
    fprintf(stderr, "TOTAL %.1f s\n", dt);
    return 0;
}
