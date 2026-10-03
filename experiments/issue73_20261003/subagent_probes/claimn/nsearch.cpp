// Claim N, case a = 0: v (minimal P2 word of lag Lv, w_1 = S) at clock 0 is the NEWEST member of a finite
// closed configuration; owners have lag <= Lo (independent of Lv).  Every member u != v satisfies u <= -1.
// Semantics as experiments/issue73_20260916/matching_closure_search.py (MRV, no LA-AAS, injective own),
// plus NEWEST.  Because hi = 0 is fixed, an owner window [u-L, u] (u <= -1) can only stick out on the OLDER
// side, so consistency = range query on codes sorted by value (known part = high bits of the code).
// Usage: nsearch Lv Lo memberCap nodeCap [--anyfirst] [--k0any] [--si] [--brutecheck] [--v=WORD] [--quiet]
//   --anyfirst : do not restrict v to w_1 = S (all minimal words of lag Lv; Claim N in general)
//   --k0any    : let v own any of its S's (default: case a=0 forces own(v) = -1; other a: all offsets)
//   --si       : prune with the suffix-Hall inequality #S[z,-1] <= #M[z+1,0] + #(unplaced A's that could still
//                become members) — here: every A in [z+1,-1] that is not yet a member is counted as possible.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>
#include <map>

struct Word { int L; uint32_t idxkey; uint32_t code; std::vector<int> soff; std::string str; };
static std::vector<Word> OWN;
struct Group { int L, k; std::vector<uint32_t> codes; std::vector<int> cidx; };
static std::vector<Group> GROUPS;
static int Lv, Lo, memberCap; static long long nodeCap;
static bool TRACE = false; static long long depthHist[200];
static bool BRUTE = false, ANYFIRST = false, K0ANY = false, SI = false, QUIET = false;

static int MAXL = 64;
static std::vector<std::vector<int>> minA, maxA;
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
    if (d >= 1 && y == 0 && area == 0) return;
    int r = L - d;
    if (y < -r || y > r) return;
    int need = -area;
    if (need < minA[r][y + MAXL] || need > maxA[r][y + MAXL]) return;
    dfsWords(L, d + 1, y - 1, area + y, key | (1u << d), out);
    dfsWords(L, d + 1, y + 1, area + y, key, out);
}
static bool isMinimalKey(uint32_t key, int L) {
    auto p2 = [&](int d) { int mass = 0, mom = 0; for (int i = 1; i <= d; i++) { int s = (key >> (i - 1)) & 1 ? 1 : -1; mass += s; mom += i * s; } return mass == 1 && mom == 0; };
    if (!p2(L)) return false;
    for (int d = 1; d < L; d++) if (p2(d)) return false;
    return true;
}
static std::vector<uint32_t> minimalWords(int L) {
    std::vector<uint32_t> out; dfsWords(L, 0, 1, 0, 0u, out);
    std::sort(out.begin(), out.end());
    return out;
}

static int OFF, SIZE, NW;
static std::vector<uint64_t> vals;
static std::vector<int> memberWord, ownerOf;
static const int NONE = INT32_MIN;
static int lo, nMembers;               // hi == 0 always
static long long nodes; static bool capHit, found; static int spanLo;
static std::string foundStr;
static long long siPrunes;

static inline uint32_t ext(int p, int len) {
    int w = p >> 6, b = p & 63;
    uint64_t x = vals[w] >> b;
    if (b + len > 64) x |= vals[w + 1] << (64 - b);
    return (uint32_t)(x & ((len >= 64) ? ~0ull : ((1ull << len) - 1)));
}
static inline int bitAt(int pos) { return (vals[(pos + OFF) >> 6] >> ((pos + OFF) & 63)) & 1; }
static inline void setbit(int p, uint32_t v) {
    int w = p >> 6, b = p & 63;
    vals[w] = (vals[w] & ~(1ull << b)) | ((uint64_t)(v & 1) << b);
}
static inline void groupRange(const Group& g, int sc, int& b, int& e) {
    int u = sc + g.k;
    b = e = 0;
    if (u > -1) return;                                   // NEWEST (u = 0 is v itself)
    if (memberWord[u + OFF] >= 0) return;
    if (!bitAt(u)) return;                                // u is S (u >= lo always since u > sc >= lo)
    int t = u - g.L;
    if (t >= lo) {
        uint32_t key = ext(t + OFF, g.L + 1);
        auto p = std::equal_range(g.codes.begin(), g.codes.end(), key);
        b = p.first - g.codes.begin(); e = p.second - g.codes.begin();
    } else {
        int s = lo - t; uint32_t key = ext(lo + OFF, u - lo + 1);
        uint64_t a0 = (uint64_t)key << s, a1 = (uint64_t)(key + 1) << s;
        b = std::lower_bound(g.codes.begin(), g.codes.end(), (uint32_t)a0) - g.codes.begin();
        e = (a1 > 0xffffffffull) ? (int)g.codes.size() : (int)(std::lower_bound(g.codes.begin(), g.codes.end(), (uint32_t)a1) - g.codes.begin());
    }
}
static bool consistentBrute(int wi, int k, int sc) {
    const Word& w = OWN[wi]; int u = sc + k;
    if (u > -1) return false;
    if (memberWord[u + OFF] >= 0) return false;
    if (!bitAt(u)) return false;
    for (int i = 1; i <= w.L; i++) {
        int c = u - i;
        if (c >= lo && c <= 0) if ((uint32_t)bitAt(c) != ((w.idxkey >> (i - 1)) & 1)) return false;
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
static void listCons(int sc, std::vector<std::pair<int, int>>& out) {
    out.clear(); int b, e;
    for (const Group& g : GROUPS) { groupRange(g, sc, b, e); for (int j = b; j < e; j++) out.push_back({g.cidx[j], g.k}); }
    std::sort(out.begin(), out.end());
}
static std::string membersStr() {
    std::string s; bool first = true;
    for (int p = lo; p <= 0; p++) if (memberWord[p + OFF] >= 0) { if (!first) s += ' '; first = false; s += std::to_string(p) + ":" + (p == 0 ? std::string("v") : OWN[memberWord[p + OFF]].str); }
    return s;
}
// suffix Hall: for z in [lo,-1]: #S[z,-1] <= #{A in [z+1,0]} (members or possible future members: any A).
// Future members can only be A clocks inside [lo,-1] (u <= -1, u > needed S >= lo) or, for z near lo, A clocks
// older than lo are irrelevant (they are < z+1).  So the bound is exact w.r.t. currently known bits.
static bool siViolated() {
    int s = 0, a = 1; // a counts A's in [z+1, 0]; v at 0
    for (int z = -1; z >= lo; z--) {
        if (bitAt(z)) { /* A at z: counted for z' < z */ }
        else s++;
        if (s > a) return true;
        if (bitAt(z)) a++;
    }
    return false;
}
static bool rec(const std::vector<int>& need) {
    nodes++;
    spanLo = std::min(spanLo, lo);
    if (nodes > nodeCap) { capHit = true; return false; }
    if (need.empty()) { found = true; foundStr = membersStr(); return false; }
    if (nMembers >= memberCap) { capHit = true; return false; }
    if (SI && siViolated()) { siPrunes++; return true; }
    depthHist[nMembers]++;
    int sc = need[0]; long long best = -1;
    for (int c : need) { long long n = countCons(c); if (best < 0 || n < best) { best = n; sc = c; if (n == 0 && !BRUTE) break; } }
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
        int olo = lo;
        for (int p = t; p < lo; p++) setbit(p + OFF, w.code >> (p - t));
        lo = std::min(lo, t);
        memberWord[u + OFF] = pk.first; nMembers++; ownerOf[sc + OFF] = u;
        need2 = rest; size_t restN = rest.size();
        for (int kk : w.soff) {
            int c = u - kk;
            if (ownerOf[c + OFF] != NONE) continue;
            bool inRest = false;
            for (size_t j = 0; j < restN; j++) if (rest[j] == c) { inRest = true; break; }
            if (!inRest) need2.push_back(c);
        }
        if (TRACE) { printf("%*s[%d] own S@%d by %s@%d (k=%d, lag %d, t=%d) need%s\n", 2*nMembers, "", nMembers, sc, w.str.c_str(), u, k, w.L, t, [&]{std::string r; for(int c: need2) r += " " + std::to_string(c); return r;}().c_str()); }
        bool sub = rec(need2);
        ownerOf[sc + OFF] = NONE; memberWord[u + OFF] = -1; nMembers--; lo = olo;
        if (!sub) allExcluded = false;
        if (found || capHit) return false;
    }
    return allExcluded;
}

int main(int argc, char** argv) {
    std::vector<std::string> args, flags;
    for (int i = 1; i < argc; i++) { std::string a = argv[i]; if (a.rfind("--", 0) == 0) flags.push_back(a); else args.push_back(a); }
    std::string vsel;
    for (auto& f : flags) {
        if (f == "--brutecheck") BRUTE = true; if (f == "--anyfirst") ANYFIRST = true; if (f == "--k0any") K0ANY = true;
        if (f == "--si") SI = true; if (f == "--trace") TRACE = true; if (f == "--quiet") QUIET = true; if (f.rfind("--v=", 0) == 0) vsel = f.substr(4);
    }
    Lv = std::atoi(args.at(0).c_str()); Lo = std::atoi(args.at(1).c_str());
    memberCap = args.size() > 2 ? std::atoi(args[2].c_str()) : 14;
    nodeCap = args.size() > 3 ? std::atoll(args[3].c_str()) : 2000000;
    int Lmax = std::max(Lv, Lo);
    if (Lmax > 30) { fprintf(stderr, "lag too large\n"); return 1; }
    initDP(Lmax);
    std::map<int, std::vector<uint32_t>> MW;
    for (int L = 3; L <= Lmax; L += 4) {
        MW[L] = minimalWords(L);
        if (BRUTE && L <= 23) {
            std::vector<uint32_t> bf;
            for (uint32_t key = 0; key < (1u << L); key++) if (isMinimalKey(key, L)) bf.push_back(key);
            if (bf != MW[L]) { fprintf(stderr, "enumeration mismatch at L=%d\n", L); abort(); }
        }
    }
    auto mk = [&](uint32_t key, int L) { Word w; w.L = L; w.idxkey = key; w.code = 1u << L;
        for (int i = 1; i <= L; i++) { int b = (key >> (i - 1)) & 1; if (b) w.code |= 1u << (L - i); else w.soff.push_back(i); w.str += b ? 'A' : 'S'; }
        return w; };
    for (int L = 3; L <= Lo; L += 4) for (uint32_t key : MW[L]) OWN.push_back(mk(key, L));
    long long npl = 0; for (auto& w : OWN) npl += w.soff.size();
    for (int L = 3; L <= Lo; L += 4)
        for (int k = 1; k <= L; k++) {
            Group g; g.L = L; g.k = k; std::vector<std::pair<uint32_t, int>> a;
            for (int wi = 0; wi < (int)OWN.size(); wi++) if (OWN[wi].L == L && !((OWN[wi].idxkey >> (k - 1)) & 1)) a.push_back({OWN[wi].code, wi});
            if (a.empty()) continue;
            std::sort(a.begin(), a.end());
            for (auto& p : a) { g.codes.push_back(p.first); g.cidx.push_back(p.second); }
            GROUPS.push_back(g);
        }
    OFF = (memberCap + 2) * (Lmax + 1) + 64; OFF = (OFF + 63) & ~63; SIZE = 2 * OFF + 128; NW = SIZE / 64 + 2;
    vals.assign(NW, 0); memberWord.assign(SIZE, -1); ownerOf.assign(SIZE, NONE);
    std::vector<Word> V;
    for (uint32_t key : MW[Lv]) { Word w = mk(key, Lv); if (!vsel.empty() && w.str != vsel) continue; if (!ANYFIRST && vsel.empty() && w.str[0] != 'S') continue; V.push_back(w); }
    printf("v lag %d (%s): %zu words; owners lag <= %d: %zu words, %lld placements; memberCap=%d nodeCap=%lld SI=%s\n",
           Lv, ANYFIRST ? "all" : "w_1=S", V.size(), Lo, OWN.size(), npl, memberCap, nodeCap, SI ? "on" : "off");
    fflush(stdout);
    int excluded = 0, open_ = 0, capped = 0; long long totalNodes = 0, maxNodes = 0; int minSpan = 0;
    auto T0 = std::chrono::steady_clock::now();
    for (const Word& v : V) {
        spanLo = 0; bool anyfound = false, anycap = false; long long tot = 0; std::vector<std::string> res;
        // v's own word is placed as a member at 0 with index -2 marker (not an owner word necessarily)
        for (int k0 : v.soff) {
            if (!K0ANY && v.str[0] == 'S' && k0 != 1) continue;
            lo = -v.L;
            for (int p = lo; p <= 0; p++) setbit(p + OFF, v.code >> (p - lo));
            memberWord[0 + OFF] = 1 << 30; nMembers = 1; ownerOf[-k0 + OFF] = 0;
            std::vector<int> need; for (int k : v.soff) if (k != k0) need.push_back(-k);
            nodes = 0; found = false; capHit = false;
            rec(need);
            memberWord[0 + OFF] = -1; ownerOf[-k0 + OFF] = NONE; nMembers = 0;
            for (int p = lo; p <= 0; p++) setbit(p + OFF, 0);
            tot += nodes;
            if (found && !capHit) { anyfound = true; res.push_back("own offset " + std::to_string(k0) + ": CONSISTENT (" + std::to_string(nodes) + " nodes): " + foundStr); }
            else if (capHit) { anycap = true; res.push_back("own offset " + std::to_string(k0) + ": cap (" + std::to_string(nodes) + " nodes)"); }
            else res.push_back("own offset " + std::to_string(k0) + ": excluded (" + std::to_string(nodes) + " nodes)");
        }
        totalNodes += tot; maxNodes = std::max(maxNodes, tot); minSpan = std::min(minSpan, spanLo);
        const char* tag;
        if (anyfound) { open_++; tag = "CONSISTENT"; } else if (anycap) { capped++; tag = "CAP"; } else { excluded++; tag = "excluded"; }
        if (!QUIET || std::string(tag) != "excluded") {
            printf("  %s: %s (total %lld nodes, span %d..0)\n", v.str.c_str(), tag, tot, spanLo);
            if (std::string(tag) != "excluded") for (auto& r : res) printf("     %s\n", r.c_str());
        }
        fflush(stdout);
    }
    printf("   node depth histogram (members placed):"); for (int i = 0; i < 200; i++) if (depthHist[i]) printf(" %d:%lld", i, depthHist[i]); printf("\n");
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - T0).count();
    printf("=> v lag %d owners<=%d: excluded %d/%zu, consistent %d, cap %d; nodes total %lld max/word %lld; min span %d; SI prunes %lld; %.2fs\n",
           Lv, Lo, excluded, V.size(), open_, capped, totalNodes, maxNodes, minSpan, siPrunes, dt);
    return 0;
}
