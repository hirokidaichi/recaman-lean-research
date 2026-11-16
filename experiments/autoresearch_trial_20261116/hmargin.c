/*
 * Line capacity conjecture H (E-509, CONJECTURED; COMPUTED for length <= 34):
 * for every +-1 word and every interval [p, k), the number of A clocks b in
 * [p, k) that end a P2 window [t, b) with t >= p (mass 1, moment 0, length
 * = 3 mod 4) is at most the number of S in [p, k).
 *
 * h_margin(w) = max over intervals of (e - s).  H holds on w  <=>  margin <= 0.
 * This is a search evaluator for the 2026-11-16 auto-research tool trial;
 * its output is OBSERVED/COMPUTED evidence only, never a proof.
 *
 * Window test copied from experiments/issue73_20261020/eqcheck.c:
 *   F[i] = height before step i, window [t, b) is P2 iff
 *   F[b] == F[t] + 1  and  sum_{u=t+1..b} (F[u] - F[t]) == 0.
 *
 * Build: cc -O2 -shared -fPIC -o libhmargin.so hmargin.c   (Python ctypes)
 *        cc -O2 -DHMARGIN_MAIN -o hmargin hmargin.c       (CLI: words on stdin)
 */
#include <stdlib.h>
#include <string.h>

#define HM_MAXN 4096

/* Latest valid window start for each A clock (-1 if none). O(n^2/4). */
static void latest_starts(const char *w, int n, int *F, long *G, int *tmax) {
    F[0] = 0; G[0] = 0;
    for (int i = 0; i < n; i++) {
        F[i + 1] = F[i] + (w[i] == 'A' ? 1 : -1);
        G[i + 1] = G[i] + F[i + 1];
    }
    for (int b = 0; b < n; b++) {
        tmax[b] = -1;
        if (w[b] != 'A') continue;
        for (int t = b - 3; t >= 0; t -= 4) {
            if (F[b] != F[t] + 1) continue;
            if ((G[b] - G[t]) - (long)(b - t) * F[t] == 0) { tmax[b] = t; break; }
        }
    }
}

/*
 * Returns max_{p<k} (e_p(k) - s_p(k)); writes the first maximizing interval.
 * Also returns via *tight the number of intervals attaining e == s with e >= 1
 * (a secondary signal: how "saturated" the word is).
 */
int h_margin(const char *w, int n, int *best_p, int *best_k, long *tight) {
    static int F[HM_MAXN + 1], tmax[HM_MAXN];
    static long G[HM_MAXN + 1];
    if (n <= 0 || n > HM_MAXN) return -1000000;
    latest_starts(w, n, F, G, tmax);
    int best = -1000000, bp = 0, bk = 0;
    long nt = 0;
    for (int p = 0; p < n; p++) {
        int e = 0, s = 0;
        for (int k = p + 1; k <= n; k++) {
            int b = k - 1;
            if (w[b] == 'A') { if (tmax[b] >= p) e++; }
            else s++;
            int d = e - s;
            if (d > best) { best = d; bp = p; bk = k; }
            if (d == 0 && e >= 1) nt++;
        }
    }
    if (best_p) *best_p = bp;
    if (best_k) *best_k = bk;
    if (tight) *tight = nt;
    return best;
}

/* Number of endable A clocks counted over the whole word (window inside w). */
int h_endable(const char *w, int n) {
    static int F[HM_MAXN + 1], tmax[HM_MAXN];
    static long G[HM_MAXN + 1];
    if (n <= 0 || n > HM_MAXN) return 0;
    latest_starts(w, n, F, G, tmax);
    int e = 0;
    for (int b = 0; b < n; b++) if (tmax[b] >= 0) e++;
    return e;
}

/*
 * Number of endable A clocks whose shortest window [t, b) is unclean (E-511):
 * some u with t < u < b returns to the base level (F[u] == F[t]) with
 * non-negative area sum_{v=t+1..u} (F[v] - F[t]) >= 0.  By the Clean Window
 * theorem a counterexample to H needs unclean endables, so the search uses
 * this as a secondary objective.
 */
int h_unclean(const char *w, int n) {
    static int F[HM_MAXN + 1], tmax[HM_MAXN];
    static long G[HM_MAXN + 1];
    if (n <= 0 || n > HM_MAXN) return 0;
    latest_starts(w, n, F, G, tmax);
    int cnt = 0;
    for (int b = 0; b < n; b++) {
        int t = tmax[b];
        if (t < 0) continue;
        for (int u = t + 1; u < b; u++) {
            if (F[u] == F[t] && (G[u] - G[t]) - (long)(u - t) * F[t] >= 0) { cnt++; break; }
        }
    }
    return cnt;
}

/*
 * Number of endable A clocks whose shortest window is at least Lmin long.
 * E-372 (COMPUTED): H restricted to windows of length <= 31 holds for every
 * word, so every interval violating H contains an endable whose shortest
 * window (latest start) has length >= 32.  The hunt task rewards these.
 */
int h_longwin(const char *w, int n, int Lmin) {
    static int F[HM_MAXN + 1], tmax[HM_MAXN];
    static long G[HM_MAXN + 1];
    if (n <= 0 || n > HM_MAXN) return 0;
    latest_starts(w, n, F, G, tmax);
    int cnt = 0;
    for (int b = 0; b < n; b++) if (tmax[b] >= 0 && b - tmax[b] >= Lmin) cnt++;
    return cnt;
}

#ifdef HMARGIN_MAIN
#include <stdio.h>
int main(void) {
    static char line[HM_MAXN + 8];
    while (fgets(line, sizeof line, stdin)) {
        int n = (int)strcspn(line, "\r\n");
        line[n] = 0;
        if (n == 0) continue;
        int p, k; long tight;
        int m = h_margin(line, n, &p, &k, &tight);
        printf("%d\t%d\t%d\t%ld\t%s\n", m, p, k, tight, line);
    }
    return 0;
}
#endif
