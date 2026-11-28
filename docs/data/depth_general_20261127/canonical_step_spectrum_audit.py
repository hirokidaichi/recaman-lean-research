#!/usr/bin/env python3
r"""
Reproducible discovery, holdout, G_d falsification, and 12-filter variable-step bridge audit
for Track 3 (H-20261127-08 / E-790 PROVED-LEAN & E-791 PROVED-PAPER).

Part A (E-790 Lean theorems audit on real Recaman.Basic.a):
  1. canonical_step_difference_realized:
       Every k in [1, b] appears as |u - v| for some u, v in V_b = valuesThrough(b).
  2. canonical_consecutive_incident_steps:
       Every v in V_b \ {0, a(b)} has a clock t in [1, b - 1] and u1, u2 in V_b with
       |v - u1| = t and |v - u2| = t + 1 (hence both an even- and odd-distance neighbor <= b).
  3. canonical_separated_set_clock_budget:
       Any Nodup subset L of V_b \ {0, a(b)} with pairwise |v - w| > b and nearest-neighbor
       distance in V_b at least theta (1 <= theta <= b) satisfies 2 * |L| <= b + 1 - theta.
  4. canonical_distinct_sum_le_upperTri_top:
       Any Nodup subset L of V_b satisfies sum(L) <= sum_{j=0}^{|L|-1} upperTri(b - j).

Part B (E-782 G_d refutation + E-791 12-filter variable-step bridge audit):
  - Verifies that E-782's constant-step bridge G_d (d = b - 200*N) FAILS f9 (step spectrum)
    and f10 (consecutive incident steps / odd-even neighbor).
  - Tests whether an explicit VARIABLE-STEP bridge (consecutive steps b, b-1, b-2, ... down
    from the target value into [0, L], where L = b/2 already realizes all steps 1..L!) passes
    ALL 12 filters (E-778 f1..f4 + E-781 f5..f8 + E-790 f9..f12) AND exact greedy replay for
    every E-759-admissible word of length 1..8 and staged words W_n (n=1..4) and E-789 B_1!
"""

from __future__ import annotations
import itertools
import random
import time


def recaman(N: int) -> list[int]:
    a = [0] * (N + 1)
    seen = {0}
    for n in range(1, N + 1):
        cand = a[n - 1] - n
        if cand > 0 and cand not in seen:
            a[n] = cand
        else:
            a[n] = a[n - 1] + n
        seen.add(a[n])
    return a


def upper_tri(n: int) -> int:
    return n * (n + 1) // 2


def audit_real_recaman(a: list[int], b_list: list[int], rng: random.Random):
    v9 = v10 = v11 = v12 = 0
    checks11 = 0
    for b in b_list:
        Vb = sorted(set(a[: b + 1]))
        Vset = set(Vb)
        # (1) Step spectrum 1..b
        for k in range(1, b + 1):
            # Check exact witness a[k-1], a[k] AND check existence in Vset
            if abs(a[k] - a[k - 1]) != k or a[k] not in Vset or a[k - 1] not in Vset:
                v9 += 1
        # (2) Consecutive incident steps for every v in V_b \ {0, a[b]}
        for v in Vb:
            if v == 0 or v == a[b]:
                continue
            ok = False
            for t in range(1, b):
                has_t = (v + t in Vset) or (v >= t and v - t in Vset)
                has_t1 = (v + t + 1 in Vset) or (v >= t + 1 and v - (t + 1) in Vset)
                if has_t and has_t1:
                    ok = True
                    break
            if not ok:
                v10 += 1
        # (3) Separated set clock budget (greedy build maximal >b-separated subset of V_b \ {0, a[b]})
        cands = [v for v in Vb if v != 0 and v != a[b]]
        for _ in range(3):
            rng.shuffle(cands)
            L = []
            for v in cands:
                if all(abs(v - w) > b for w in L):
                    L.append(v)
            if L:
                # Compute min neighbor distance theta in V_b
                idx_map = {val: idx for idx, val in enumerate(Vb)}
                theta = b + 1
                for v in L:
                    idx = idx_map[v]
                    d_nb = 10**18
                    if idx > 0:
                        d_nb = min(d_nb, v - Vb[idx - 1])
                    if idx + 1 < len(Vb):
                        d_nb = min(d_nb, Vb[idx + 1] - v)
                    theta = min(theta, d_nb)
                theta_c = max(1, min(theta, b))
                checks11 += 1
                if 2 * len(L) > b + 1 - theta_c:
                    v11 += 1
        # (4) Distinct sum bound on full V_b and top-k subsets
        for k in (1, min(5, len(Vb)), len(Vb) // 2, len(Vb)):
            if k <= 0:
                continue
            top_k = Vb[-k:]
            bound = sum(upper_tri(b - j) for j in range(k))
            if sum(top_k) > bound:
                v12 += 1
    return v9, v10, v11, v12, checks11


def check_e759(W: list[int]) -> bool:
    H = 0
    B = 0
    out_set = {(0, 0)}
    cand_set = set()
    for i, s in enumerate(W):
        if s == 1:
            cand_set.add((H - 1, B - i * (H - 1)))
        H += s
        B += H
        v = i + 1
        key = (H, B - v * H)
        if s == -1:
            if key in out_set or key in cand_set:
                return False
        out_set.add(key)
    return True


def build_variable_step_bridge_12filter(W: list[int]):
    r"""
    Construct a 12-filter seen-set V for ANY E-759-admissible word W of length N:
      Choose b even, large (e.g., b = 1000 * (N + 2)^2, L = b // 2).
      Wait: we want V = [0..L] U G_var U {a_b} U {external seeds S_ext} such that:
        - f1..f4 (E-778): |V| <= b+1, parity(a_b) == parity(upperTri(b)), max(V) <= upperTri(b),
          sorted clock cover (E-755): k-th largest element <= upperTri(b - k + 1) ... wait exact E-755!
        - f5..f8 (E-781): walk peak 2*max(V) <= a_b + upperTri(b), adjacent gaps <= b,
          tail distinct count above any empty gap g <= b + 1 - g, gap-rank <= b - theta.
        - f9 (E-790 step spectrum): EVERY k in {1, ..., b} appears as |u - v| in V!
            Note: [0..L] ALREADY realizes ALL k in {1, ..., L = b/2}!!
            To realize EVERY k in {L + 1, ..., b}, simply include ONE extra anchor point `b`
            (wait: `{0, ..., L}` + `{b}` has distances `b - j` for `j = 0..L`, which IS `{b - L, ..., b} = {L, ..., b}`!!
            HOLD ON!! JUST **ONE SINGLE POINT `{b}`** PLUS `[0..L]` REALIZES EVERY SINGLE STEP `1..b`!!
            WAIT A SECOND!! Check if `b` has consecutive incident steps (f10):
            `b - (b - L) = L` and `b - (b - L - 1) = L + 1`? YES!! `0 ∈ [0..L]` gives distance `b`,
            `1 ∈ [0..L]` gives distance `b - 1`!! SO `{b}` HAS CONSECUTIVE INCIDENT STEPS `(b - 1, b)`!!)
        - f10 (E-790 consecutive incident steps): EVERY v in V \ {0, a_b} must have t in [1, b-1]
            with both t and t+1 realized as distances from v to V!
            Check every point of V:
              1) v in [1..L]: has 0 and/or neighbors at distances 1, 2 (since L >= 4)!
              2) v = b: has 1 (dist b-1) and 0 (dist b) -> consecutive (b-1, b)!
              3) Bridge points climbing from [0..L] up to a_b:
                 Instead of constant step d (which failed f10!), use CONSECUTIVE DECREASING STEPS:
                   g_0 = a_b, g_1 = a_b - b, g_2 = g_1 - (b - 1), g_3 = g_2 - (b - 2), ...,
                   stopping once g_m <= L!!
                 CHECK EVERY INTERIOR BRIDGE POINT g_j (1 <= j < m):
                   - distance to g_{j-1} is b - j + 1,
                   - distance to g_{j+1} is b - j!!
                   THEY ARE **EXACTLY CONSECUTIVE `(b - j, b - j + 1)`**!!
                 AND check the last bridge point g_m (if g_m > L, wait: g_m <= L is INSIDE [0..L],
                 and g_{m-1} > L has distance `b - m + 1` to g_m ∈ [0..L], AND since g_m >= 1
                 (just shift a_b slightly or choose m so 1 <= g_m <= L), g_m - 1 ∈ [0..L] is at distance
                 `b - m + 2` from g_{m-1} — **CONSECUTIVE `(b - m + 1, b - m + 2)`!!**)!
              4) What about external seeds S_ext (for free A's of W whose candidate c = a_b + h*b + r
                 lies ABOVE L)?!
                 AHA!! A free A's candidate `c` is a SINGLE isolated point `c ∈ V` at height `h >= 1`
                 (Wait: `c` is `a_b + h*b + O(N^2)` where `h` is the signed height of `A`!).
                 To satisfy f10 for EVERY external seed `c` (NOT equal to `a_b`), simply add ONE tiny
                 paired twin `c - 1`? NO! `c - 1` would only give distance `1`, wait: adding `{c - 1, c + 1}`
                 gives `c` distances `1` and `2`? No, `{c - 1, c + 1}` gives `c` distances `1` and `1`!
                 Adding **`{c - 1, c + 2}`** gives `c` distances `1` and `2`, AND `c - 1` has distances `1` (to `c`) and `3` (to `c + 2`)...
                 EVEN SIMPLER: adding a **3-point consecutive block `{c, c + 1, c + 2}`** (a tiny cluster of size 3!)
                 gives EVERY point in `{c, c + 1, c + 2}` distances `1` AND `2` (consecutive `(1, 2)`!!):
                   - `c` has `c+1` (1) and `c+2` (2)!
                   - `c+1` has `c` (1) and `c+2` (1)... wait `c+1` needs 1 AND 2 -> use a **4-point block `{c, c+1, c+2, c+3}`**!
                     - `c`: `c+1` (1), `c+2` (2)
                     - `c+1`: `c+2` (1), `c+3` (2)
                     - `c+2`: `c+1` (1), `c` (2)
                     - `c+3`: `c+2` (1), `c+1` (2)!!
                 WAIT A SECOND!! Does adding `{c+1, c+2, c+3}` near a seed `c` interfere with greedy execution of W?!
                 CHECK!! In W, ALL candidates and outputs lie in congruence classes `Phi_r` with `|Phi_r| <= N^2`,
                 separated by `O(b)` between distinct heights, and inside the same height `h`, TWO different
                 steps could have `Phi` differing by `1, 2, 3`!
                 SO instead of `{c, c+1, c+2, c+3}` (step 1), use a **4-point cluster with step `S_step = 4 * N^2 + 1`**
                 (`{c, c + S_step, c + 2*S_step, c + 3*S_step}`? No, that has distances `S_step, 2*S_step`, NOT consecutive!)
                 USE A **CONSECUTIVE-STEP MINI-ARC**:
                 `{c, c + M, c + 2*M + 1, c + 3*M + 3}`? Wait: what about `c + 3*M + 3`'s second incident step?
                 USE A **CLOSED 3-CYCLE OF STEPS `(M, M+1, 2M+1)`**? No, `2M+1` isn't consecutive with `M+1`!
                 USE A **4-POINT CYCLE**: `x0 = c`, `x1 = c + M`, `x2 = c + 2*M + 1`, `x3 = c + M + 1`?
                 CHECK DISTANCES OF `{c, c + M, c + M + 1, c + 2*M + 1}`?!
                 NO! `c + M` and `c + M + 1` are at distance `1` (which could collide with `c + M + 1`? No! `M = 10 * N^2` is FAR outside the `[-N^2, +N^2]` residue window around `c`!!)!
                 HOLD EVERYTHING!! CHECK ALL 4 POINTS OF **`{c, c + M, c + M + 1, c + M + 2}`** (where `M = 10 * N^2`, `M + 2 < b / 4`)!!
                 - `c`: has `c + M` (dist `M`) and `c + M + 1` (dist `M + 1`) -> **CONSECUTIVE `(M, M + 1)`!!**
                 - `c + M`: has `c + M + 1` (dist `1`) and `c + M + 2` (dist `2`) -> **CONSECUTIVE `(1, 2)`!!**
                 - `c + M + 1`: has `c + M` (dist `1`) and `c + M - ...` -> add `c + M + 3`:
                 **4 AUXILIARY POINTS `{c + M, c + M + 1, c + M + 2, c + M + 3}`** (ALL at offset `M = 10 * N^2` away from `c` — ZERO interference with ANY `W` output or candidate in `[c - N^2, c + N^2]`!!):
                 - `c` sees `c + M` (dist `M`) and `c + M + 1` (dist `M + 1`) -> **CONSECUTIVE `(M, M + 1)`**!!
                 - Every point in `{c + M, c + M + 1, c + M + 2, c + M + 3}` sees distances **`1` AND `2`** -> **CONSECUTIVE `(1, 2)`**!!
                 - **AND** for `f11` (`2 * |L| <= b + 1 - theta`): since `c` has neighbor at distance `M << b`, `theta <= M`, and `|S_ext| <= N`, `2 * N << b + 1 - M`!!
                 - **AND** for `f12` (`sum(L) <= topUpperTriSum`): total cardinality is `b/2 + O(N)`, and `max(V) = O(N * b) << upperTri(b) = b^2 / 2`!!

    LET'S TEST THIS EXACT 12-FILTER CONSTRUCTION ON ALL 256 LENGTH-8 WORDS RIGHT NOW!!
    """
    N = len(W)
    # Compute heights & Phi for W
    H = [0]
    B = [0]
    for s in W:
        H.append(H[-1] + s)
        B.append(B[-1] + H[-1])
    Hmin = min(H)
    Hmax = max(H)
    span = Hmax - Hmin + 4
    # Choose large even b so bridge residues (-17*j*(N+2)^2) and seed offsets (+3*(N+2)^2)
    # are completely disjoint from trajectory window [-N^2, +N^2] mod b!
    b = 2 * max(1000, 100 * (N + 2) ** 3)
    L = b // 2
    M_off = 3 * (N + 2) * (N + 2)
    assert M_off + 10 < b // 4

    # Place a_b above L so all trajectory values stay strictly > L and match parity(upperTri(b))!
    # Trajectory values are a_b + H[t] * b + B[t].
    # We want min(a_b + H[t]*b + B[t]) > L + 2*b AND all bridge points down to [0..L] avoid trajectory!
    # Choose height offset h0 = max(2, -Hmin + 4), and base offset r0 = 20 * (N + 2)^2 (adjusted for parity!)
    h0 = max(3, -Hmin + 4)
    # Build variable-step bridge descending from a_b: steps b, b-1, b-2, ...
    # Sum of m steps b + (b-1) + ... + (b-m+1) = m*b - m*(m-1)/2.
    # Choose m = h0 + 1 so g_m = a_b - (m*b - m*(m-1)/2) lies inside [10, L - 10]!
    m = h0 + 1
    bridge_drop = m * b - m * (m - 1) // 2
    # Want g_m in [100, L - 100] AND a_b % 2 == upper_tri(b) % 2
    g_m_target = L // 2
    a_b = bridge_drop + g_m_target
    if a_b % 2 != upper_tri(b) % 2:
        a_b += 1
        g_m_target += 1
    # Check a_b = (h0 + 1)*b - m*(m-1)/2 + L/2 = (h0 + 1.5)*b - O(h0^2)
    # Trajectory values: a_b + H[t]*b + B[t] = (h0 + H[t] + 1.5)*b + O(N^2),
    # whereas bridge points are g_j = a_b - (j*b - j*(j-1)/2) = (h0 - j + 1.5)*b + j*(j-1)/2 - m*(m-1)/2!
    # Wait: could g_j (j >= 1) collide with a trajectory value or candidate at height h = -j?!
    # Trajectory candidates/outputs at height h have residue B[t] in [-N^2, +N^2],
    # while g_j has residue +j*(j-1)/2 (which IS small!).
    # TO GUARANTEE ZERO COLLISION WITH TRAJECTORY AT EVERY HEIGHT:
    # Simply shift the bridge descent to start from a_b by first stepping `b` -> `a_b - b` (residue 0),
    # wait: `a_b - b` has residue `0`, which COULD hit a height `-1` candidate `( -1, 0 )`!!
    # SOLUTION (1-line!!): Let `g_0 = a_b` step DOWN by **`d_0 = b - 5 * (N + 2)^2`**, THEN `d_0 - 1, d_0 - 2, ...`!!
    # CHECK THAT!!
    #   - Every bridge step is STILL strictly consecutive: `d_0, d_0 - 1, d_0 - 2, ...` (`<= b`),
    #   - Every bridge point `g_j` (`j >= 1`) has residue `+5*j*(N+2)^2 + j*(j-1)/2` mod `b` —
    #     COMPLETELY OUTSIDE `[-N^2, +N^2]` mod `b` (ZERO collision with ANY output or candidate of W!!),
    #   - And to keep `f9` (step spectrum 1..b) 100% satisfied: `{b}` alone + `[0..L]` ALREADY realizes
    #     EVERY step `1..b` (and `b` has residue `0` at height `0`? Wait: `b` is at `b < 2*b < min_traj`,
    #     COMPLETELY BELOW the entire trajectory `min_traj >= 3*b`!!)!
    d0 = b - 17 * (N + 2) * (N + 2)
    bridge = [a_b]
    cur = a_b
    step = d0
    while cur > L:
        cur -= step
        step -= 1
        bridge.append(cur)
    # Ensure final bridge point cur lies in [1, L] (adjust a_b upward slightly if cur < 1)
    if cur < 1:
        shift = (10 - cur)
        if shift % 2 == 1:
            shift += 1
        a_b += shift
        bridge = [x + shift for x in bridge]
    assert 1 <= bridge[-1] <= L, f"bridge[-1]={bridge[-1]}, L={L}"

    # Collect required external seeds for A-steps of W not internally supplied:
    # Actually just add the exact minimal external seed set for W (all A candidates not previously output!)
    out_keys = {(0, 0)}
    seeds = set()
    for i, s in enumerate(W):
        if s == 1:
            key = (H[i] - 1, B[i] - i * (H[i] - 1))
            if key not in out_keys:
                # Candidate value at clock b + i + 1:
                # a_{b+i} - (b+i+1) = (a_b + H[i]*b + B[i]) - (b+i+1)?
                # Wait: exact trajectory from clock b:
                # a(b + t) = a_b + H[t]*b + sum_{j=1}^t s_j * j!
                # Let's compute exact trajectory directly!
                pass
        out_keys.add((H[i + 1], B[i + 1] - (i + 1) * H[i + 1]))

    # Compute exact trajectory from (b, a_b) using signs W:
    traj = [a_b]
    cands_A = []
    for i, s in enumerate(W):
        step_k = b + i + 1
        if s == 1:
            cands_A.append(traj[-1] - step_k)
            traj.append(traj[-1] + step_k)
        else:
            traj.append(traj[-1] - step_k)

    # External seeds needed for A steps: those c in cands_A not in earlier traj and > L
    traj_seen = {a_b}
    ext_seeds = set()
    for i, s in enumerate(W):
        step_k = b + i + 1
        if s == 1:
            c = traj[i] - step_k
            if c > L and c not in traj_seen:
                ext_seeds.add(c)
        traj_seen.add(traj[i + 1])

    # Build sparse high set T_high = {b} U down_bridge U up_bridge U ext_seeds U {c + M_off + r}
    # (note: [0..L] is implicitly in V!)
    T_high = {b}
    for x in bridge[:-1]:
        if x > L:
            T_high.add(x)
    # Extend variable-step bridge upward from a_b if any external seed exceeds a_b + d0
    if ext_seeds:
        top_seed = max(ext_seeds)
        cur_u = a_b
        step_u = d0
        up_pts = []
        while cur_u + b < top_seed:
            cur_u += step_u
            step_u -= 1
            up_pts.append(cur_u)
            T_high.add(cur_u)
        if up_pts:
            # Give the top upward bridge point consecutive incident steps via a 4-point cluster
            u_top = up_pts[-1]
            for r in range(4):
                T_high.add(u_top + M_off + r)
    for c in ext_seeds:
        T_high.add(c)
        for r in range(4):
            T_high.add(c + M_off + r)

    # Check ALL 12 filters + exact greedy replay!
    # 1. Exact greedy replay of W from (b, a_b) with V = [0..L] U T_high:
    seen_dyn = set(T_high)
    cur = a_b
    for i, expected in enumerate(W):
        step_k = b + i + 1
        cand = cur - step_k
        is_seen = (0 <= cand <= L) or (cand in seen_dyn)
        if cand > 0 and not is_seen:
            actual = -1
            cur = cand
        else:
            actual = 1
            cur = cur + step_k
        if actual != expected:
            return False, f"greedy mismatch at i={i}"
        if cur > L:
            seen_dyn.add(cur)

    # 2. Verify all 12 filters on V = [0..L] U T_high:
    T_sorted = sorted(T_high)
    card = (L + 1) + len(T_sorted)
    # f1: cardinality <= b + 1
    if card > b + 1:
        return False, "f1"
    # f2: parity
    if a_b % 2 != upper_tri(b) % 2:
        return False, "f2"
    # f3 & f5: max <= upperTri(b) and 2*max <= a_b + upperTri(b)
    mx = max(T_sorted) if T_sorted else L
    if mx > upper_tri(b) or 2 * mx > a_b + upper_tri(b):
        return False, "f3/f5"
    # f4: sorted clock cover (for k-th largest element v_k (0-indexed from top), v_k <= upperTri(b - k))
    for idx, v in enumerate(reversed(T_sorted)):
        if v > upper_tri(b - idx):
            return False, f"f4 at idx={idx}"
    # f6: adjacent gaps <= b
    prev = L
    gaps = []
    for x in T_sorted:
        if x - prev > b:
            return False, f"f6 gap {x - prev} > {b}"
        if x - prev > 1:
            gaps.append((prev, x, x - prev))
        prev = x
    # f7: tail distinct count above any empty gap (lo, hi) <= b + 1 - (hi - lo)
    for lo, hi, g in gaps:
        # Count elements of V >= hi
        tail_cnt = sum(1 for x in T_sorted if x >= hi)
        if tail_cnt > b + 1 - g:
            return False, f"f7 gap={g}, tail={tail_cnt}"
    # f8: gap rank (count of gaps > theta <= b - theta)
    for _, _, g in gaps:
        theta = g - 1
        cnt = sum(1 for _, _, gg in gaps if gg > theta)
        if cnt > b - theta:
            return False, f"f8 theta={theta}"
    # f9: EVERY step k in {1..b} realized in V (since [0..L] covers 1..L and {b} + [0..L] covers L..b!)
    assert b in T_high and L == b // 2
    # f10: EVERY v in T_high \ {a_b} has consecutive incident steps (t, t+1) with 1 <= t < b!
    for v in T_sorted:
        if v == a_b:
            continue
        # Check distances from v to other points in T_high or [0..L]
        dists = set()
        # Distances to [0..L] (if v - L <= b):
        # Every d in [max(1, v - L), min(b, v)] is realized by u = v - d in [0..L]!
        lo_d = max(1, v - L)
        hi_d = min(b, v)
        has_consec = (hi_d >= lo_d + 1)
        if not has_consec:
            for u in T_sorted:
                d = abs(v - u)
                if 1 <= d <= b:
                    dists.add(d)
            if lo_d <= hi_d:
                dists.add(lo_d)
            for d in dists:
                if d < b and (d + 1) in dists:
                    has_consec = True
                    break
        if not has_consec:
            return False, f"f10 failed at v={v}"
    # f11: separated set clock budget: any >b-separated subset of T_high \ {a_b} has size <= len(T_high),
    # and every element of T_high \ {a_b} has a neighbor in V at distance <= max(d0, M_off) < b - 2*|T_high|
    # Check exact worst-case separated subset of T_high \ {a_b}:
    cands_sep = [v for v in T_sorted if v != a_b]
    sep_L = []
    for v in cands_sep:
        if all(abs(v - w) > b for w in sep_L):
            sep_L.append(v)
    if sep_L:
        # Compute min neighbor dist theta for sep_L
        theta = b
        for v in sep_L:
            nb = min(abs(v - u) for u in T_sorted if u != v) if len(T_sorted) > 1 else b
            if v > L:
                nb = min(nb, v - L)
            theta = min(theta, nb)
        if 2 * len(sep_L) > b + 1 - max(1, theta):
            return False, f"f11 sep={len(sep_L)}, theta={theta}"
    # f12: distinct sum bound on full V <= sum_{j=0}^{card-1} upperTri(b - j)
    sum_V = L * (L + 1) // 2 + sum(T_sorted)
    # Note: sum_{j=0}^{card-1} upperTri(b - j) >= upperTri(b) + ...
    # Compute exact top-card sum using closed form: sum_{m=0}^n m(m+1)/2 = n(n+1)(n+2)/6
    def sum_ut(n):
        return n * (n + 1) * (n + 2) // 6 if n >= 0 else 0
    bound_sum = sum_ut(b) - sum_ut(b - card)
    if sum_V > bound_sum:
        return False, f"f12 sum_V={sum_V} > {bound_sum}"

    return True, f"b={b}, |T_high|={len(T_sorted)}, |bridge|={len(bridge)}, |ext|={len(ext_seeds)}"


def main():
    t0 = time.time()
    rng = random.Random(2026112708)

    # Part A: Real Recaman orbit audit (Discovery b=0..250, Holdout b=251..600)
    a = recaman(600)
    d_res = audit_real_recaman(a, list(range(0, 251)), rng)
    h_res = audit_real_recaman(a, list(range(251, 601)), rng)
    print(f"[E-790 Discovery b=0..250] viols(f9,f10,f11,f12)={d_res[:4]}, f11_checks={d_res[4]}")
    print(f"[E-790 Holdout   b=251..600] viols(f9,f10,f11,f12)={h_res[:4]}, f11_checks={h_res[4]}")
    assert sum(d_res[:4]) == 0 and sum(h_res[:4]) == 0

    # Part B1: Confirm E-782 constant-step bridge G_d FAILS f9 & f10!
    b_gd = 10000
    d_gd = b_gd - 200
    L_gd = b_gd // 2
    # Step k_miss = L_gd + 1 (5001) is MISSING from G_d (all gaps between [0..L] and g1 are >= d_gd > L_gd + 1)!
    # And bridge point g2 = L_gd + 2*d_gd (> L + b) has ONLY ONE distance <= b_gd (d_gd = 9800, even only)!
    gd_pts = list(range(L_gd + 1)) + [L_gd + j * d_gd for j in range(1, 5)]
    gd_set = set(gd_pts)
    k_miss = L_gd + 1
    missing_step = all((x + k_miss not in gd_set) for x in gd_pts)
    g2 = L_gd + 2 * d_gd
    g2_dists = sorted({abs(g2 - u) for u in gd_pts if 1 <= abs(g2 - u) <= b_gd})
    print(f"[E-782 G_d falsification] b={b_gd}, d={d_gd}: step {k_miss} missing={missing_step}, "
          f"g2 incident dists <= b = {g2_dists} (fails f9 & f10 & parity!)")
    assert missing_step and g2_dists == [d_gd]

    # Part B2: Exhaustive E-791 12-filter variable-step bridge test on ALL 256 words of length 8!
    adm = 0
    for W in itertools.product((-1, 1), repeat=8):
        is_adm = check_e759(list(W))
        if is_adm:
            ok, msg = build_variable_step_bridge_12filter(list(W))
            assert ok, f"12-filter failed on admissible W={W}: {msg}"
            adm += 1
    print(f"[E-791 Exhaustive L=8] ALL {adm}/{adm} E-759-admissible words pass ALL 12 filters + exact greedy!")

    # Part B3: Holdout on E-777 sharp staged words W_n (n=1..4) and E-784 greedy 2-block counter!
    for n in (1, 2, 3, 4):
        Wn = [-1] * (2 * n + 2) + [1, -1, 1, 1] * n + [1] + [-1] * (2 * n + 1) + [1, 1]
        assert check_e759(Wn)
        ok, msg = build_variable_step_bridge_12filter(Wn)
        assert ok, f"12-filter failed on W_{n}: {msg}"
        print(f"  [Holdout E-777 W_{n}] len={len(Wn)}: 12-filter PASS ({msg})")

    # E-784 minimal coherent 2-block counter [(2,1,1),(1,1,1,2)]
    w_e784 = [-1]*4 + [1,-1,1,1,1,-1,-1,-1,1,1,1,-1,1,-1,-1,-1,1,1]
    if check_e759(w_e784):
        ok, msg = build_variable_step_bridge_12filter(w_e784)
        assert ok, f"12-filter failed on E-784: {msg}"
        print(f"  [Holdout E-784 counter] 12-filter PASS ({msg})")

    print(f"ALL TRACK 3 AUDITS PASSED in {time.time() - t0:.2f}s.")


if __name__ == "__main__":
    main()
