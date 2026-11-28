#!/usr/bin/env python3
"""
Reproducible exact audit for E-796 (REFUTED):
  Refutes ALL upper-free-only overflow conjectures on actual EndN:
    - 3 * E_{r+1}       <= W(r) + C * F_{>= r-1}
    - 3 * E_{r+1} + E_r <= W(r) + C * F_{>= r-1}
  for EVERY constant C (both on padded BlockWord+A^16 prefixes and on empty prefix n=0),
  and simultaneously proves asymptotic constant-1 sharpness of E-794
  (3 * E_{r+1} + E_r <= W(r) + 3 * AA_{r-1}) with slack == 1 for ALL k >= 1!

Mechanism (exact D=13, L=1 two-potential resonance):
  dip  = S^13 ++ A S ++ A^11 ++ S A A ++ A      (len = 30, W(r) = 199, Delta p_{r-1} = -199, drop_{r-2} = 169)
  unit = dip ++ A ++ (A S)^66 ++ A ++ S S       (len = 166, E_{r+1} = 67, Delta p_{r-1} = +3, Delta p_{r-2} = +169)
  Because drop_{r-2}(dip) == Delta p_{r-2}(unit) == 169:
    - At every copy j >= 2, the AA exit d'_j at height r satisfies
      p_{r-2}(d'_j) = p_{r-2}(a_{0,j} + 1) - 169 = p_{r-2}(a_{0,j-1} + 1),
      so d'_j is SUPPLIED by the preceding copy's first descent step at height r - 1!
    - Meanwhile d_{1,j} = d'_j - 1 at height r - 1 is locally supplied by the trailing S A A window!
    - And all 67 height-(r+1) additions of copy j sit at p_{r-1} = 204 + 3*(j-1) - 198 + 3*i (i = 0..66),
      where i = 0..65 are supplied by earlier anchors and i = 66 sits at 204 + 3*(j-1),
      supplied by copy (j-1)'s trailing S S landing at height r!
    - Hence F_{>= r-1} stays STRICTLY CONSTANT (205 for n=16; 206 for n=0) as k -> infinity,
      while 3*E_{r+1} - W(r) = 2*k (n=16) and 3*E_{r+1} + E_r - W(r) = 3*k - 1 (n=16),
      matching E-794's W(r) + 3*AA_{r-1} = 202*k to exact slack 1 for ALL k >= 1!
"""


def build_unit():
    dip = "S" * 13 + "AS" + "A" * 11 + "SAA" + "A"
    assert len(dip) == 30
    unit = dip + "A" + "AS" * 66 + "A" + "SS"
    assert len(unit) == 166
    return dip, unit


def verify_unit_algebra(dip: str, unit: str):
    # Trace relative to height r = 16
    r = 16
    h = r
    w_dip = 0
    dp_r1_dip = 0
    dp_r2_dip = 0
    for c in dip:
        if c == "A" and h < r:
            w_dip += 2 * (r - h) - 1
        h += 1 if c == "A" else -1
        dp_r1_dip += h - r
        dp_r2_dip += h - (r - 1)
    assert h == r and w_dip == 199 and dp_r1_dip == -199 and dp_r2_dip == -169

    h = r
    dp_r1_u = 0
    dp_r2_u = 0
    for c in unit:
        h += 1 if c == "A" else -1
        dp_r1_u += h - r
        dp_r2_u += h - (r - 1)
    assert h == r and dp_r1_u == 3 and dp_r2_u == 169
    # Exact resonance identity: drop_{r-2}(dip) == Delta p_{r-2}(unit) == 169!
    assert -dp_r2_dip == dp_r2_u == 169
    print(
        f"[1] Exact unit algebra verified: |dip|=30, |unit|=166, W(r)=199, "
        f"dp_{{r-1}}(unit)=+{dp_r1_u}, dp_{{r-2}}(unit)=+{dp_r2_u} == drop_{{r-2}}(dip)={-dp_r2_dip}."
    )


def eval_family(pref: str, prefix_in_tail: str, unit: str, ks):
    r = 16
    rows = []
    for k in ks:
        tail = prefix_in_tail + "AS" * 204 + unit * k
        full = pref + tail
        N = len(full)
        n = len(pref)
        K = len(tail)
        Fw = [0] * (N + 1)
        for i, c in enumerate(full):
            Fw[i + 1] = Fw[i] + (1 if c == "A" else -1)
        assert min(Fw) >= 0, "Walk dropped below 0!"
        P = [0] * (N + 1)
        for i in range(N):
            P[i + 1] = P[i] + Fw[i + 1]
        End = [False] * N
        seen = set()
        for t in range(N):
            if full[t] == "A":
                hh = Fw[t] - 1
                if (hh, P[t] - t * hh) in seen:
                    End[t] = True
            seen.add((Fw[t], P[t] - t * Fw[t]))
        A, E, F, AA = {}, {}, {}, {}
        for t in range(n, n + K):
            hh = Fw[t]
            if full[t] == "A":
                A[hh] = A.get(hh, 0) + 1
                if End[t]:
                    E[hh] = E.get(hh, 0) + 1
                else:
                    F[hh] = F.get(hh, 0) + 1
                if t + 1 < n + K and full[t + 1] == "A":
                    AA[hh] = AA.get(hh, 0) + 1
        W_r = sum((2 * (r - hh) - 1) * c for hh, c in A.items() if hh < r)
        ep1 = E.get(r + 1, 0)
        er = E.get(r, 0)
        aa = AA.get(r - 1, 0)
        f_ge = sum(c for hh, c in F.items() if hh >= r - 1)
        rows.append((k, len(full), ep1, er, W_r, aa, f_ge, F.get(r - 1, 0), F.get(r, 0)))
    return rows


def main():
    dip, unit = build_unit()
    verify_unit_algebra(dip, unit)

    # Discovery & holdout checks on padded prefix pref = "A"^16 (n = 16)
    print("[2] Padded prefix pref='A'^16 (n=16, r=16):")
    for k, L, ep1, er, W_r, aa, f_ge, frm1, fr in eval_family("A" * 16, "", unit, [1, 5, 30, 100, 300, 500]):
        assert ep1 == 67 * k
        assert er == k - 1
        assert W_r == 199 * k
        assert aa == k
        assert f_ge == 205 and frm1 == 0 and fr == 205
        assert 3 * ep1 - W_r == 2 * k
        assert 3 * ep1 + er - W_r == 3 * k - 1
        assert (W_r + 3 * aa) - (3 * ep1 + er) == 1  # EXACT CONSTANT-1 SHARPNESS OF E-794!!
        print(
            f"    k={k:3d} (len={L:5d}): 3*E_{{17}}+E_{{16}}={3*ep1+er:6d}, W(16)={W_r:6d}, "
            f"3*E_{{17}}-W={3*ep1-W_r:+5d}, 3*E_{{17}}+E_{{16}}-W={3*ep1+er-W_r:+5d}, "
            f"F_{{>=15}}={f_ge} (CONST), E-794 slack={(W_r+3*aa)-(3*ep1+er)}"
        )

    # Empty prefix pref = "" (n = 0)
    print("[3] Empty prefix pref='' (n=0, r=16):")
    for k, L, ep1, er, W_r, aa, f_ge, frm1, fr in eval_family("", "A" * 16, unit, [86, 129, 200, 500]):
        assert ep1 == 67 * k
        assert er == k - 1
        assert W_r == 199 * k + 256
        assert aa == k + 1
        assert f_ge == 206 and frm1 == 1 and fr == 205
        assert 3 * ep1 + er - W_r == 3 * k - 257
        assert 3 * ep1 - W_r == 2 * k - 256
        assert (W_r + 3 * aa) - (3 * ep1 + er) == 260
        print(
            f"    k={k:3d} (len={L:5d}): 3*E_{{17}}-W={3*ep1-W_r:+5d}, "
            f"3*E_{{17}}+E_{{16}}-W={3*ep1+er-W_r:+5d}, F_{{>=15}}={f_ge} (CONST)"
        )

    # Negative control: off-resonance D = 12 breaks drop_{r-2} == dp_{r-2}, making d' FREE on every copy!
    dip12 = "S" * 12 + "AS" + "A" * 10 + "SAA" + "A"
    # Check W(r) of dip12 = 172 (== 1 mod 3), e4 = 58
    unit12 = dip12 + "A" + "AS" * 57 + "A" + "SS"
    rows12 = eval_family("A" * 15, "", unit12, [10, 50])
    # Extract F_{>=14} for r=15 directly
    def f_ge_for(D_val, unit_str, k_val):
        r = D_val + 3
        pref = "A" * r
        tail = "AS" * 204 + unit_str * k_val
        full = pref + tail
        N = len(full); n = len(pref)
        Fw = [0] * (N + 1)
        for i, c in enumerate(full): Fw[i + 1] = Fw[i] + (1 if c == "A" else -1)
        P = [0] * (N + 1)
        for i in range(N): P[i + 1] = P[i] + Fw[i + 1]
        seen = set(); f_ge = 0
        for t in range(N):
            if full[t] == "A":
                hh = Fw[t] - 1
                if t >= n and Fw[t] >= r - 1 and (hh, P[t] - t * hh) not in seen:
                    f_ge += 1
            seen.add((Fw[t], P[t] - t * Fw[t]))
        return f_ge
    f12_10 = f_ge_for(12, unit12, 10)
    f12_50 = f_ge_for(12, unit12, 50)
    assert f12_50 - f12_10 == 40, f"Expected linear growth +40 for off-resonance D=12, got {f12_50 - f12_10}"
    print(
        f"[4] Negative control (off-resonance D=12): F_{{>=r-1}}(k=10)={f12_10}, F_{{>=r-1}}(k=50)={f12_50} "
        f"(grows linearly +1/copy; exact D=13 resonance drop==dp==169 is essential!)."
    )
    print("ALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
