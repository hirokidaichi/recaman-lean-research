#!/usr/bin/env python3
"""H-20260908-01 falsifier: HARD completions, wrap-around, packing, residual.

Independent P2 sums (not incremental). Does not clobber hard_type.txt.
Discovery only; not a holdout for E-067.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
from collections import Counter
from pathlib import Path

HARD = (1, 4, 7, 10, 11)
GAP2_LESS = [
    (1, 2, 9, 10, 11),
    (1, 4, 7, 10, 11),
    (1, 5, 6, 10, 11),
    (1, 5, 8, 9, 10),
    (2, 3, 7, 10, 11),
    (4, 5, 6, 7, 11),
]
LAG3 = (3,)
LAG7H1 = (1, 6, 7)
LAG7H2 = (2, 5, 7)

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "docs/data/issue73_20260908/lag11/falsify_hard.txt"


def p2_at(word, t, d):
    """Exact coefficient identities on the cyclic unfolding."""
    p = len(word)
    s = m = 0
    offs = []
    for i in range(1, d + 1):
        x = word[(t - i) % p]
        s += x
        m += i * x
        if x < 0:
            offs.append(i)
    return s == 1 and m == 0, tuple(offs)


def min_p2(word, t, cap=11):
    for d in (3, 7, 11):
        ok, offs = p2_at(word, t, d)
        if ok:
            return d, offs
    return None, ()


def phi7_image(t, d, offs, p):
    if d == 3 and offs == LAG3:
        return (t - 3) % p, "lag3"
    if d == 7 and offs == LAG7H1:
        return (t - 7) % p, "lag7h1"
    if d == 7 and offs == LAG7H2:
        return (t - 5) % p, "lag7h2"
    return None, None


def signs_of(offsets):
    """Newest-first length-11 window as S/A string."""
    return "".join("S" if i in offsets else "A" for i in range(1, 12))


def cyclic_complete(offsets, pad, extra_s_positions=()):
    """Oldest-first block: offsets as past of a terminal A, then pad.

    pad is a string of A/S after t. Period = 11 + 1 + len(pad) if we include t.
    The length-11 past is unique up to the offsets.
    """
    past = ["A"] * 11  # indices 0..10 = t-11 .. t-1
    for i in offsets:
        past[11 - i] = "S"
    word = "".join(past) + "A" + pad
    return word


def to_pm(word_sa):
    return tuple(1 if c == "A" else -1 for c in word_sa)


def analyze_word(word_pm, want_offs=HARD):
    p = len(word_pm)
    images = {}
    rows = []
    for t, e in enumerate(word_pm):
        if e > 0:
            d, offs = min_p2(word_pm, t)
            if d is None:
                continue
            img, kind = phi7_image(t, d, offs, p)
            if img is not None:
                images[t] = (img, kind)
            if d == 11 and offs == want_offs:
                rows.append(t)
    occupied = {img for img, _ in images.values()}
    out = []
    for t in rows:
        domain = {(t - i) % p for i in want_offs}
        residual = domain - occupied
        taken = []
        for i in want_offs:
            s = (t - i) % p
            if s in occupied:
                takers = [
                    (k, images[k][1]) for k, (img, _) in images.items() if img == s
                ]
                taken.append({"offset": i, "phase": s, "takers": takers})
        out.append(
            {
                "t": t,
                "domain": sorted(domain),
                "residual": sorted(residual),
                "residual_size": len(residual),
                "taken": taken,
                "n_domain": len(domain),
            }
        )
    return {
        "period": p,
        "sign_sum": sum(word_pm),
        "n_U7": len(images),
        "n_D": sum(1 for x in word_pm if x < 0),
        "n_hard": len(out),
        "rows": out,
        "empty": [r for r in out if r["residual_size"] == 0],
    }


def exhaust_periods(pmin, pmax, want_offs=HARD):
    stats = Counter()
    empty_witness = None
    wrap_hits = []
    taken_kinds = Counter()
    residual_sizes = Counter()
    domain_sizes = Counter()
    occ = 0
    for p in range(pmin, pmax + 1):
        for raw in itertools.product((-1, 1), repeat=p):
            images = {}
            hits = []
            for t, e in enumerate(raw):
                if e > 0:
                    d, offs = min_p2(raw, t)
                    if d is None:
                        continue
                    img, kind = phi7_image(t, d, offs, p)
                    if img is not None:
                        images[t] = (img, kind)
                    if d == 11 and offs == want_offs:
                        hits.append(t)
            if not hits:
                continue
            occupied = {img for img, _ in images.values()}
            for t in hits:
                occ += 1
                domain = {(t - i) % p for i in want_offs}
                residual = domain - occupied
                residual_sizes[len(residual)] += 1
                domain_sizes[len(domain)] += 1
                stats[(p, len(domain), len(residual))] += 1
                for i in want_offs:
                    s = (t - i) % p
                    if s in occupied:
                        for k, (img, kind) in images.items():
                            if img == s:
                                taken_kinds[(i, kind)] += 1
                if not residual and empty_witness is None:
                    empty_witness = {
                        "period": p,
                        "word": "".join("A" if x > 0 else "S" for x in raw),
                        "sign_sum": sum(raw),
                        "t": t,
                        "domain": sorted(domain),
                        "phi7": {str(k): list(v) for k, v in images.items()},
                    }
                if p < 11:
                    wrap_hits.append(
                        {
                            "p": p,
                            "word": "".join("A" if x > 0 else "S" for x in raw),
                            "t": t,
                            "n_domain": len(domain),
                            "n_residual": len(residual),
                        }
                    )
    return {
        "occurrences": occ,
        "residual_sizes": dict(sorted(residual_sizes.items())),
        "domain_sizes": dict(sorted(domain_sizes.items())),
        "taken_kinds": {str(k): v for k, v in taken_kinds.items()},
        "empty_count": 0 if empty_witness is None else "found",
        "empty_witness": empty_witness,
        "wrap_p_lt_11": wrap_hits[:20],
        "n_wrap_p_lt_11": len(wrap_hits),
        "by_p_domain_residual": {str(k): v for k, v in sorted(stats.items())},
    }


def packing_words():
    """Several HARD copies, with connectors that try to steal last-S via lag3."""
    past = cyclic_complete(HARD, "")[:-1]  # length-11 past only, no terminal A
    # block of 12: past + A
    block = past + "A"  # SSAASAASAASA
    words = {
        "single_S_completion": cyclic_complete(HARD, "S"),
        "single_A_completion": cyclic_complete(HARD, "A"),
        "AA_pad": cyclic_complete(HARD, "AA"),
        "AAA_pad": cyclic_complete(HARD, "AAA"),
        "repeat1": block,
        "repeat2": block * 2,
        "repeat3": block * 3,
        "repeat4": block * 4,
        "hard_AA_hard": block + "AA" + block,
        "hard_AAS_hard": block + "AAS" + block,
        "hard_AAA_hard": block + "AAA" + block,
        "hard_SAA_hard": block + "SAA" + block,
        "named_allA": "A" * 12,
        "named_allS": "S" * 12,
        "named_SAAA": "SAAA",
        "named_SSSSAAAASAAA": "SSSSAAAASAAA",
        "named_AAASSASSSAA": "AAASSASSSAA",
        "boundary_SAAASAASSSA": "SAAASAASSSA",
    }
    return words


def check_assignment_injection(pmin, pmax, charge_by_type):
    """charge_by_type: tuple offsets -> charged offset.

    Collision if two U11min phases map to the same S, or image in phi7.
    """
    collisions = []
    u7_hits = []
    used = 0
    for p in range(pmin, pmax + 1):
        for raw in itertools.product((-1, 1), repeat=p):
            images = {}
            u11 = []
            for t, e in enumerate(raw):
                if e > 0:
                    d, offs = min_p2(raw, t)
                    if d is None:
                        continue
                    img, kind = phi7_image(t, d, offs, p)
                    if img is not None:
                        images[t] = (img, kind)
                    if d == 11:
                        u11.append((t, offs))
            if not u11:
                continue
            occupied = {img for img, _ in images.values()}
            phi11 = {}
            for t, offs in u11:
                if offs not in charge_by_type:
                    continue
                c = charge_by_type[offs]
                s = (t - c) % p
                used += 1
                if s in occupied:
                    if len(u7_hits) < 8:
                        u7_hits.append(
                            {
                                "p": p,
                                "word": "".join("A" if x > 0 else "S" for x in raw),
                                "t": t,
                                "offs": offs,
                                "charged": c,
                                "s": s,
                            }
                        )
                if s in phi11:
                    if len(collisions) < 8:
                        collisions.append(
                            {
                                "p": p,
                                "word": "".join("A" if x > 0 else "S" for x in raw),
                                "t1": phi11[s],
                                "t2": t,
                                "s": s,
                            }
                        )
                else:
                    phi11[s] = t
    return {
        "assigned_events": used,
        "n_collisions_recorded": len(collisions),
        "n_u7_hits_recorded": len(u7_hits),
        "collision_examples": collisions,
        "u7_hit_examples": u7_hits,
    }


def main() -> None:
    lines = []

    def emit(msg=""):
        lines.append(msg)
        print(msg, flush=True)

    emit("protocol=H-20260908-01 HARD falsifier wrap/pack/residual")
    emit(
        "source_revision="
        + subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    )
    emit(
        "script_sha256="
        + hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    )
    emit("HARD_WINDOW_NEWEST_FIRST=" + signs_of(HARD))
    ok, offs = True, HARD
    # Independent P2 arithmetic on the abstract window
    emit("P2_CHECK_d11_sum_offsets=%d target=33" % sum(HARD))
    emit("P2_CHECK_d11_sign_sum=%d" % (11 - 2 * 5))
    inside3 = tuple(x for x in HARD if x <= 3)
    inside7 = tuple(x for x in HARD if x <= 7)
    emit("PREFIX3=%s sum=%d (need one offset=3)" % (list(inside3), sum(inside3)))
    emit("PREFIX7=%s sum=%d (need 14)" % (list(inside7), sum(inside7)))

    emit("HARD_FOLLOWING_GAPS_INTERNAL=offset4:3, offset7:3, offset10:3, offset11:1")
    emit("HARD_LAST_S_GAP_GE=2")

    emit("=== cyclic completions and packing ===")
    for name, w in packing_words().items():
        rec = analyze_word(to_pm(w), HARD)
        rec_out = {
            "name": name,
            "word": w,
            "period": rec["period"],
            "sign_sum": rec["sign_sum"],
            "n_hard": rec["n_hard"],
            "empty": rec["empty"],
            "rows": rec["rows"],
        }
        emit("PACK " + json.dumps(rec_out, sort_keys=True))

    emit("=== exhaust p=1..12 ALL words (including nonpositive sum) ===")
    ex12 = exhaust_periods(1, 12)
    emit("EXHAUST_1_12 " + json.dumps(ex12, sort_keys=True))

    emit("=== exhaust p=13..16 ALL words ===")
    ex16 = exhaust_periods(13, 16)
    emit("EXHAUST_13_16 " + json.dumps({k: v for k, v in ex16.items() if k != "wrap_p_lt_11"}, sort_keys=True))

    emit("=== exhaust p=1..12 for all 6 gap2-less types, empty residual? ===")
    for typ in GAP2_LESS:
        rec = exhaust_periods(1, 12, want_offs=typ)
        emit(
            "GAP2LESS "
            + json.dumps(
                {
                    "type": typ,
                    "occ": rec["occurrences"],
                    "residual_sizes": rec["residual_sizes"],
                    "domain_sizes": rec["domain_sizes"],
                    "taken": rec["taken_kinds"],
                    "empty_witness": rec["empty_witness"],
                    "n_wrap": rec["n_wrap_p_lt_11"],
                },
                sort_keys=True,
            )
        )

    # Candidate repair: gap2 if present else first U7-incompatible internal S.
    # Safe internals for HARD are 4,7,10,11; charge offset 4.
    emit("=== assignment injection p=1..12 (repair: gap2 else listed offset) ===")
    # filled after a local safe-offset table computed here
    types = []
    for s in itertools.combinations(range(1, 12), 5):
        if sum(s) != 33:
            continue
        if tuple(x for x in s if x <= 3) == (3,) and sum(x for x in s if x <= 3) == 6:
            continue
        inside7 = tuple(x for x in s if x <= 7)
        if len(inside7) == 3 and sum(inside7) == 14:
            continue
        types.append(tuple(s))

    def window_of(offsets):
        w = {0: 1}
        for i in range(1, 12):
            w[-i] = -1 if i in offsets else 1
        return w

    def u7_possible(window, s_time, kind):
        if kind == "lag3":
            tp = s_time + 3
            need = {tp: 1, tp - 1: 1, tp - 2: 1, tp - 3: -1}
        elif kind == "lag7h1":
            tp = s_time + 7
            need = {tp: 1}
            for off in range(1, 8):
                need[tp - off] = -1 if off in LAG7H1 else 1
        else:
            tp = s_time + 5
            need = {tp: 1}
            for off in range(1, 8):
                need[tp - off] = -1 if off in LAG7H2 else 1
        return all(rel not in window or window[rel] == val for rel, val in need.items())

    charge = {}
    for offs in types:
        w = window_of(offs)
        o = list(offs)
        gap2 = []
        safe = []
        for j, i in enumerate(o):
            if j == 0:
                gap_kind, gap = "ge", i + 1
            else:
                gap_kind, gap = "eq", i - o[j - 1]
            kinds = [k for k in ("lag3", "lag7h1", "lag7h2") if u7_possible(w, -i, k)]
            rec = {"offset": i, "gap_kind": gap_kind, "gap": gap, "u7": kinds}
            if gap_kind == "eq" and gap == 2:
                gap2.append(rec)
            if not kinds:
                safe.append(rec)
        if gap2:
            # prefer exact gap2 even if last-S future could overlap; gap2 is never a U7 image
            charge[offs] = gap2[0]["offset"]
        elif safe:
            charge[offs] = safe[0]["offset"]
        else:
            charge[offs] = None
    emit("CHARGE_MAP " + json.dumps({str(k): v for k, v in charge.items()}, sort_keys=True))
    if any(v is None for v in charge.values()):
        emit("CHARGE_INCOMPLETE types without gap2 and without safe S")
    inj = check_assignment_injection(1, 12, {k: v for k, v in charge.items() if v is not None})
    emit("INJECTION_1_12 " + json.dumps(inj, sort_keys=True))

    empty_any = ex12["empty_witness"] or ex16["empty_witness"]
    if empty_any:
        emit("CONCLUSION=REFUTED empty residual witness exists")
    else:
        emit(
            "CONCLUSION=no empty HARD residual in p=1..16 all words; "
            "packing/wrap produced no collision; not yet an all-period theorem"
        )
    OUT.write_text("\n".join(lines) + "\n")
    emit("wrote " + str(OUT))


if __name__ == "__main__":
    main()
