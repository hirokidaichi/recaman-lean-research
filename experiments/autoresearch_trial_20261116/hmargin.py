"""Python access to hmargin.c plus an independent naive reference.

Search evaluator for the H conjecture (E-509).  OBSERVED/COMPUTED only.
"""
from __future__ import annotations

import ctypes
import itertools
import os
import random
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
LIB = HERE / "libhmargin.so"


def _build() -> None:
    src = HERE / "hmargin.c"
    if not LIB.exists() or LIB.stat().st_mtime < src.stat().st_mtime:
        subprocess.run(["cc", "-O2", "-shared", "-fPIC", "-o", str(LIB), str(src)], check=True)


_build()
_lib = ctypes.CDLL(str(LIB))
_lib.h_margin.restype = ctypes.c_int
_lib.h_margin.argtypes = [ctypes.c_char_p, ctypes.c_int, ctypes.POINTER(ctypes.c_int),
                          ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_long)]
_lib.h_endable.restype = ctypes.c_int
_lib.h_endable.argtypes = [ctypes.c_char_p, ctypes.c_int]
_lib.h_unclean.restype = ctypes.c_int
_lib.h_unclean.argtypes = [ctypes.c_char_p, ctypes.c_int]


_lib.h_longwin.restype = ctypes.c_int
_lib.h_longwin.argtypes = [ctypes.c_char_p, ctypes.c_int, ctypes.c_int]


def longwin(word: str, lmin: int = 32) -> int:
    """Endable A clocks whose shortest window has length >= lmin (E-372 needs >= 32)."""
    return _lib.h_longwin(word.encode(), len(word), lmin)


def unclean(word: str) -> int:
    """Endable A clocks whose shortest window is unclean (E-511 sense)."""
    return _lib.h_unclean(word.encode(), len(word))


def margin(word: str) -> tuple[int, int, int, int]:
    """(max_{p<k}(e-s), p, k, #tight intervals).  H holds on word iff result[0] <= 0."""
    p, k, t = ctypes.c_int(), ctypes.c_int(), ctypes.c_long()
    m = _lib.h_margin(word.encode(), len(word), ctypes.byref(p), ctypes.byref(k), ctypes.byref(t))
    return m, p.value, k.value, t.value


def endable(word: str) -> int:
    return _lib.h_endable(word.encode(), len(word))


# ---------- independent naive reference (different code path) ----------

def naive_margin(word: str) -> int:
    n = len(word)
    best = -10**9
    for p in range(n):
        for k in range(p + 1, n + 1):
            sub = word[p:k]
            # heights relative to p
            F = [0]
            for c in sub:
                F.append(F[-1] + (1 if c == "A" else -1))
            e = 0
            for b, c in enumerate(sub):
                if c != "A":
                    continue
                ok = False
                for t in range(b - 1, -1, -1):
                    L = b - t
                    if L % 4 != 3:
                        continue
                    if F[b] - F[t] != 1:
                        continue
                    if sum(F[u] - F[t] for u in range(t + 1, b + 1)) == 0:
                        ok = True
                        break
                e += ok
            s = sub.count("S")
            best = max(best, e - s)
    return best


def self_test(nmax: int = 14, random_trials: int = 300) -> None:
    for n in range(1, nmax + 1):
        worst = max(margin("".join(w))[0] for w in itertools.product("AS", repeat=n))
        assert worst <= 0, (n, worst)
    rng = random.Random(20261116)
    for _ in range(random_trials):
        n = rng.randint(1, 26)
        w = "".join(rng.choice("AS") for _ in range(n))
        assert margin(w)[0] == naive_margin(w), w
    # H+ counterexample from E-511: H itself holds (e=11, S=13 on the whole word).
    w = "SAAASSSSAAAASASSSAAASAAASSAAAASAAA"
    assert margin(w)[0] <= 0 and endable(w) == 11 and w.count("S") == 13
    # E-511 reports unclean 3 for this word, so H+ (e + #unclean <= s) fails: 11 + 3 > 13.
    assert unclean(w) == 3, unclean(w)
    # longwin: SAAA has a length-3 window; a length-35 window needs a deep excursion.
    assert longwin("SAAA", 3) == 1 and longwin("SAAA", 4) == 0
    rng2 = random.Random(7)
    for _ in range(200):  # longwin(L) is non-increasing in L and bounded by endable()
        w2 = "".join(rng2.choice("AS") for _ in range(rng2.randint(1, 60)))
        vals = [longwin(w2, L) for L in (1, 3, 7, 11, 32)]
        assert vals == sorted(vals, reverse=True) and vals[0] == endable(w2), w2
    print(f"self_test ok: exhaustive n<={nmax} margin<=0, {random_trials} random words agree with naive")


if __name__ == "__main__":
    self_test()
