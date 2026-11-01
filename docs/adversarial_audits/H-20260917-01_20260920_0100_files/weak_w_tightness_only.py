#!/usr/bin/env python3
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_qw import W1, complete_u, hall, nbd, past, sign

word_text = "SSAAAASA"
word = tuple(c == "A" for c in word_text)
p = len(word)
U, lag = complete_u(word)
B = (7,)
t = 7
N = nbd(word, B, lag)

facts = {
    "p": p,
    "word": word_text,
    "signSum": sum(map(sign, word)),
    "periodic_extension": True,
    "U_complete": U,
    "U_nodup": len(U) == len(set(U)),
    "minimal_lags": tuple((u, lag[u]) for u in U),
    "Hall_all_subsets": hall(word, U, lag),
    "B": B,
    "B_sub_U": all(b in U for b in B),
    "B_lags_3_or_7": all(lag[b] in (3, 7) for b in B),
    "N_B": tuple(sorted(N)),
    "tight": len(N) == len(B),
    "phase_t_in_B": t % p in B,
    "lag_phase_t": lag[t % p],
    "past_t_7": "".join("A" if b else "S" for b in past(word, t, 7)),
    "expected_w1": W1,
    "next_sign": "A" if word[(t + 1) % p] else "S",
}

assert facts["signSum"] > 0
assert facts["U_nodup"] and facts["Hall_all_subsets"]
assert facts["B_sub_U"] and facts["B_lags_3_or_7"]
assert not facts["tight"]
assert facts["phase_t_in_B"] and facts["lag_phase_t"] == 7
assert facts["past_t_7"] == W1 and facts["next_sign"] == "S"
print(facts)
print("VERDICT weakened-W-without-tightness=REFUTED; all other card/W assumptions checked")
