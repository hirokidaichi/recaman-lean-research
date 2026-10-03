#!/usr/bin/env python3
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_qw import W1, complete_u, donor_info, hall, nbd, past, sign


def bits(text):
    return tuple(c == "A" for c in text)


q_text = "SSAASAAA"
q_word = bits(q_text)
q_U, q_lag = complete_u(q_word)
q_u0 = 3
q_B = (7,)
q_info = donor_info(q_word, q_u0, q_lag)
q_N = nbd(q_word, q_B, q_lag)
q = {
    "word": q_text,
    "signSum": sum(map(sign, q_word)),
    "U": q_U,
    "lags": tuple((u, q_lag[u]) for u in q_U),
    "Hall": hall(q_word, q_U, q_lag),
    "donor": q_u0,
    "donor_info": q_info,
    "B": q_B,
    "N_B": tuple(sorted(q_N)),
    "tight": len(q_N) == len(q_B),
    "avoids_donor": q_u0 not in q_B,
    "true_oldest_uncovered": q_info[2] not in q_N,
}
assert q["signSum"] > 0 and q["Hall"] and q["tight"] and q["avoids_donor"]
assert q_lag[q_u0] == 11 and q_info[0] == "ASSAAASAASS" and q_info[1:] == (11, 0)
assert all(q_lag[b] in (3, 7, 11) for b in q_B) and q["true_oldest_uncovered"]

w_text = "SSAAAASAAA"
w_word = bits(w_text)
w_U, w_lag = complete_u(w_word)
w_B = (4, 7, 9)
w_t = 7
w_N = nbd(w_word, w_B, w_lag)
w_past = "".join("A" if b else "S" for b in past(w_word, w_t, 7))
w = {
    "word": w_text,
    "signSum": sum(map(sign, w_word)),
    "U": w_U,
    "lags": tuple((u, w_lag[u]) for u in w_U),
    "Hall": hall(w_word, w_U, w_lag),
    "B": w_B,
    "N_B": tuple(sorted(w_N)),
    "tight": len(w_N) == len(w_B),
    "B_lags_3_or_7": all(w_lag[b] in (3, 7) for b in w_B),
    "t": w_t,
    "lag_t": w_lag[w_t],
    "past_t_7": w_past,
    "next_sign": "A" if w_word[(w_t + 1) % len(w_word)] else "S",
}
assert w["signSum"] > 0 and w["Hall"] and w["tight"] and w["B_lags_3_or_7"]
assert w_t in w_B and w["lag_t"] == 7 and w_past == W1 and w["next_sign"] == "A"

print("Q_P8_VALIDATED", q)
print("W_P10_VALIDATED", w)
