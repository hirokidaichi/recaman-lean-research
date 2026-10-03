#!/usr/bin/env python3
"""Independent fixed controls for the 2026-09-24 weekly audit.

No search ranges or holdout claims: only named finite witnesses and weakened-premise attacks.
"""

import json


def past(word, t, d):
    p = len(word)
    return "".join(word[(t - k) % p] for k in range(1, d + 1))


def p2(bits):
    vals = [1 if bit == "A" else -1 for bit in bits]
    return sum(vals) == 1 and sum((i + 1) * val for i, val in enumerate(vals)) == 0


def ss_count(bits):
    return sum(bits[i : i + 2] == "SS" for i in range(len(bits) - 1))


def minimum_p2_lag(word, u, cap=None):
    if cap is None:
        cap = len(word) * (len(word) + 1)
    return next((d for d in range(1, cap + 1) if p2(past(word, u, d))), None)


def neighborhood(word, windows):
    p = len(word)
    return sorted({(u - k) % p for u, d in windows for k in range(1, d + 1)
                   if word[(u - k) % p] == "S"})


def true_oldest(word, u, d):
    bits = past(word, u, d)
    offset = max(k for k, bit in enumerate(bits, 1) if bit == "S")
    return offset, (u - offset) % len(word)


def row(word, u0, windows):
    donor = past(word, u0, 11)
    offset, phase = true_oldest(word, u0, 11)
    n = neighborhood(word, windows)
    return {
        "word": word,
        "p": len(word),
        "positive_mass": word.count("A") - word.count("S"),
        "donor_clock": u0,
        "donor_word": donor,
        "donor_p2": p2(donor),
        "donor_min_lag": minimum_p2_lag(word, u0),
        "donor_ss": ss_count(donor),
        "true_oldest_offset": offset,
        "true_oldest_phase": phase,
        "windows": windows,
        "all_windows_current_A": all(word[u] == "A" for u, _ in windows),
        "all_windows_p2": all(p2(past(word, u, d)) for u, d in windows),
        "all_windows_minimal": all(minimum_p2_lag(word, u) == d for u, d in windows),
        "neighborhood": n,
        "tight": len(n) == len(windows),
        "deleted": [x for x in n if x != phase],
        "deletion_hall": len(windows) <= len([x for x in n if x != phase]),
    }


def main():
    p8 = "SSAASAAA"
    print(json.dumps({"name": "p8_tight", **row(p8, 3, [(7, 3)])}, sort_keys=True))
    print(json.dumps({"name": "p8_slack_single", **row(p8, 3, [(3, 11)])}, sort_keys=True))
    print(json.dumps({"name": "p8_slack_full", **row(p8, 3, [(3, 11), (7, 3)])}, sort_keys=True))

    p12 = "AAAASAAASSSS"
    print(json.dumps({"name": "ss3_deletion_failure", **row(p12, 3, [(2, 3), (5, 7), (7, 3)])}, sort_keys=True))

    p18 = "AAAASSAAAASAAASASS"
    print(json.dumps({"name": "e240_non_pure_aas", **row(p18, 7, [(2, 3), (8, 3), (11, 7), (13, 3)])}, sort_keys=True))

    p69 = "SSSSAAAASAAA"
    l7 = minimum_p2_lag(p69, 7)
    l11 = minimum_p2_lag(p69, 11)
    print(json.dumps({
        "name": "e069_oldest_not_injective",
        "word": p69,
        "lags": {"7": l7, "11": l11},
        "oldest7": true_oldest(p69, 7, l7),
        "oldest11": true_oldest(p69, 11, l11),
    }, sort_keys=True))

    p15 = "SAAASSSASASASAAA"
    bits15 = past(p15, 15, 15)
    off15, phase15 = true_oldest(p15, 15, 15)
    print(json.dumps({
        "name": "length15_false_offset11",
        "word": p15,
        "donor_word": bits15,
        "p2": p2(bits15),
        "ss": ss_count(bits15),
        "proper_p2_prefixes": [d for d in range(1, 15) if p2(bits15[:d])],
        "true_oldest_offset": off15,
        "true_oldest_phase": phase15,
        "fixed_offset11_phase": (15 - 11) % len(p15),
        "N": neighborhood(p15, [(3, 3)]),
    }, sort_keys=True))

    # W becomes false if onto is removed: the lone w1 member owns its oldest S,
    # but its newest S has no owner and the next sign can be S.
    bits = {0: "A", -1: "S", -2: "A", -3: "A", -4: "A", -5: "A", -6: "S", -7: "S", 1: "S"}
    print(json.dumps({
        "name": "ownerfamily_without_onto",
        "window": "".join(bits[-k] for k in range(1, 8)),
        "member_current_A": bits[0] == "A",
        "owned_offset": 7,
        "next_sign": bits[1],
        "onto_newest_S": False,
        "w_conclusion": bits[1] == "A",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
