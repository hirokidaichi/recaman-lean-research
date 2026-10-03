#!/usr/bin/env python3
"""Replay only the fixed H-20260921-01 semantic-audit controls."""

import hashlib
import importlib.util
from pathlib import Path


BASELINE = Path("experiments/issue73_20260920/baseline_q_w.py")
REVISION = "08c08565c743f39350c9b959e1df7d30aa1cae5d"


def load_baseline():
    spec = importlib.util.spec_from_file_location("baseline_q_w", BASELINE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def fixed_row(base, label, word, u0, members, subset):
    full = base.full_u(word)
    lag, donor_word, _cover, oldest, _offset = full[u0]
    neighborhood = base.neighborhood(full, subset)
    deleted = neighborhood - {oldest}
    row = {
        "p": len(word),
        "positive_mass": 2 * word.count("A") - len(word),
        "fullU": sorted(full),
        "U": members,
        "B": subset,
        "B_sub_U": all(x in members for x in subset),
        "U_nodup": len(set(members)) == len(members),
        "all_U_short": all(u in full and full[u][0] in (3, 7, 11) for u in members),
        "all_U_minimal_P2": all(u in full for u in members),
        "donor": u0,
        "donor_lag": lag,
        "donor_ss": base.ss_count(donor_word),
        "donor_word": donor_word,
        "true_oldest": oldest,
        "N": sorted(neighborhood),
        "tight": len(neighborhood) == len(subset),
        "deletedN": sorted(deleted),
        "removed": oldest in neighborhood,
        "conclusion": len(subset) <= len(deleted),
    }
    print(label, row)


def main():
    base = load_baseline()
    print("PROTOCOL fixed_named_words_only discovery=none holdout=none seed=none")
    print("REVISION", REVISION)
    print("BASELINE_SHA256", hashlib.sha256(BASELINE.read_bytes()).hexdigest())
    fixed_row(base, "Q_P8_TIGHT", "SSAASAAA", 3, [7], [7])
    fixed_row(base, "Q_P8_DONOR_CONTAINING", "SSAASAAA", 3, [3, 7], [3])
    fixed_row(base, "Q_P8_DONOR_CONTAINING", "SSAASAAA", 3, [3, 7], [3, 7])
    fixed_row(base, "E240_SCOPE_CONTROL", "AAAASSAAAASAAASASS", 7,
              sorted(base.full_u("AAAASSAAAASAAASASS")), [2, 8, 11, 13])
    fixed_row(base, "SS3_SCOPE_NEGATIVE", "AAAASAAASSSS", 3, [2, 5, 7], [2, 5, 7])
    fixed_row(base, "NON_TIGHT_SLACK", "AAAASASASSS", 3, [5], [5])
    print("EMPTY_B_BOUNDARY", {"B": [], "length": 0, "deleted_length": 0, "conclusion": True})
    print("DUPLICATE_U_SCOPE_NEGATIVE", {"U": [7, 7], "nodup": False})
    proper_word = "SSAAAASAAAAAAAAASAAA"
    donors = [
        u for u in range(len(proper_word))
        if base.p2(base.past(proper_word, u, 11))
        and base.ss_count(base.past(proper_word, u, 11)) == 2
        and all(not base.p2(base.past(proper_word, u, d)) for d in range(1, 11))
    ]
    print("PROPER_U_P20_SCOPE_NEGATIVE", {
        "word": proper_word,
        "fullU": sorted(base.full_u(proper_word)),
        "B": [4, 7, 9],
        "minimal_lag11_ss2_donor_phases": donors,
    })


if __name__ == "__main__":
    main()
