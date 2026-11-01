#!/usr/bin/env python3
"""Independent finite controls for the 01:30 repair audit.

These are regression/countermodel recomputations, not a proof or a holdout.
The newest-first conventions are transcribed from the Lean definitions.
"""

from itertools import combinations
import hashlib
import json
import subprocess


def word(text):
    return tuple(ch == "A" for ch in text)


def render(bits):
    return "".join("A" if bit else "S" for bit in bits)


def p2(bits):
    signs = tuple(1 if bit else -1 for bit in bits)
    return sum(signs) == 1 and sum((i + 1) * sign for i, sign in enumerate(signs)) == 0


def minimal_p2(bits):
    return p2(bits) and all(not p2(bits[:d]) for d in range(1, len(bits)))


def ss_count(bits):
    return sum((not bits[i]) and (not bits[i + 1]) for i in range(len(bits) - 1))


def past(cycle, clock, lag):
    return tuple(cycle[(clock - 1 - i) % len(cycle)] for i in range(lag))


def s_offsets(bits):
    return tuple(i + 1 for i, bit in enumerate(bits) if not bit)


def oldest_offset(bits):
    return max(s_offsets(bits), default=0)


def minimal_lag(cycle, clock, cap=None):
    limit = cap if cap is not None else len(cycle) * (len(cycle) + 1)
    for lag in range(1, limit + 1):
        if p2(past(cycle, clock, lag)):
            return lag
    return None


def supplies(text):
    cycle = word(text)
    result = {}
    for phase, bit in enumerate(cycle):
        if not bit:
            continue
        lag = minimal_lag(cycle, phase)
        if lag is None:
            continue
        window = past(cycle, phase, lag)
        result[phase] = {
            "lag": lag,
            "window": render(window),
            "minimal": minimal_p2(window),
            "covered": sorted((phase - off) % len(cycle) for off in s_offsets(window)),
        }
    return result


def neighborhood(supply, subset):
    covered = set()
    for phase in subset:
        covered.update(supply[phase]["covered"])
    return sorted(covered)


def hall(supply, universe):
    universe = tuple(universe)
    for size in range(len(universe) + 1):
        for subset in combinations(universe, size):
            if len(neighborhood(supply, subset)) < len(subset):
                return False
    return True


def merge(env, endpoint, bits):
    out = dict(env)
    placements = [(endpoint, True)] + [
        (endpoint - 1 - i, bit) for i, bit in enumerate(bits)
    ]
    for clock, bit in placements:
        if clock in out and out[clock] != bit:
            return None
        out[clock] = bit
    return out


def compatible_owners(root_bits, subtraction_clock, owner_words):
    root = merge({}, 0, root_bits)
    found = []
    for name, bits in owner_words:
        for offset in s_offsets(bits):
            endpoint = subtraction_clock + offset
            if merge(root, endpoint, bits) is not None:
                found.append([name, endpoint, offset])
    return found


def donor_w1_overlap(donor, w1):
    donor_env = merge({}, 0, donor)
    target = -oldest_offset(donor)
    found = []
    for offset in s_offsets(w1):
        endpoint = target + offset
        merged = merge(donor_env, endpoint, w1)
        if merged is not None:
            found.append([endpoint, offset, "A" if merged.get(endpoint + 1, True) else "S"])
    return found


def case(text, subset):
    supply = supplies(text)
    return {
        "period": len(text),
        "supply_phases": sorted(supply),
        "supply": supply,
        "B": subset,
        "N": neighborhood(supply, subset),
        "tight": len(neighborhood(supply, subset)) == len(subset),
        "hall_on_full_supply": hall(supply, sorted(supply)),
    }


aas = word("AAS")
w1 = word("SAAAASS")
w2 = word("ASAASAS")
donor_texts = (
    "AAASSSASASA",
    "ASAAASSSASA",
    "ASASAAASSSA",
    "ASSAAAASSAS",
    "ASSAAASAASS",
    "SAAASAASSSA",
    "SAAASSAAASS",
)
donors = tuple(word(text) for text in donor_texts)

head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
source = open("Recaman/ShortTightDonorAvoidance.lean", "rb").read()

out = {
    "head": head,
    "short_tight_sha256": hashlib.sha256(source).hexdigest(),
    "donor_offsets": [oldest_offset(donor) for donor in donors],
    "donor_minimal_p2": [minimal_p2(donor) for donor in donors],
    "donor_ss_count": [ss_count(donor) for donor in donors],
    "fixed_offset_11_bits": [render(donor)[10] for donor in donors],
    "local_older_s_owners": compatible_owners(w1, -7, (("AAS", aas), ("w1", w1), ("w2", w2))),
    "local_newest_s_owners": compatible_owners(w1, -1, (("AAS", aas), ("w1", w1), ("w2", w2))),
    "donor_w1_overlaps": [
        {"donor": text, "oldest": oldest_offset(bits), "overlaps": donor_w1_overlap(bits, w1)}
        for text, bits in zip(donor_texts, donors)
    ],
    "p15_false_offset": case("AAAASAAASASASSS", [3]),
    "e240": case("AAAASSAAAASAAASASS", [2, 8, 11, 13]),
    "ss3_weakening": case("AAAASAAASSSS", [7]),
    "not_tight": case("AAAASASASSS", [5]),
    "w_without_tightness": case("SSAAAASA", [7]),
    "w_positive": case("SSAAAASAAA", [4, 7, 9]),
    "proper_u": case("SSAAAASAAAAAAAAASAAA", [4, 7, 9]),
    "q_positive": case("SSAASAAA", [2]),
}

assert out["head"] == "08c08565c743f39350c9b959e1df7d30aa1cae5d"
assert out["short_tight_sha256"] == "bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85"
assert out["donor_offsets"] == [10, 10, 10, 11, 11, 10, 11]
assert out["donor_minimal_p2"] == [True] * 7
assert out["donor_ss_count"] == [2] * 7
assert out["fixed_offset_11_bits"] == ["A", "A", "A", "S", "S", "A", "S"]
assert out["local_older_s_owners"] == [["w1", 0, 7]]
assert out["local_newest_s_owners"] == [["AAS", 2, 3], ["w1", 0, 1], ["w2", 6, 7]]
assert [entry for entry in out["donor_w1_overlaps"] if entry["overlaps"]] == [
    {"donor": "AAASSSASASA", "oldest": 10, "overlaps": [[-9, 1, "S"]]},
    {"donor": "ASAAASSSASA", "oldest": 10, "overlaps": [[-9, 1, "S"]]},
    {"donor": "ASSAAAASSAS", "oldest": 11, "overlaps": [[-10, 1, "S"]]},
]

# False fixed offset: donor ends at phase 3, true oldest phase is 8, fixed-11 phase is 7/A.
p15 = word("AAAASAAASASASSS")
assert render(past(p15, 3, 11)) == "AAASSSASASA"
assert (3 - 10) % 15 == 8 and (3 - 11) % 15 == 7 and p15[7]

assert out["e240"]["N"] == [4, 5, 10, 17] and out["e240"]["tight"]
assert out["ss3_weakening"]["supply"][3]["window"] == "AAASSSSAAAS"
assert ss_count(past(word("AAAASAAASSSS"), 3, 11)) == 3
assert out["ss3_weakening"]["N"] == [4] and out["ss3_weakening"]["tight"]
assert not out["not_tight"]["tight"]
assert out["w_without_tightness"]["supply"][7]["window"] == "SAAAASS"
assert word("SSAAAASA")[(7 + 1) % 8] is False
assert out["w_positive"]["tight"] and out["w_positive"]["N"] == [0, 1, 6]
assert out["proper_u"]["tight"] and out["proper_u"]["supply_phases"] == [4, 7, 9, 19]
assert out["proper_u"]["N"] == [0, 1, 6]
assert out["q_positive"]["tight"] and out["q_positive"]["B"] == [2]

print(json.dumps(out, indent=2, sort_keys=True))
print("PASS: 8 finite controls; 7 donors; local placement tables")
