#!/usr/bin/env python3
"""Independent direct replay of the C++ falsifier's output certificates."""
import hashlib
import json
import math
import pathlib
import sys

def first_p2(mask, p, t):
    mass = moment = 0
    for d in range(1, p * (p + 1) + 1):
        s = 1 if mask & (1 << ((t-d) % p)) else -1
        mass += s
        moment += d*s
        if mass == 1 and moment == 0:
            return d
    return 0

def replay(mask, p, t, d):
    word = "".join("A" if mask & (1 << ((t-j) % p)) else "S"
                   for j in range(1, d+1))
    mass = sum(1 if x=="A" else -1 for x in word)
    moment = sum(j*(1 if x=="A" else -1) for j,x in enumerate(word,1))
    assert mass == 1 and moment == 0
    last = max(j for j,x in enumerate(word,1) if x=="S")
    neighbors = sum(1<<q for q in {(t-j)%p for j,x in enumerate(word,1) if x=="S"})
    return dict(phase=t, lag=d, ss=sum(word[j:j+2]=="SS" for j in range(d-1)),
                oldest=(t-last)%p, tail_A=d-last, neighbors_mask=neighbors, word=word)

def verify_record(row):
    p, mask = row["p"], row["mask"]
    assert 0 <= mask < 2**p and 2*bin(mask).count("1")-p == row["period_mass"] > 0
    members = row["donors"] + row["low"]
    assert len({w["phase"] for w in members}) == len(members)
    nb = 0
    for w in members:
        assert 0 <= w["phase"] < p and mask & (1<<w["phase"])
        assert first_p2(mask,p,w["phase"]) == w["lag"]
        assert replay(mask,p,w["phase"],w["lag"]) == w
        nb |= w["neighbors_mask"]
    v,w = row["donors"]
    assert v["ss"] == w["ss"] == 2 and v["oldest"] == w["oldest"]
    assert {v["tail_A"],w["tail_A"]} == {0,1}
    assert all(w["ss"]<=1 for w in row["low"])
    assert nb == row["neighbors_mask"]
    assert bin(nb).count("1")-len(members) == row["slack"] >= 0

def main():
    counts = []
    for filename in sys.argv[1:]:
        path = pathlib.Path(filename)
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        summaries = [row for row in rows if row["kind"]=="summary"]
        records = [row for row in rows if row["kind"]=="record"]
        for row in summaries:
            p=row["p"]
            assert row["positive_mass_words"] == sum(math.comb(p,k) for k in range(p//2+1,p+1))
            assert row["violations"] == 0 and row["max_oldest_group"] <= 2
            assert (row["collision_pairs"] > 0) == (row["min_slack"] >= 0)
        for row in records:
            verify_record(row)
        counts.append(dict(file=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                           summaries=len(summaries), exact_records_checked=len(records)))
    word="AAAASAASASASASSS"
    mask=sum(1<<q for q,x in enumerate(word) if x=="A")
    control=[replay(mask,16,3,11),replay(mask,16,12,19)]
    assert first_p2(mask,16,3)==11 and first_p2(mask,16,12)==19
    assert control[0]["oldest"]==control[1]["oldest"]==9
    assert [w["word"] for w in control]==["AAASSSASASA","SASASAASAAAASSSASAS"]
    assert control[1]["neighbors_mask"] == ((1<<16)-1)^mask
    print(json.dumps(dict(status="PASS", files=counts, E133_control=control,
                          verifier_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()),
                     indent=2))

if __name__ == "__main__":
    main()
