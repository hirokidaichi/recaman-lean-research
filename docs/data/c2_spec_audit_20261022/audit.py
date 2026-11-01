#!/usr/bin/env python3
"""Re-evaluate only the three fixtures frozen in PROTOCOL.md; no search."""
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time
from datetime import datetime, timezone

resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
started = time.monotonic()
root = Path(__file__).resolve().parents[3]
output = Path(__file__).resolve().parent
fixtures = ("SAAA", "SSAAAASA|AA", "SSSAAAASAAA|SSSSAAAA")


def evaluate(encoded):
    q0 = encoded.index("|") if "|" in encoded else 1
    word = encoded.replace("|", "")
    signs = [1 if c == "A" else -1 for c in word]
    n = len(signs)
    F, G = [0], [0]
    for sign in signs:
        F.append(F[-1] + sign)
        G.append(G[-1] + F[-1])
    windows = {}
    for b in range(n):
        direct = []
        for t in range(b):
            mass = sum(signs[t:b])
            moment = sum(signs[c] * (b - c) for c in range(t, b))
            by_definition = mass == 1 and moment == 0
            by_area = (F[b] == F[t] + 1
                       and G[b] - G[t] == (b - t) * F[t])
            assert by_definition == by_area, (word, t, b)
            if by_definition:
                direct.append(t)
        skipped = [t for t in range(b - 3, -1, -4)
                   if F[b] == F[t] + 1
                   and G[b] - G[t] == (b - t) * F[t]]
        assert direct == sorted(skipped), (word, b, direct, skipped)
        windows[b] = direct
    endable = [signs[b] == 1 and bool(windows[b]) for b in range(n)]
    d, a = [0], [0]
    for b in range(n):
        d.append(d[-1] + (signs[b] == -1) - endable[b])
        a.append(a[-1] + (signs[b] == 1 and not endable[b]))
    zeros = [u for u in range(q0) if d[u] == 0]
    k1 = max(zeros) if zeros else None
    mid_events = []
    for b in range(q0, n):
        mid = [t for t in windows[b] if k1 is not None and k1 < t < q0]
        if not endable[b] or not mid:
            continue
        assumptions = {
            "prefix_nonnegative": min(d[:q0 + 1]) >= 0,
            "d_q0_eq_1": d[q0] == 1,
            "positive_through_b_plus_1": min(d[q0:b + 2]) >= 1,
            "a_y_le_1": a[b + 1] - a[q0] <= 1,
            "endable_A": endable[b],
        }
        mid_events.append({
            "b": b, "starts": mid, "lengths": [b - t for t in mid],
            "words": [word[t:b] for t in mid],
            "local_starts": [t for t in windows[b] if t >= q0],
            "d_b_plus_1": d[b + 1], "a_y": a[b + 1] - a[q0],
            "v1_assumptions": assumptions,
            "v1_domain": all(assumptions.values()),
            "ay2_domain": all(value for key, value in assumptions.items()
                              if key != "a_y_le_1")
                          and a[b + 1] - a[q0] <= 2,
        })
    return {"encoded": encoded, "word": word, "q0": q0, "k1": k1,
            "F": F, "G": G, "d": d, "a_p_prefix": a,
            "endable_clocks": [b for b in range(n) if endable[b]],
            "mid_events": mid_events}


results = [evaluate(fixture) for fixture in fixtures]
long_control = next(event for event in results[2]["mid_events"]
                    if event["b"] == 18 and 11 in event["lengths"])
assert results[2]["q0"] == 11 and results[2]["k1"] == 0
assert long_control["ay2_domain"] and not long_control["v1_domain"]
assert long_control["a_y"] == 2
assert [key for key, value in long_control["v1_assumptions"].items()
        if not value] == ["a_y_le_1"]
terminal_control = next(event for event in results[1]["mid_events"]
                        if event["b"] == 9)
assert terminal_control["lengths"] == [3]
assert terminal_control["d_b_plus_1"] == 0
assert not terminal_control["v1_domain"]
paths = ("Recaman/LeadingRunSupply.lean", "Recaman/LineCapacityPeriodic.lean",
         "experiments/issue73_20261020/c2proof/c2.c",
         "experiments/issue73_20261020/c2proof/c3.c",
         "docs/HYPOTHESIS_CARD_2026-10-21_C2_WINDOW_POSITION.md",
         "docs/RESEARCH_ALLOCATION_2026-10-21.md",
         "docs/data/c2_spec_audit_20261022/PROTOCOL.md",
         "docs/data/c2_spec_audit_20261022/audit.py")
sources = {path: hashlib.sha256((root / path).read_bytes()).hexdigest()
           for path in paths}
revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root,
                          check=True, capture_output=True, text=True).stdout.strip()
dirty = subprocess.run(["git", "diff", "--binary", "HEAD"], cwd=root,
                       check=True, capture_output=True, text=True).stdout
(output / "working-tree.patch").write_text(dirty)
status = subprocess.run(["git", "status", "--short"], cwd=root,
                        check=True, capture_output=True, text=True).stdout
(output / "git-status.txt").write_text(status)
report = {
    "label": "COMPUTED", "scope": "three previously known fixtures only",
    "command": "python3 docs/data/c2_spec_audit_20261022/audit.py",
    "revision": revision, "dirty": True,
    "timestamp_utc": datetime.now(timezone.utc).isoformat(),
    "source_sha256_at_execution": sources,
    "results": results,
    "checks": {"direct_equals_area_and_stride": True,
               "known_ay2_counterexample_reproduced": True,
               "known_terminal_slack_zero_reproduced": True},
    "elapsed_seconds": time.monotonic() - started,
}
assert report["elapsed_seconds"] < 10
rendered = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
(output / "result.json").write_text(rendered)
print(rendered, end="")
