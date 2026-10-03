#!/usr/bin/env python3
"""Compare the frozen verbatim statements to source and existing E-360 G5."""
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
source = (ROOT / "Recaman/ShortTightDonorAvoidance.lean").read_text().splitlines()
quoted = (Path(__file__).resolve().parent / "statement_signatures.txt").read_text()
q = "\n".join(source[332:345]) + "\n"
literal = "\n".join(source[650:661]) + "\n"
assert quoted == q + literal
audit = (ROOT / "docs/statement_audits/E-360.md").read_text()
section = audit.split("## Recaman.ShortTightDonorAvoidance.short_tight_avoids_ss2_donor", 1)[1]
official_q = section.split("```lean\n", 1)[1].split("```", 1)[0]
assert official_q == q
print("source signatures: exact (Q 13 lines; literal 11 lines)")
print("existing E-360 G5 Q: exact")
print("new registration G5: not applicable; no row proposed")
