# Entry/barrier parallel unit reproducibility

Source revision: `612fcfaf74bfb49f3ae05a268057c82f70dcca26`.
All programs use exact Python integers and the actual Recaman strict-positive/unseen step.
The 1M canonical interval is existing repository territory, not a new holdout. Universal
claims are supported by the paper arguments in H-20260907-04/05, not by finite output.

Run from repository root:

```sh
python3 experiments/parallel20260907/entry_probe.py --limit 1000000 > docs/data/parallel20260907/entry_probe.txt
python3 experiments/parallel20260907/entry_canonical_swap.py > docs/data/parallel20260907/entry_canonical_swap.txt
python3 experiments/parallel20260907/entry_source_birth.py > docs/data/parallel20260907/entry_source_birth.txt
```

Each output embeds its command, source revision and script SHA-256. The canonical swap
was discovered after the primary test and then frozen as a fixed exact witness; it is
not independent evidence for a universal extrapolation. The source-birth inequality was
stated in the card before the second pass and is refuted at the first displayed witness.
No Lean files, shared maps, GitHub issues, commits, or user files were modified by this worker.
