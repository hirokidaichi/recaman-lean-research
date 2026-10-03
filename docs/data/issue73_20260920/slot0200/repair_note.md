# Initial run rejected before evidence use

- Source SHA256: `ead649739e53ca1d52853cac01f11a47f957b1ee1320469849971a5560cdbac5`
- Command: `python3 -u experiments/issue73_20260920/w_partial_u_probe.py --max-period 11 --max-work 2000000 --seconds 240`
- Exit: `0`
- Wall time reported by the runner: `5.738032` seconds.
- Program elapsed time: `5.576564` seconds.
- Result: rejected. The variable named `w1_antecedents` counted only antecedents whose next bit
  was already `S`, rather than all w1 antecedents. Consequently it reported zero despite the known
  full-U regression having 32 antecedent occurrences. It also enumerated proper U only after that
  incorrectly filtered set was nonempty.
- Permitted repair: separate the W antecedent from `next=S`, enumerate Hall-valid proper U for every
  antecedent, count those targets, and test the conclusion only afterward. No quantifier, period range,
  lag bound, or acceptance condition changes.
