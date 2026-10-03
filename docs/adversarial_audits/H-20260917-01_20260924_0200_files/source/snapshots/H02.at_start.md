# Hypothesis card: lag-11 SS=2 donor without minimality

- ID: `H-20260920-02`
- Owner: daytime research, same-session proposer / falsifier / formalizer / auditor
- Created: 2026-09-20 15:02 JST
- Status: `CONJECTURED` (limited semantic audit passed; overall research procedure incomplete)
- Research branch: working-tree continuation of H-20260920-01; no registry promotion

## Exact statement

For every `e : Int → Bool`, period `p > 0` with `e (x+p)=e x`, nodup list
`B : List Nat` of phases `< p` with `e b = A`, and lag function assigning each
member a minimal P2 window of length 3, 7 or 11, suppose `|N(B)|=|B|`.
For every integer donor clock `u0`, if `past e u0 11` has mass 1, moment 0,
and overlapping SS count 2, its oldest S phase is not in `N(B)`.
Donor minimality, donor current sign, donor exclusion from B, positive period
mass, ambient Hall and an upper bound on p are NOT premises of this question.
The short-member minimality restriction remains explicit.

Existing supporting lemma in the current source: for any `OwnerFamily e mem own lag`, if member t has
window w1=SAAAASS, then `mem (t+2)`, `lag (t+2)=3`, its window is AAS,
and `own (t+2)=t-1`. This strengthens H-01's next A to an actual future member.

## Why it would matter

It removes a donor-side assumption from short tight-set avoidance. This is
still restricted to length-11 donors and member lags at most 11. It does not
settle all-lag Hall, general Gate T6 or the Recamán orbit question.

## Provenance and dependencies

- E-357 excludes lag-11 and w2 members of OwnerFamily; E-359 supplies the
  periodic tight-set lift.
- H-01 candidate proves w1 owns t-7 and forces next sign A, and derives Hall
  from the existing short injection with its local image bound.
- Discovery already used: H-01 negative controls p=1..12 found no violation
  after dropping donor minimality. It is NOT fresh holdout evidence here.
- No unproved mathematical hypothesis beyond the displayed object premises.
- Portfolio and E-350, E-351, E-353, E-356..359 checked: pure-AAS classification
  was refuted; non-AAS tight triples are retained, not ruled out. E-351 needs
  next A and ambient inclusion; the proposed line theorem needs neither.

## Falsification plan

- Enumerate all 2^11 words independently by mass/moment/SS count. Check all
  compatible AAS/w1/w2 cover placements at the actual oldest S.
- Check all permitted coverers against the forced future AAS member; keep
  w2 in the raw overlap table and remove it only using E-357.
- Translation/boundary: donor clocks -101,-1,0,1,101; periods 1..12 include
  wrapping and repeated phases. Test zero and negative period mass.
- Weakened-history controls: remove onto or single-valued ownership; confirm
  the forced future-member conclusion can then fail.
- Frozen holdout: all binary cycles of periods 13 and 14, all mass signs,
  all nonempty tight subsets of their least P2 supplies of length <=11;
  donors are ALL lag-11 P2 SS=2 windows, including nonminimal donors.
  Use short windows only; do not use a full-supply bound at nonpositive mass.
  Do not use old p32/33 samples as fresh holdout.
- Acceptance: exact local table has no surviving AAS/w1 ownership completion,
  nonminimal donor instances and nonempty B are actually exercised; Lean
  statement matches the displayed quantifiers; full repository audit passes.
- Stop: one genuine counterexample refutes the broad claim. At most one
  implementation correction is allowed if independently diagnosed; do not
  repair the mathematical claim by reintroducing donor minimality silently.
- Wall-clock boundary: stop new exploration early enough to hand off at16:30.

## Informal dependency chain (before implementation)

Tightness + short injection => periodic OwnerFamily. E-357 => members AAS/w1.
w1 must own its paired oldest S t-7. Its newest S t-1 has an owner; AAS gives
t+2, while w1 at t cannot own two S and other w1 placements conflict in bits.
Thus the owner is the AAS member t+2. Of the 12 length-11 P2 SS=2 words,
7 are old minimal donors and 5 are nonminimal. New compatible w1 covers in
two nonminimal words force e(t+2)=A where the donor has S. Verify this finite
classification before Lean implementation; it is currently a conjecture.

## Evidence log

`COMPUTED`: source and card frozen in `daytime/PRE_DONOR_MINIMALITY_SHA256SUMS`.
Commands: `python3 -u experiments/issue73_20260920/donor_without_minimality.py --mode local`
and `--mode holdout`. Original outputs saved as `daytime/donor_without_minimality_*.jsonl`.
HEAD is `08c08565c743f39350c9b959e1df7d30aa1cae5d`; script hash disambiguates uncommitted code.
All 12 words enumerated, 5 nonminimal. No AAS cover, 5 w1 placements, 2 w2 placements;
w2 is excluded only by E-357. All w1 placements conflict with the future AAS member.
p13: 8192 cycles, 221 nonminimal-donor/nonempty-tight-B checks, 143 nonpositive checks.
p14: 16384 cycles, 532 nonminimal checks, 658 nonpositive checks. No violations.
Actual nonminimal example: p13 `AASSSAAAASSSS`, donor10 with window `SAAAASSSAAS`,
donor sign S, B={7}, N(B)={4}; this exercises the lack of donor-current-A too.

Implementation correction (one allowed): first Lean finite table reused the old
two-bit `aasClash`; Lean's `decide` rejected it. For the two newly compatible w1
words, the two AAS past bits can both be A, while the putative AAS member itself
would have sign S. The Python table already included current-member A. Fix the
Lean table to check all three required A signs. Main theorem quantifiers unchanged.
Failed source and exact failure log are archived as `ShortTightDonorAvoidance_nonminimal_v1.lean`
and `build_nonminimal_local.log`. This is not a counterexample to the card statement.
The creation timestamp above was entered as 15:02 before a fresh clock check;
actual calls confirm this unit was underway by 14:59 and the failure was at15:01.

## Semantic audit

- Abstract periodic signs, not real-orbit provenance.
- Not vacuous: H-01 supplies explicit nonempty tight sets; this cycle must
  separately exhibit nonminimal donors with nonempty tight B.
- Quantifier audit must distinguish donor minimality (removed) from member
  minimality (retained) and true oldest offset from the fixed offset 11.
- No positivity or full-U premise may slip into the implementation.

## Daytime decision (historical, same-session)

The exact statement is implemented as `short_tight_avoids_ss2_window`, including
integer donor clock and no donor-current-A. `w1_future_aas_member` gives the
actual future member and its ownership. `./scripts/check.sh` passed with 2566
audited declarations, allowed axioms only; module lint 14/15 substantive,
vacuity scan 0/15 flagged. Original output: `daytime/check_nonminimal.log`.
Thus the Lean candidate and computational protocol are complete. Card remains
CONJECTURED for promotion bookkeeping until the required independent-session
semantic audit; do not read this as an independent review having occurred.

Same-session shortcut audit: the existing fixed shortOff assignment does NOT
already avoid donor oldest S. Three compatible lag-11 charge collisions exist
in `daytime/short_charge_donor_exploratory.jsonl` (OBSERVED, exploratory script
was an inline command). This rules out that particular shortcut, not all possible
fixed injections. The tight-owner-family reasoning is not merely a direct use
of the old injection's image property.

## 2026-09-23 01:30 scope and audit outcome

The proposed new certification is only the removal of donor minimality from the
lag-11 SS=2 statement. `w1_future_aas_member` is an existing dependency in the
current source, not a newly discovered lemma in this slot. The historical
daytime same-session workflow lacked a separate preformalization entrance
check; this later review does not retroactively supply one.

The frozen candidate is `short_tight_avoids_ss2_window` at source SHA
`bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
It has arbitrary positive period, all integer donor clocks, no donor-current-A,
no donor minimality, no positive period mass, no full-U premise, and member
minimality at lag 3/7/11. The p13 nonminimal example has proper P2 prefix 7;
its true oldest offset is 11 and true oldest phase is 12, while `N([7])=[4]`.
Earlier prefix-3/phase-0 expectations were errors in the 01:30 regression
checker, not in the original card or in the mathematical statement. Original
stderr is retained, but the source from each failed original run was not
captured before execution; the `recheck_v1.py` and `recheck_v2.py` sources in
`slot0130/` were reconstructed afterward and rerun. This is a provenance
limitation for those failed runs. The final checker has a pre-run SHA and raw
stdout/stderr in the packet.

The separate Sol's review found the source/statement match and the local
counterexample attacks sufficient for a **limited semantic pass** on this
exact version. The overall research procedure remains **incomplete** because
the required independent entrance check was missing before the daytime Lean
formalization began. A later semantic audit cannot retroactively perform that
preformalization gate. Keep this card `CONJECTURED`; do not register the H-02
claim as `PROVED-LEAN` or use it as an established downstream dependency.
The claim says nothing about arbitrary donor lengths (whether minimal or not),
lag 15, general Gate T6,
all-lag Hall/capacity, full U, actual Recaman orbits, or surjectivity.

The parent audit record is [H-20260920-02_20260923_0130.md](/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/adversarial_audits/H-20260920-02_20260923_0130.md);
the dated handoff is [RESEARCH_HANDOFF_2026-09-23_SOL.md](/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/RESEARCH_HANDOFF_2026-09-23_SOL.md).

The p13/p14 range called a frozen holdout in the original daytime plan is
historical consumed data in this slot. Rerunning it only checks reproducibility.
The current `./scripts/check.sh` result is 392 jobs and 2572 allowed-axiom
declarations; `report_vacuity --all` flags 0/21 and module lint marks 20/21
substantive. These are syntax and build checks, not the independent semantic
decision. No `PROVED-LEAN` status is proposed by this card version. The next
decision is to preserve this candidate as limited evidence and revisit the
research procedure only under a separately authorized future plan, without
altering the 2026-09-20 chronology or weakening the target statement.

## 2026-09-24 週間記載の監査

週間報告で採用できるのは、2026-09-23監査が確認した**限定意味監査合格**までである。
`short_tight_avoids_ss2_window` は、任意の正周期 `p` と周期符号語 `e`、nodup・範囲内
current-Aの緊密 `B`、各メンバーが最小P2かつ lag 3/7/11、任意の整数donor時計 `u0`、
長さ11のP2・SS=2 donorを量化し、donor最小性・donor current-A・ambient Hall・正driftを
仮定せず真の最古S位相を `N(B)` から除く。一般lag、lag 15以上、完全all-lag U、実軌道は扱わない。

独立監査はこのstatementと定義・証明・既知例を限定範囲で合格としたが、昼の形式化前の独立入口検査は
欠落しており、後日の監査で遡及的に埋められない。最終checker以前の二つの失敗runにも実行時source/hashの
保存欠落がある。したがって総合手続きは**未完了**、状態は `CONJECTURED` のまま、新規登録・昇格・
後続の確立済み根拠への採用はしない。p13 `AASSSAAAASSSS`, `u0=10`, `B=[7]` は
nonminimal/current-S donorと非空tight Bの共存例であり、反例ではない。詳細は
[9/24合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、その根拠となる
[9/23監査](adversarial_audits/H-20260920-02_20260923_0130.md) と
[9/24週間整理packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。
