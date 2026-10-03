===== docs/data/issue73_20260924/slot0130/proposed_h02_card_append.md =====
# 2026-09-24 週間整理案（live card 末尾へ適用する場合）

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

===== docs/data/issue73_20260924/slot0130/proposed_h02_card_full.md =====
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

# 2026-09-24 週間整理案（live card 末尾へ適用する場合）

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

===== docs/data/issue73_20260924/slot0130/proposed_h03_card_append.md =====
# 2026-09-24 週間整理案（live card 末尾へ適用する場合）

`tight_neighborhood_eq_of_p2_prefix` のLean文は、任意の正周期 `p`、周期符号語 `e`、nodup・範囲内
current-Aの `B`、`m b <= lag b <= 11`、`P2(past e b (m b))`、lag側の緊密性から
`N_m(B)=N_lag(B)` を結論する。full-window `P2` と `m` の最小性を仮定しないため、元カードより広い。
元カードからLean文への向きは `exists_minimal_p2_prefix` で得られるが、Lean文の例を元カードのstrict例へ
逆向きに流用できない。

限定意味監査は合格したが、元カードの `m<lag`・full-lag P2・tightを同時に満たす領域は既知の
p1..12およびp15で0件で、globalな非存在も反例も証明されていない。p4 `AAAS`, `B=[2]`,
`m=3,lag=4` は広いLean文のstrict/tight例だがlag4窓はP2でない。p9 `ASAAASASS`, `B=[4]`,
`m=3,lag=7` はfull-P2 strict例だがtightでなく近傍が異なる。昼の独立入口検査も欠落するので、
総合手続きは**未完了**、状態は `CONJECTURED` のまま、strict reductionを行使済み新入力としない。
詳細は [9/24合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、その根拠となる
[9/23監査](adversarial_audits/H-20260920-03_20260923_0200.md) と
[9/24週間整理packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。

===== docs/data/issue73_20260924/slot0130/proposed_h03_card_full.md =====
# Hypothesis card: short P2 prefix reduction preserves tight neighborhoods

- ID: `H-20260920-03`
- Created: 2026-09-20 15:05 JST
- Owner: same-session four-role research pass
- Status: `CONJECTURED`

## Exact question

Let e be any integer-indexed periodic Bool stream with period p>0. Let B be
a nodup list of A phases below p. Each b is assigned a P2 window of length
d(b)<=11, with no minimality requirement. For each b choose the least positive
P2 prefix m(b). If |N_d(B)|=|B|, is N_m(B)=N_d(B)?

Intended consequence: for every integer donor clock u0 with P2(past e u0 11)
and ssCount=2, its true oldest S phase is outside N_d(B). For any such short
list B (without tightness), deleting that phase preserves |B|<=|N_d(B) minus s|.
No minimality on either side, no positive drift, no current-A donor premise,
no full supply set or period upper bound. All B members still current A.

## Existing work and smallest new edge

H-01 short_window_hall already uses P2 length<=11 without minimality.
H-02 short_tight_avoids_ss2_window accepts arbitrary donor but minimal B windows.
Repository search found take_past and the existing neighborhood membership lemma,
but no theorem asserting neighborhood equality under minimal-prefix reduction.
No stopped all-AAS route is reopened; w1 triples remain admissible.

Chain before implementation: every finite P2 window has a shortest P2 prefix;
its neighborhood is included in the original. Short Hall gives |B|<=|N_m(B)|,
and tightness gives |N_d(B)|=|B|, so the finite neighborhoods are equal. Apply H-02
to m and transport the nonmembership. In the nontight case one deletion consumes
at most the already-positive slack. The proposed new edge was strict shrinking
under the original full-P2/tight premises; its nonvacuity still needs evidence.

## Falsifier protocol and acceptance

- Discovery: all binary cycles p1..12, all period masses, all assignments of
  P2 windows with length<=11 to every sublist of A phases; multiple windows at
  one phase are alternative assignments, never duplicate B elements.
- Frozen holdout: the same exhaustive protocol at p=15 only, not H-02's p13/14.
- Compare actual set unions from strings for d and independently minimized m.
- Check equality on every tight assignment and donor avoidance for every
  length-11 P2 SS=2 window at every clock, regardless of current sign.
- Controls: record shrinking that changes a nontight neighborhood; check the
  known SS3 donor counterexample survives; no identity is accepted without a
  nonminimal assigned window appearing in the evaluated domain.
- Stop on a true counterexample to equality or avoidance. Do not restore
  minimality in the statement after seeing data. If no tight nonminimal example
  exists in range, say so rather than claiming it was exercised.
- Accept only with a symbolic proof, Lean audit, quantifier audit, and frozen
  computation. Same-session review does not replace independent promotion review.

## Historical 2026-09-20 evidence and decision

Frozen source/card hashes: `daytime/PRE_PREFIX_REDUCTION_SHA256SUMS`.
Commands: `python3 -u experiments/issue73_20260920/short_prefix_reduction.py --mode discovery`
and `--mode holdout`. Complete original JSONL files are `short_prefix_discovery.jsonl`
and `short_prefix_holdout.jsonl`. Source revision is in each output.

Discovery evaluated1141 nonminimal assignments and609 tight donor checks.
Holdout p15:32768 cycles,62545 assignments,8115 nonminimal assignments,
39340 tight assignments,4590 tight donor checks,10890 deletion checks;
no violations. Tight nonminimal assignments:0; they were not falsely counted
as exercised. Shrinking changed7995 nontight neighborhoods, so the equality
depends on tightness. SS3 counterexample preserved.

Formal proof completed: `exists_minimal_p2_prefix`,
`neighborhood_prefix_sublist`, `tight_neighborhood_eq_of_p2_prefix`,
`short_p2_tight_avoids_ss2_window`, `short_p2_ss2_deletion`.
The strongest deletion statement has no minimality on either side, no Hall
premise, no positive mass, arbitrary period and integer donor clock, but member
lags <=11 and donor length exactly11 remain. `./scripts/check.sh` passes with
2571 audited declarations; exact log `daytime/check_prefix.log`.
Independent-session review is still pending; no registry/frontier promotion.

## 2026-09-23 02:00 independent audit

The original exact claim above is unchanged: full `P2(past e b (lag b))` for
each member, and `m b` is the least positive P2 prefix. The Lean equality
signature is broader: it assumes `m b <= lag b <= 11` and `P2` at `m b`, but
does not assume `P2` at `lag b` or minimality of `m b`. The original follows
by applying `exists_minimal_p2_prefix` and then the equality theorem. The
source theorem's extra domain does not supply a strict witness for the
original card.

The Lean proof is the direct composition of short Hall for `m`, prefix
neighborhood sublist inclusion, and equality of finite lengths from
tightness. It has no H-02 dependency. Its status as a mathematically new
input for the original strict-reduction subcase remains unverified.

Original experiment replay, byte-identical to the frozen daytime JSONL:
p1..12 had 1,141 nonminimal assignments; p15 had 8,115 nonminimal and
39,340 tight assignments, with `tight_nonminimal=0`. `PASS` checks only that
nonminimal assignments, changed nontight neighborhoods, and donor checks
are positive. It does not require a tight nonminimal assignment. Thus the
tested strict full-P2/tight case remains unexercised. This does not prove
global impossibility or make the entire exact claim vacuous: period-4
`AAAS`, `B=[2]`, `m=lag=3` has current A, P2 `AAS`, and tight `N=[3]`.

A strict tight source instance at the same period and B uses `m=3`,
`lag=4`, `past4=AASA`, `N_m=N_lag=[3]`; `P2(past4)` is false, so it is
outside the original claim. A strict full-P2 nontight control is period-9
`ASAAASASS`, `B=[4]`, `m=3`, `lag=7`, with `N_m=[1]` and
`N_lag=[1,7,8]`. No exact-premise strict tight witness is asserted.

`short_p2_tight_avoids_ss2_window` uses the equality to transport the
earlier H-02 avoidance theorem; `short_p2_ss2_deletion` depends on that
transport in its tight branch. H-02's 01:30 audit found a limited semantic
pass but an overall missing preformalization gate. These downstream claims
are inventoried, not promoted or used as established results here.

Candidate packet: `data/issue73_20260923/slot0200/` contains source and
card snapshots, exact signature audit, frozen checker source, raw outputs,
commands, and manifest. This 02:00 packet does not repair the historical
missing independent preformalization entry check. The independent Sol gave
a limited semantic pass to the original-card-to-Lean implication and to the
literal equality proof, but found the exact strict full-P2/tight subdomain
unverified. The overall procedural verdict is **未完了**. This is neither a
counterexample to the equality nor a proof that strict configurations are
globally impossible. H-03 remains `CONJECTURED`, with no new E-row,
frontier, or proof-map claim. The next decision is whether the original
strict subcase has any realized tight configuration under exactly its
premises. Until then, strict reduction is not an exercised new input.

The parent audit is
`adversarial_audits/H-20260920-03_20260923_0200.md`; the daily handoff
is `RESEARCH_HANDOFF_2026-09-23_SOL.md`. The old 2026-09-20 section above
is a historical record, not this audit's verdict.

# 2026-09-24 週間整理案（live card 末尾へ適用する場合）

`tight_neighborhood_eq_of_p2_prefix` のLean文は、任意の正周期 `p`、周期符号語 `e`、nodup・範囲内
current-Aの `B`、`m b <= lag b <= 11`、`P2(past e b (m b))`、lag側の緊密性から
`N_m(B)=N_lag(B)` を結論する。full-window `P2` と `m` の最小性を仮定しないため、元カードより広い。
元カードからLean文への向きは `exists_minimal_p2_prefix` で得られるが、Lean文の例を元カードのstrict例へ
逆向きに流用できない。

限定意味監査は合格したが、元カードの `m<lag`・full-lag P2・tightを同時に満たす領域は既知の
p1..12およびp15で0件で、globalな非存在も反例も証明されていない。p4 `AAAS`, `B=[2]`,
`m=3,lag=4` は広いLean文のstrict/tight例だがlag4窓はP2でない。p9 `ASAAASASS`, `B=[4]`,
`m=3,lag=7` はfull-P2 strict例だがtightでなく近傍が異なる。昼の独立入口検査も欠落するので、
総合手続きは**未完了**、状態は `CONJECTURED` のまま、strict reductionを行使済み新入力としない。
詳細は [9/24合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、その根拠となる
[9/23監査](adversarial_audits/H-20260920-03_20260923_0200.md) と
[9/24週間整理packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。

===== docs/data/issue73_20260924/slot0130/proposed_h04_card_append.md =====
# 2026-09-24 週間整理案（live card 末尾へ適用する場合）

週間結論は、監査済みp16 literal `SAAASSSASASASAAA` による**非最小lag15 donor延長だけ**の
`REFUTED` と、その同一ルートの `STOPPED` である。`u0=15`、`B=[3]`、donor窓は
`AASASASASSSAAAS`、proper P2 prefixは3、真の最古offsetは15・phase0、`N(B)=[0]`。
従って真oldest回避と削除後Hallは失敗する。固定offset11はphase4であり、真oldestの代用ではない。

このwitnessはdonor非最小であるため、最小lag15、任意lag、一般Gate T6、実軌道を反証しない。
旧32768/85/46 census、第二w1例、pまたはlagの最小性は独立監査範囲外であり、週間の確立済み根拠に
採用しない。昼の形式化前入口検査欠落も残る。詳細は
[9/24合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、その根拠となる
[9/23監査](adversarial_audits/H-20260920-04_20260923_0100.md) と
[9/24週間整理packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。

===== docs/data/issue73_20260924/slot0130/proposed_h04_card_full.md =====
# Hypothesis card: boundary at donor length 15

- ID: `H-20260920-04`
- Created: 2026-09-20 15:10 JST
- Status: `REFUTED` (the period-16 literal certifies only the nonminimal length-15 extension)
- Owner: same-session four-role pass; limited independent review on 2026-09-23

## Exact question

Does H-03 remain true if the donor's length 11 is changed to 15, keeping
P2 and SS count 2 and still allowing a nonminimal donor window? The short
collection B, its tightness, periodicity and current-A premises are unchanged.

Acceptance is either a proof of this exact statement or an explicit periodic
countermodel with positive period mass, a current-A donor and a nonempty tight
short B that excludes donor phase u0 but covers its true oldest S. The extra
positive-mass/current-A properties are desirable properties of a
counterexample, not added theorem premises.
If a counterexample exists, do not silently replace the claim with minimal donors.

## Prior work and search

E-133 refutes joint oldest-S injectivity across some longer SS2 windows; that
does not itself refute tight-set avoidance. E-350 is length11 only. The older
2026-09-11 card predates the vacuity audit and its broad prose is not evidence.
SS2AASCollisionObstruction bounds a shared-endpoint intervening length below by
12; this points to length15 as the first possible AAS collision. The current
question is about actual oldest S and a concrete tight set, not a fixed endpoint.

## Falsification before formalization

- Discovery: enumerate all 2^15 words, test exact P2 and overlapping SS=2.
- Place AAS and the consistent w1 triple {-3:AAS,0:w1,2:AAS} on the oldest S
  in all ways consistent with the entire donor word and its current A.
- Embed a surviving placement into a periodic word with no overlapping
  inconsistent bits, verify the actual least short supplies and tightness.
- Independently verify any counterexample from its literal periodic string,
  including all proper donor prefixes, true oldest phase, N(B), deletion and
  full-U Hall at the positive-period finite bound p(p+1).
- This is a counterexample search; no arbitrary larger period census is a
  success condition and no holdout is needed to certify one literal witness.
- Stop as REFUTED if one literal witness passes independent arithmetic and
  Lean computation; stop the broad length replacement, not the length11 theorem.
- Time limit: stop discovery by15:25 and preserve a negative result if no witness.

## Evidence / decision

The length15 replacement is refuted. Period16 chronological word
`SAAASSSASASASAAA`, donor15 with word `AASASASASSSAAAS`, mass1, moment0,
SS count2. B={3} has minimal AAS, N(B)={0}; donor's true oldest S is0,
so deletion leaves N empty. Period mass2; donor current A; donor not in B.
Donor has proper P2 prefix3, so this is NOT a counterexample with a minimal donor.

Discovery: all32768 length15 words,85 P2/SS2 donors,46 minimal. One AAS overlap
and one w1-triple overlap survive, both from the same nonminimal donor word.
Frozen source/card hashes: `daytime/PRE_DONOR_LENGTH_SHA256SUMS`.
Original output: `daytime/donor_length_boundary.jsonl`.
Command: `python3 -u experiments/issue73_20260920/donor_length_boundary.py`.
These historical census figures and the w1 example were not part of the
2026-09-23 independent review.

The original same-session implementation reads literal periodic strings,
recomputes supply up to p(p+1), and checks subsets for Hall in two examples.
For period16, full U={1,3,11,15} with least lags11,3,39,3. Hall itself holds;
the donor's NONMINIMAL lag15 selection is exactly the failed assumption change.
Command: `python3 -u experiments/issue73_20260920/verify_donor_length_boundary.py`.
Original output: `daytime/donor_length_boundary_verified.jsonl`.
Only the period-16 literal and its full-U check were independently rechecked
on 2026-09-23; the second example remains outside that review.

Lean `nonminimal_donor_length15_counterexample` certifies period, positive
mass, current A, donor P2/SS2 and its proper P2 prefix, AAS member, N={0},
true oldest phase0 and empty deleted neighborhood. Original build log:
`daytime/build_length15_counterexample.log`. This was same-session verification;
the later independent review below is the separate procedural check.

Decision: STOP the nonminimal length15 extension. If proceeding with minimal
donors, use a new exact question and keep this counterexample as a control.

## 2026-09-23 limited independent audit

Procedure verdict: **PASS for the one period-16 literal and this limited stop
decision**, following an independent Sol report and parent comparison of the
reported source, commands, raw output and hashes. The review record is
`docs/adversarial_audits/H-20260920-04_20260923_0100.md`. The audited Lean
source `Recaman/ShortTightDonorAvoidance.lean` has SHA-256
`bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`;
the scoped candidate packet `docs/data/issue73_20260923/slot0100/candidate_packet.md`
has SHA-256
`d8b4f8292d7430d9ac7afd71720fcc545e25d3a835646a03d510b61d58284d11`.
Exact literal recomputation, verbatim statements, command/timeout/exit records,
raw stdout/stderr and the original 28-file manifest are in that slot directory.

The p16 witness has `B=[3]`, `N(B)=[0]`, actual oldest S phase 0, and empty
deleted neighborhood; it negates true-oldest avoidance and deletion Hall while
meeting all proposed premises. Its donor has proper P2 prefix3, so the
certificate supports `REFUTED` only for the nonminimal length-15 replacement.
The old 32768/85/46 census, second w1 example, minimum-period or minimum-lag
optimality, arbitrary-lag owner search, general Gate T6, and actual-orbit
claims were not independently reviewed here. No evidence-registry row is
added or promoted for this card.

The daytime formalization lacked an independent pre-formalization entry
check. The later adversarial review does not retroactively supply that
missing step. A minimal length-15 donor question requires its own exact
card and audit; the current witness does not decide it.

# 2026-09-24 週間整理案（live card 末尾へ適用する場合）

週間結論は、監査済みp16 literal `SAAASSSASASASAAA` による**非最小lag15 donor延長だけ**の
`REFUTED` と、その同一ルートの `STOPPED` である。`u0=15`、`B=[3]`、donor窓は
`AASASASASSSAAAS`、proper P2 prefixは3、真の最古offsetは15・phase0、`N(B)=[0]`。
従って真oldest回避と削除後Hallは失敗する。固定offset11はphase4であり、真oldestの代用ではない。

このwitnessはdonor非最小であるため、最小lag15、任意lag、一般Gate T6、実軌道を反証しない。
旧32768/85/46 census、第二w1例、pまたはlagの最小性は独立監査範囲外であり、週間の確立済み根拠に
採用しない。昼の形式化前入口検査欠落も残る。詳細は
[9/24合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、その根拠となる
[9/23監査](adversarial_audits/H-20260920-04_20260923_0100.md) と
[9/24週間整理packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。

===== docs/data/issue73_20260924/slot0130/proposed_h05_card_append.md =====
# 2026-09-24 週間整理案（live card 末尾へ適用する場合）

週間報告で限定合格と言えるのは、`moment_ending_A_budget`、`moment_ending_AA_ss2`、
`ss2_intervening_prefix` の局所3宣言だけである。最後の命題は任意の有限語 `w` について、
`X=w++[A]`、mass 0、`moment(X)+|X|<=0`、SS数2以下なら、非空suffixを残すstrictなS-ended
P2 prefixが存在すると述べる。長さ上限、周期性、OwnerFamily、実軌道は仮定しない。

独立監査はこの3宣言と紙§1-2の対応、非空例 `AASASASASSSA`、負対照
`AAASSS` / `SASASSSA` / `SA` / `AAASSSSA` を限定範囲で合格とした。しかし、後半Lean、
紙§3-5、AAS/w1各配置、true-oldest分解との結合、周期lift、任意長donor回避・削除は未監査で、
sourceにH-05全体を表す最終定理はない。昼の独立入口検査と初回補助checkerのprehashも欠落する。
従ってH-05総合手続きは**未完了**、状態は `CONJECTURED` のまま。詳細は
[9/24合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、その根拠となる
[9/23監査](adversarial_audits/H-20260920-05_20260923_0230.md) と
[9/24週間整理packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。

===== docs/data/issue73_20260924/slot0130/proposed_h05_card_full.md =====
# Hypothesis card: minimal SS2 donors and short tight motifs, arbitrary donor length

- ID: `H-20260920-05`
- Created: 2026-09-20 15:14 JST
- Status: `CONJECTURED`
- Owner: same-session research roles, no independent reviewer

## Exact question

For every integer sign stream e, a current-A clock u0, and any d with
P2(past e u0 d), no proper positive P2 prefix, and SS count2, is the oldest S
incompatible with (a) an AAS member covering it or (b) a w1 member covering it
together with the forced next two A signs?

Formally, if v=past e u0 d, s=u0-oldestOffset(v), e u0=A, and v satisfies
those three word conditions, then neither of these configurations is possible:
1. e(s+1)=e(s+2)=e(s+3)=A (an AAS member at s+3).
2. for t=s+1, s+6 or s+7, past e t 7=w1, e t=e(t+1)=e(t+2)=A.
The three shifts correspond to w1's actual S offsets1,6,7.

If established, H-01's short-owner theorem and the H-03 prefix reduction give
avoidance/deletion for arbitrary-length MINIMAL SS2 donors, while B still has
P2 windows of length<=11. It does not remove the short-B restriction or prove
all-lag Hall/capacity. H-04's nonminimal length15 counterexample remains valid.

## Prior evidence and dependencies

- E-350 covers donor length11; H-02 (`CONJECTURED`, limited semantic audit only,
  overall procedure incomplete) proposes an extension to nonminimal length11.
- E-133 refutes oldest-S joint injectivity, which is not being proposed here.
- TwoSSEndpoint.ss_one_two_no_shared_endpoint excludes endpoint sharing of
  current-A SS1/SS2 windows, but oldest S need not be the endpoint (trailing A).
- SSGapBudget gives exact A-gap budget; with SS2 there are only two extra S
  within S-runs and four A beyond the mandatory separators for a mass1 word.
- The prior lag15 certificate route was explicitly stopped for kernel cost;
  do not restart forceful certificate checking as this question's substitute.

## Falsifier and acceptance

Discovery lengths11,15,19: enumerate SS2 mass1 words by their S-runs and A gaps.
Validate the generator independently against all2^d words through19.
For each P2 word record minimality, number of trailing A, and all compatible
AAS/w1-complete-motif placements. Nonminimal length15 control must reappear.
Holdout lengths23,27,31: freeze generator before running; check all such words,
not random samples. This computation is for structural discovery, not proof.
If a minimal compatible word occurs, build and independently verify a periodic
countermodel. One actual counterexample stops the broad statement.

Success requires a length-independent argument from the gap/moment conditions,
or a concrete countermodel. Merely extending a census is not frontier progress.
If no argument by15:50, stop formalization of the broad claim and record the
precise missing local word lemma; keep the established length11 candidates.
Complete the day's validation and handoff before16:30.

## Proposed dependency chain

Finite defect budget => classify possible terminal A-run and last few gaps;
moment0 plus no earlier P2 excludes AAS/complete-w1 cover patterns => local
oldest-S avoidance => periodic short-tight avoidance via the actual OwnerFamily.
The unknown edge is the terminal-pattern exclusion, not the periodic transport.

## Evidence / decision

Discovery generator exactly matches independent binary enumeration at11,15,19.
Holdout23,27,31 contains647,1673,3605 minimal SS2/P2 words, respectively; no
compatible AAS or complete-w1 pattern. Nonminimal controls reappear at all lengths.
Raw data and source hashes: `daytime/minimal_donor_{discovery,holdout}.jsonl`
and `daytime/PRE_MINIMAL_DONOR_PATTERNS_SHA256SUMS`. This remains finite evidence.

15:21 proof-route refinement, before implementation: the gap argument suggests
a simpler induction on actual words. The new lemma to falsify is:
for every w, if x=w++[A] has mass0, moment(x)+length(x)<=0 and ssCount(x)<=2,
then x has a strict S-ended P2 prefix. Split its final letters: AA is impossible
by a moment lower bound; SA strips off a neutral pair; SSA leaves a mass1
nonpositive prefix with at most one SS, and SSSA leaves a zero-SS prefix.
Existing LowSSEndpoint prefix lemmas handle the last two cases.

New lemma falsifier: all binary words through length18 (discovery), and all
ending-A mass0 words with exactly two SS at lengths20 and24 (holdout), generated
by S-runs with two extra S and three extra A. Test the full <=0 inequality,
not only equality. Also remove last-A or the SS bound as negative controls.
No mathematical statement of H-05 has been weakened by this proof-route change.

## 2026-09-23 02:30 audit of the local word lemma

This audit is deliberately narrower than H-05. The exact Lean signature
`SS2OldestPattern.ss2_intervening_prefix` says: for arbitrary `w`, if
`X=w++[A]` has mass zero, `moment(X)+|X|<=0`, and SS count at most two, then
`X=(u++[S])++v` for a P2 prefix `u++[S]` and nonempty `v`. Since every finite
A-ended word has this form, this is equivalent in both directions to the 15:21
card lemma and paper section 2. `v != []` is precisely strictness.

The two direct inequalities also match paper section 1. For every natural q,
`moment_ending_A_budget` proves `q+1 <= moment(X)+q|X|` for an A-ended word
with SS count at most q. `moment_ending_AA_ss2` proves
`5 <= moment(X)+|X|` for an AA-ended word with SS count at most two. Their
proofs use structural induction and the earlier proved suffix mass bound. The
prefix proof is well-founded recursion on word length, excluding AA by the
second inequality, stripping terminal SA, and invoking the established
low-SS/zero-SS prefix lemmas in the SSA/SSSA cases. It neither assumes the
conclusion nor uses a defined unproved Prop, periodicity, OwnerFamily, or orbit
facts. The statements have no length cutoff.

The original frozen checker was replayed byte-identically: all binary words
through length 18 give 8 premise cases, and the generated ending-A mass-zero
exactly-SS2 length-20/24 sets give 8 and 16 cases. The literal all-word audit
through length 18 has 3 equality and 5 strict-negative cases; the smallest is
`AASASASASSSA` with P2 prefix `AAS`. It also checks the two inequalities on
434,721 and 45,976 instances. Removing ending A, mass zero, the moment bound,
or the SS bound yields respectively `AAASSS`, `SASASSSA`, `SA`, and
`AAASSSSA`, each lacking the conclusion. These are finite checks and controls,
not the proof or a new holdout.

E-130's standard-step-115 word `AAASSSASASA` still refutes the broad SS<=2
S-ended prefix normalization. It is outside the new lemma's mass-zero and
moment-plus-length premises. This local lemma must not be described as undoing
E-130 or proving a general normalization.

The target file SHA is
`a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de`.
Direct Lean, vacuity 0/13, lint 13/13, and full check (392 jobs; 2,572 axiom
declarations) pass. The modified root imports the module, but Audit and the
registry do not contain this result; the source is untracked. Build acceptance
does not register it or replace semantic review.

Candidate packet: `docs/data/issue73_20260923/slot0230/`, containing verbatim
signatures, dependency audit, frozen source/card/paper/experiment snapshots,
raw streams, commands, and a relative manifest. The independent Sol verdict is
recorded separately by the parent before any application of this proposed card.
The independent auditor reproduced the bounded counts, inequalities, boundary
split, four negative controls, and exact paper/Lean correspondence with
prehashed independent sources. After one documentation-only correction (the
future-AAS lemma is the existing E-360 OwnerFamily/W-dependent consequence,
not a new H-02 input), it accepted the bounded three-declaration mathematical
judgment. The parent audit path is
`docs/adversarial_audits/H-20260920-05_20260923_0230.md`.
The daily consolidation path is
`docs/RESEARCH_HANDOFF_2026-09-23_SOL.md`.

Writer procedure has a separate gap: the first executions of the newly created
literal checker and Lean diagnostic did not have persisted pre-run hashes.
Their initial raw outputs were preserved; the unchanged files were then hashed
and replayed once to byte-identical results in separate files. This later replay
does not retroactively supply the first-run provenance. More importantly, H-05
itself was formalized during the daytime without the now-required independent
preformalization entry review. The present audit cannot repair that historical
gap. Therefore the bounded mathematical/semantic judgment is a limited pass,
while the overall H-05 procedural judgment remains **未完了**.

H-05 remains `CONJECTURED`. Paper sections 3-5 and the source's downstream
AAS/w1 lemmas, stream decomposition, periodic transport, donor avoidance, and
deletion are unreviewed obligations. The source has no final theorem for the
whole H-05 claim. H-02 and H-03 remain `CONJECTURED` with their historical
preformalization entry gap; this audit does not repair or use them as
established inputs. No registry/frontier/proof-map/Audit promotion follows
from this bounded local audit.

# 2026-09-24 週間整理案（live card 末尾へ適用する場合）

週間報告で限定合格と言えるのは、`moment_ending_A_budget`、`moment_ending_AA_ss2`、
`ss2_intervening_prefix` の局所3宣言だけである。最後の命題は任意の有限語 `w` について、
`X=w++[A]`、mass 0、`moment(X)+|X|<=0`、SS数2以下なら、非空suffixを残すstrictなS-ended
P2 prefixが存在すると述べる。長さ上限、周期性、OwnerFamily、実軌道は仮定しない。

独立監査はこの3宣言と紙§1-2の対応、非空例 `AASASASASSSA`、負対照
`AAASSS` / `SASASSSA` / `SA` / `AAASSSSA` を限定範囲で合格とした。しかし、後半Lean、
紙§3-5、AAS/w1各配置、true-oldest分解との結合、周期lift、任意長donor回避・削除は未監査で、
sourceにH-05全体を表す最終定理はない。昼の独立入口検査と初回補助checkerのprehashも欠落する。
従ってH-05総合手続きは**未完了**、状態は `CONJECTURED` のまま。詳細は
[9/24合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、その根拠となる
[9/23監査](adversarial_audits/H-20260920-05_20260923_0230.md) と
[9/24週間整理packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。

