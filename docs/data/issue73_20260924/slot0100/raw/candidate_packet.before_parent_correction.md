# 2026-09-24 01:00 weekly audit candidate packet

## Bounded question, quantifiers, assumptions, conclusion, and gates

**Question.** As an established part of the weekly report, how far may E-360's Q/W and
`short_supply_donor_deletion` be described with respect to arbitrary period `p`, restricted lags,
assumptions, and novelty, without promoting a finite check or a restricted corollary into general
Gate T6?

**Q quantifiers and assumptions.** For every `e : Int -> Bool`, `p : Nat`, `B : List Nat`,
`lag : Nat -> Nat`, and `u0 : Nat`, assume:

1. `0 < p` and `e (x + p) = e x` for every integer `x`;
2. `B.Nodup` and `|neighborhood e p B lag| = |B|`;
3. every `b in B` satisfies `b < p`, `e b = A`, and `lag b` is exactly 3, 7, or 11;
4. every corresponding window is P2 and has no positive shorter P2 prefix;
5. the donor window `past e u0 11` is P2, has no positive shorter P2 prefix, and has
   `ssCount = 2`.

**Q conclusion.** The donor's `trueOldestPhase e p u0 11` is not in
`neighborhood e p B lag`.

**W quantifiers and assumptions.** For every integer sign word `e`, membership predicate `mem`,
owner function `own`, lag function on integer clocks, and member `t`, assume the defined structural
premise `OwnerFamily e mem own lag` and that the member's actual window is `w1`. Expanded,
`OwnerFamily` has exactly four fields: each member window is in the explicit 20-word list
`ownerWords`; each member is current A; each member owns an S in its own window; and every S in
every member window is owned by some member.

**W conclusions.** `own t = t - 7` and `e (t + 1) = true`. W has no period binder and is not an
unconditional arbitrary-period theorem. Its periodic use additionally requires the existing
E-358/E-359 construction from `p>0`, periodicity, nodup ambient `U`, Hall on `U`, `B` sublisted from
`U`, tightness, in-range current-A members, and minimal P2 lag-3/7/11 windows.

**Deletion quantifiers and assumptions.** For every positive-period periodic sign word, nodup list
`U`, arbitrary lag function, donor clock `u0`, and `B.Sublist U`, assume every member of `U` is an
in-range current-A phase with a minimal P2 window whose lag is exactly 3, 7, or 11, and assume the
donor is minimal P2 of length 11 with `ssCount = 2`.

**Deletion conclusion.** After filtering the donor's true-oldest phase from `N(B)`, the remaining
neighborhood has length at least `B.length`.

**Informal dependency chain.** Short selector locality proves Hall for every nodup short sublist;
E-358/E-359 construct the periodic owner family; E-357/E-353 plus the four owner fields give W;
E-348's donor/w1 overlap classification and E-350's AAS/true-oldest separation give Q; minimal
lag-11 P2 plus SS=2 supplies the seven-donor classification. The deletion theorem restricts the
all-`U` hypotheses to `B`, proves short Hall, splits tight versus slack, uses Q in the tight case,
and uses the existing one-deletion slack lemma in the other case.

**Acceptance test.** Accept only wording that matches each verbatim signature and definition in
both directions; distinguishes W's defined premise from Q's concrete hypotheses; exhibits the
period and lag restrictions; preserves the known nonempty, boundary, and weakening controls; calls
the deletion result a direct restricted corollary; and retains the original hashes and historical
process gaps.

**Stopping condition.** Stop this branch of the weekly audit if any wording claims arbitrary lag,
unrestricted complete supply `U`, general Gate T6, actual-orbit provenance, E-070/E-067, or
surjectivity; treats W as unconditional; treats p32/33 as newly or fully independently certified;
or suppresses the missing daytime entry audit or first-checker retention gap. No mathematical
repair, range extension, new Lean, registration, or promotion is allowed in this slot.

## Conclusion first

The safe weekly wording is:

- **Arbitrary `p`: yes, but only for periodic sign words and `p>0`.** Q and the deletion corollary
  have no upper bound on the period. This is not a theorem about arbitrary nonperiodic words or
  actual Recaman trajectories.
- **Arbitrary lag: no.** Every tight-set member in Q has a minimal P2 lag in `{3,7,11}`. Every
  ambient-`U` member in the deletion theorem has that same restriction. The donor lag is fixed at
  11. Nothing covers a tight set containing lag 15 or larger.
- **Q is concrete; W is conditional.** Q has no ambient `U`, assumed Hall, positive drift, or
  unproved defined-`Prop` premise. W assumes the four-field `OwnerFamily`; the existing periodic
  construction is a necessary dependency and may not be omitted when W is used for periodic sets.
- **Novelty is limited.** E-360's registered mathematical contribution is the conditional local W
  endpoints and the restricted periodic Q. `ownerFamily_of_minimal` and `tight_owner_family` are
  extracted existing E-357/E-359 dependencies. `short_supply_donor_deletion` is a meaningful,
  nonvacuous, already Lean-checked direct consequence of Q, short Hall, and generic deletion
  lemmas; it is not a new mathematical input and has no separate E-row.

The principal evidence is the frozen Lean source and exact E-360 statement audit, not the finite
experiments. Q is registered `PROVED-LEAN`; the deletion card is `PROVED-LEAN` only for its exact
restricted corollary. No claim about general T6, full all-lag supply, actual orbit, or surjectivity
is established.

## Exact scope and assumption ledger

| Item | Period scope | Lag scope | Ambient/full-supply assumptions | Status and novelty |
|---|---|---|---|---|
| `w1_owns_oldest` | none in signature | implicit explicit `ownerWords` through `OwnerFamily` | assumes `window/addA/own_mem/onto`; periodic construction is external | E-360 endpoint; conditional local input |
| `w1_next_addition` | none in signature | same | same | E-360 endpoint; short consequence of the substantive future-AAS chain |
| `short_tight_avoids_ss2_donor` | every `p>0`, periodic `e`; no upper bound | B minimal P2 lag 3/7/11; donor minimal lag 11, SS=2 | no ambient U, assumed Hall, positive drift, donor membership, or actual orbit | E-360 `PROVED-LEAN`; restricted Q |
| `short_supply_donor_deletion` | every `p>0`, periodic `e`; no upper bound | every U member minimal P2 lag 3/7/11; donor minimal lag 11, SS=2 | arbitrary nodup short-only U; no completeness, positive drift, donor membership, or orbit | exact restricted `PROVED-LEAN` corollary; no new E-row/input |

`short_supply_donor_deletion` does not assume `u0 in U`. It also does not assume that `U` is
complete. If a complete supply list is supplied, the theorem applies only when that entire list
already satisfies the all-short lag-3/7/11 hypotheses; it cannot discard longer members.

## Evidence and adversarial controls

- Frozen source: `Recaman/ShortTightDonorAvoidance.lean`, SHA-256
  `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
- Registry: E-360, `PROVED-LEAN`, exact three registered symbols. Official G5 is
  `docs/statement_audits/E-360.md`.
- The official G5 header's `application pending` is a timestamped pre-application sentence retained
  as history. Actual application and post-application PASS are established by the final sections of
  `docs/adversarial_audits/H-20260920-01_20260921_0200.md`; this audit does not rewrite the old G5.
- Registration audit: `docs/adversarial_audits/H-20260920-01_20260921_0200.md`, PASS for the exact
  three-symbol E-360 bundle.
- Deletion audit: `docs/adversarial_audits/H-20260921-01_20260921_0230.md`, PASS for the exact
  restricted corollary and explicit finding of no new mathematical input.
- Nonempty/actual-removal controls: p8 `SSAASAAA` and p11 `AAAASASASSS`. Empty `B` is a boundary,
  not the only realization.
- Weakening control: dropping donor `ssCount=2` fails at p12 `AAAASAAASSSS`,
  `B=[2,5,7]`, true-oldest phase 4; deletion leaves only two neighbors for three members.
- E-240 permits a non-AAS tight set and blocks the pure-AAS story while remaining compatible with
  Q. E-069/E-133 refute general named oldest-S injections, not Q's local noncoverage statement.
- The false fixed offset-11 interpretation is rejected: four of the seven minimal lag-11 SS2 donor
  words have true oldest offset 10. A false offset may delete an A or perform a no-op, so a passing
  Hall inequality does not validate its meaning.
- Phase equality is modulo `p`; the periodic lift is explicit. Repeated clocks at small `p` may
  represent the same phase and cannot be counted as distinct by informal line pictures.

## Evidence limits and historical debt

The p32/33, seed `2026091801`, 2000-word-per-period data were used during the week. They remain
finite evidence and the full independent certification is incomplete; this slot neither reruns nor
relabels them as a holdout. The daytime formalization lacked the required independent pre-entry
audit, and the 2026-09-21 01:00 independent checker's first erroneous source/raw pair was not
retained. Later semantic audits supported the exact statements but do not erase these historical
gaps.

H-02/H-03/H-05 are only locally/partially audited and remain overall incomplete `CONJECTURED`
work. H-04's nonminimal lag-15 counterexample does not extend to the minimal lag-11 Q. None of
those later candidates is used as established support here.

## Status and next decision

- Hypothesis-card status: H-20260917-01 `PROVED-LEAN` for the exact registered Q/W scope;
  H-20260921-01 `PROVED-LEAN` for the exact restricted deletion corollary, with no new registry row.
- Strongest evidence: exact source signatures/proofs, E-360 G5, Audit inclusion, and the two
  independent semantic audits.
- Failed/stopped interpretations: pure-AAS forcing, a general oldest-S injection, fixed offset 11,
  unrestricted all-lag deletion, and promoting the direct deletion composition to new mathematics.
- Remaining uncertainty: lag 15 and larger members, arbitrary-lag donor avoidance/deletion,
  unrestricted complete-U capacity, general Gate T6, actual-orbit transfer, E-070/E-067, and
  surjectivity.
- Next decision: do not extend this week. Preserve E-360 and the restricted deletion corollary as
  established local results, and carry the general-lag bridge as an open obligation for a future
  independently scoped plan.
