# Statement audit: E-360

- artifact: `Recaman/ShortTightDonorAvoidance.lean`
- source boundary: lines 1--358, SHA-256
  `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- registration status: isolated official-form draft; do not place under
  `docs/statement_audits/` before independent approval
- proposed audit symbols:
  `Recaman.ShortTightDonorAvoidance.w1_next_addition` and
  `Recaman.ShortTightDonorAvoidance.short_tight_avoids_ss2_donor`
- reviewer: pending independent registration audit on 2026-09-21

## Summary of the three checks

1. **yes** -- both cited statements quantify the actual sign word `e` and actual `past` windows.
   Q also quantifies the positive period `p`, periodicity, the phase list `B`, its lag function,
   tight neighborhood, and the donor window.
2. **W: yes, Q: no** -- W assumes the defined structural proposition `OwnerFamily`; the claim text
   names it and its four fields (`window`, `addA`, `own_mem`, `onto`). The periodic realization is
   constructed from concrete Hall/tightness hypotheses by the existing `tight_owner_family`.
   Q has no unproved defined-Prop hypothesis and does not assume its conclusion.
3. **no for both cited theorems** -- W obtains a forced future AAS owner and reads the next sign;
   Q proves Hall on every short sublist, classifies the donor, and applies the concrete phase and
   A/S contradiction. Neither cited proof is an `intro`/`exact`/`refine`/`rcases`-only wrapper or
   bare `omega`/`rfl` proof. The transported `tight_w1_next_addition` is intentionally not cited.

The row therefore registers one conditional local statement W and one concrete periodic statement
Q. It does not describe W as unconditional, and it does not describe Q as general Gate T6.

## Recaman.ShortTightDonorAvoidance.w1_next_addition

```lean
theorem w1_next_addition (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : e (t + 1) = true := by
```

1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: **yes**
   (`e`, `past e t (lag t)`, and the member/owner/lag data).
2. some hypothesis is an unproved defined `Prop` or is equivalent to the conclusion: **yes** for
   the defined structural premise `OwnerFamily`; **no** for a conclusion-equivalent premise.
   Expanded, `OwnerFamily` says exactly:

   ```lean
   structure OwnerFamily (e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat) :
       Prop where
     window : ∀ b, mem b → past e b (lag b) ∈ ownerWords
     addA : ∀ b, mem b → e b = true
     own_mem : ∀ b, mem b → ∃ k ∈ sOffsets (past e b (lag b)), own b = b - (k : Int)
     onto : ∀ b, mem b → ∀ k ∈ sOffsets (past e b (lag b)), ∃ b', mem b' ∧ own b' = b - (k : Int)
   ```

   None of these fields is `e (t + 1) = true`, future-A, oldest ownership, donor avoidance, or Q.
   Accordingly the registry claim calls W conditional. In the periodic application the existing
   `tight_owner_family` constructs this exact structure; it is not silently assumed there.
3. the proof is a wrapper/omega/rfl over imported results: **no**. It consumes the substantive
   `w1_future_aas_member` conclusion and reads offset 0 of the forced AAS window. This is a short
   corollary, but the harness classifies it substantive and the future sign is not a structure field.

Exact meaning: in any `OwnerFamily e mem own lag`, if `t` is a member with w1 window, its next
absolute sign is A. This alone is not an arbitrary-period or actual-orbit theorem.

## Recaman.ShortTightDonorAvoidance.short_tight_avoids_ss2_donor

```lean
theorem short_tight_avoids_ss2_donor (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat) (hBn : B.Nodup)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p)
    (hB_A : ∀ b ∈ B, e (b : Int) = true)
    (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hB_min : ∀ b ∈ B, ∀ d, d < lag b → 0 < d → ¬ P2 ((past e (b : Int) (lag b)).take d))
    (u0 : Nat) (hPdon : P2 (past e (u0 : Int) 11))
    (hmindon : ∀ d, d < 11 → 0 < d → ¬ P2 ((past e (u0 : Int) 11).take d))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e (u0 : Int) 11) = 2) :
    Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11 ∉ neighborhood e p B lag := by
```

1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: **yes**.
   They explicitly mention the periodic sign word, positive period, phase list `B`, neighborhood,
   every B window, and the donor window.
2. some hypothesis is an unproved defined `Prop` or is equivalent to the conclusion: **no**.
   `P2 w` is the concrete conjunction `mass w = 1 ∧ moment w = 0`; the other hypotheses are
   concrete list, sign, periodicity, minimality, tightness, and SS-count conditions. No hypothesis
   asserts true-oldest nonmembership, a named donor-avoidance property, or general capacity.
3. the proof is a wrapper/omega/rfl over imported results: **no**. It proves lag at most 11 for B,
   constructs Hall for every sublist from `short_window_hall`, derives membership in the explicit
   seven-donor list from minimal P2 plus SS=2, and applies the substantive true-oldest avoidance
   kernel. The kernel performs the periodic phase lift and the AAS/w1 contradiction.

Exact meaning: for every positive period, if B is nodup and tight, all its phases are in range and
current A, and all its windows are minimal P2 with lag 3, 7, or 11, then the true oldest S phase of
a minimal lag-11 SS=2 donor lies outside B's neighborhood. There is no period upper bound. The
theorem does not require ambient U, assumed Hall, or positive drift because Hall on each short
sublist is proved inside the dependency chain.

It does **not** prove deletion survival for an unrestricted supply list, arbitrary-lag donor
avoidance, general Gate T6, E-070/E-067, generation by the Recaman orbit, or surjectivity.

## Frozen dependency supplement

The official G5 gate requires verbatim signatures for the two cited symbols above. The complete
semantic dependency audit additionally covers the full frozen core and existing constructors:

1. `shortOff_le_window`
2. `short_window_hall`
3. `member_window_aas_or_w1`
4. `w1_owns_oldest`
5. `w1_future_aas_member`
6. `w1_next_addition`
7. `tight_w1_next_addition`
8. `donor_cover_next_subtraction`
9. `short_tight_avoids_trueOldest`
10. `short_tight_avoids_ss2_donor`
11. `ownerFamily_of_minimal`
12. `tight_owner_family`

Their punctuation-preserving source signatures are in
[`slot0130/core_signatures_verbatim.txt`](../slot0130/core_signatures_verbatim.txt), and their
binder, defined-Prop, wrapper, bidirectional-meaning, realizability, and negative-control audit is
in [`slot0130/statement_audit_pre_registration.md`](../slot0130/statement_audit_pre_registration.md).
The source hashes in those files equal this audit's frozen boundary. The two constructors are
existing E-357/E-359 extracted proof structure and are dependencies, not E-360 novelty.

Known controls retained by the audit include p8 Q, p10 W, p20 proper-U, E-240 non-pure-AAS,
the false-offset p15 example, SS3 p12, non-tight p11, W-without-tightness p8, and the local
`mem={-3,0,2}` / `own={-6,-7,-1}` family. These are finite or weakened-model controls, not new
theorems or holdout evidence for this row.

## Historical and procedural limits

The daytime formalization lacked an independent pre-formalization entry check, and the 01:00
independent checker's first erroneous source/raw pair was not retained. The later audits do not
rewrite that history. These are disclosed process debts, not a new permanent human-approval rule.
Registration still requires the separately owned audit of this exact draft and an isolated-copy
successful G1-G5 check before live application.
