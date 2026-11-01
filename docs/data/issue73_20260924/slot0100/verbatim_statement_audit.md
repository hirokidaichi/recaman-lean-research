# Verbatim statement audit: weekly E-360 and deletion scope

- Frozen target source: `Recaman/ShortTightDonorAvoidance.lean`
- SHA-256: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- Audit purpose: weekly wording only; no registration or promotion

The official E-360 G5 file was authored before live application and retains `application pending`
in its header. That sentence is historical. The live application and post-application PASS are
recorded in the final sections of `docs/adversarial_audits/H-20260920-01_20260921_0200.md`.
This weekly audit preserves both records instead of rewriting the earlier artifact.

## `w1_owns_oldest`

```lean
theorem w1_owns_oldest (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : own t = t - 7 := by
```

- Actual object binders: yes (`e`, actual `past` window, member/owner/lag data).
- Unproved defined `Prop`: yes, exactly `OwnerFamily`; no conclusion-equivalent hypothesis.
- Expanded premise: `window`, `addA`, `own_mem`, `onto`; none says `own t = t-7`.
- Wrapper: no. The proof uses paired-S coverage, exclusion of AAS owners, classification of a w1
  owner, and ownership equality.
- Safe prose: conditional local theorem; no period or orbit conclusion by itself.

## `w1_next_addition`

```lean
theorem w1_next_addition (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : e (t + 1) = true := by
```

- Actual object binders: yes.
- Unproved defined `Prop`: yes, exactly `OwnerFamily`; no conclusion-equivalent hypothesis.
- Wrapper: no for the registered endpoint. It consumes `w1_future_aas_member`, whose proof depends
  on `w1_owns_oldest` and all owner fields, then reads the actual future AAS window.
- Safe prose: a w1 member's next absolute sign is A in an `OwnerFamily`. A periodic conclusion
  requires the separately constructed periodic family.

## Exact `OwnerFamily` expansion

```lean
structure OwnerFamily (e : Int → Bool) (mem : Int → Prop) (own : Int → Int) (lag : Int → Nat) :
    Prop where
  window : ∀ b, mem b → past e b (lag b) ∈ ownerWords
  addA : ∀ b, mem b → e b = true
  own_mem : ∀ b, mem b → ∃ k ∈ sOffsets (past e b (lag b)), own b = b - (k : Int)
  onto : ∀ b, mem b → ∀ k ∈ sOffsets (past e b (lag b)), ∃ b', mem b' ∧ own b' = b - (k : Int)
```

The structure is not itself a periodicity/Hall theorem. `ownerWords` is the explicit list of the
20 minimal P2 words of lengths 3, 7, and 11. In the current registered periodic application,
`tight_owner_family` constructs the structure from its full concrete signature, including Hall and
tightness. This records the present proof dependency, not a uniqueness claim about all possible
ways of realizing the structure.

## `short_tight_avoids_ss2_donor`

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

- Actual object binders: yes; periodic word, positive period, phase list, windows, neighborhood,
  and donor are all explicit.
- Unproved defined `Prop` or conclusion hypothesis: no. `P2` unfolds to the concrete conjunction
  `mass = 1` and `moment = 0`.
- Wrapper: no. The proof establishes short Hall, donor classification, the periodic lift, and the
  AAS/w1 contradiction.
- Exact scope: arbitrary positive `p`, but B only has minimal P2 lag 3/7/11; donor is minimal
  lag-11 SS2. No ambient U, assumed Hall, positive drift, orbit, or arbitrary lag.

## `short_supply_donor_deletion`

```lean
theorem short_supply_donor_deletion (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat) (hUn : U.Nodup)
    (hUp : ∀ u ∈ U, u < p)
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (hU_lag : ∀ u ∈ U, lag u = 3 ∨ lag u = 7 ∨ lag u = 11)
    (hU_P2 : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hU_min : ∀ u ∈ U, ∀ d, d < lag u → 0 < d → ¬ P2 ((past e (u : Int) (lag u)).take d))
    (u0 : Nat) (hPdon : P2 (past e (u0 : Int) 11))
    (hmindon : ∀ d, d < 11 → 0 < d → ¬ P2 ((past e (u0 : Int) 11).take d))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e (u0 : Int) 11) = 2)
    (B : List Nat) (hBU : List.Sublist B U) :
    B.length ≤ (Recaman.TwoSSTightDisjoint.deletedNeighborhood e p B lag
      (Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11)).length := by
```

- Actual object binders: yes.
- Unproved defined `Prop` or conclusion hypothesis: no.
- Wrapper: not a syntactic wrapper, but mathematically a direct composition. It restricts all-U
  assumptions to B, proves short Hall, and invokes Q plus generic tight/slack deletion.
- Exact scope: arbitrary positive period, but every member of U is short minimal P2 lag 3/7/11.
  U need not be complete and the donor need not lie in U. No arbitrary-lag complete-U conclusion.
- Novelty: no new mathematical input beyond E-360 Q and existing deletion lemmas; no E-row.

## Bidirectional prose audit

The proposed weekly wording implies each formal statement only after retaining all restrictions
above. Conversely, the formal statements imply exactly the proposed restricted conclusions.
Neither direction licenses finite-to-infinite inference from p32/33, periodic-to-orbit transfer,
G2-to-general-T6 transfer, or a fixed-offset-11 replacement for `trueOldestPhase`.
