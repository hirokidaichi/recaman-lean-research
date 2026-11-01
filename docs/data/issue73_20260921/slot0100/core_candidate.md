# Core W/Q reproduction record

## Bounded question

Does the frozen working-tree core in `Recaman/ShortTightDonorAvoidance.lean`, through
`short_tight_avoids_ss2_donor`, state and compose the local W and short tight-donor Q from
H-20260920-01 and H-20260917-01 without assuming the conclusion, using E-357/E-358/E-359's
actual OwnerFamily construction?

Acceptance test: freeze hashes; quote all core binders; map every card premise and conclusion in
both directions; identify every non-formal dependency; reproduce vacuity/lint/Lean checks and
nonempty/negative controls. A separate new Sol decides the adversarial audit.

Stopping condition: any source change, hidden future-A/oldest-avoidance premise, fixed-offset-11
substitution, empty-only applicability, circular E-351 use, timeout, or 01:22 JST. No source was
changed by this slot.

## Exact core interfaces

`core_signatures.txt` mechanically extracts the exact source lines for all 10 declarations in
`ShortTightDonorAvoidance.lean` through the review boundary, the `OwnerFamily` structure, and the
two extracted construction/refactor declarations `ownerFamily_of_minimal` and
`tight_owner_family`. The source signatures frozen in `MANIFEST.md` include:

```lean
theorem member_window_aas_or_w1 (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t) :
    past e t (lag t) = aas ∨ past e t (lag t) = w1

theorem w1_owns_oldest (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : own t = t - 7

theorem w1_future_aas_member (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) :
    mem (t + 2) ∧ lag (t + 2) = 3 ∧ past e (t + 2) 3 = aas ∧ own (t + 2) = t - 1

theorem w1_next_addition (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : e (t + 1) = true
```

Periodic W has binders `e,p,hp,hper,U,B,lag,hU,hhall,hB,htight,hBp,hB_A,hB_lag,hB_P2,
hB_min,t,ht,hw` and conclusion `e (t + 1) = true`. In particular Hall is explicit, member
windows are minimal P2 of lag 3/7/11, and `phase p t ∈ B` is explicit. It is a wrapper around the
constructed OwnerFamily plus local W; the lint tool correctly classifies this wrapper as such.

The Hall-free semantic Q is quoted verbatim in the daytime statement-audit draft and was checked
against source lines 333-358:

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
    Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11 ∉ neighborhood e p B lag
```

The daytime statement-audit draft quotes exactly the seven symbols cited by its proposed E-360
row: `shortOff_le_window`, `short_window_hall`, `w1_owns_oldest`, `w1_next_addition`,
`short_tight_avoids_trueOldest`, `short_tight_avoids_ss2_donor`, and the non-core
`short_supply_donor_deletion`. Those seven quoted signatures match the frozen source. It does not
quote `member_window_aas_or_w1`, `w1_future_aas_member`, `tight_w1_next_addition`, or
`donor_cover_next_subtraction`; their verbatim source is preserved only in `core_signatures.txt`
for this slot. Therefore the daytime draft is not described as a complete audit of all core
declarations.

## Dependency chain

1. `shortOff_le_window` proves the existing short selector lands inside the actual P2 window;
   `short_window_hall` combines this locality with the existing injection to prove Hall for every
   nodup list of current A phases with P2 lag at most 11.
2. `PeriodicOwnerFamilyLagEleven.tight_owner_family` uses E-358's `tight_owner_map` and periodic
   phase lifting to construct an actual `OwnerFamily`. The refactor extracts code already used by
   E-359; registered E-359 theorem signatures remain unchanged.
3. `member_window_aas_or_w1` uses E-357's `no_lag_eleven_member` and `no_w2_member`. It does not
   assume pure AAS; E-240's lag-7 w1 member remains allowed.
4. `w1_owns_oldest` uses `OwnerFamily.onto`, E-353's paired-older-S exclusions, and functional
   `own`. `w1_future_aas_member` exhausts AAS/w1 owner offsets for the newest S. This yields W.
5. `donor_cover_next_subtraction` uses E-348's three lag-7 placements and donor bits to obtain S
   at the w1 next clock. W gives A at the same absolute clock.
6. `short_tight_avoids_trueOldest` transports a periodic neighborhood cover to an absolute clock,
   handles AAS by E-350, and w1 by the A/S contradiction. `short_tight_avoids_ss2_donor` converts
   semantic minimal-P2+SS2 donor premises to the seven `donors` and supplies Hall via step 1.

There is no occurrence of `TightHallAugmentation`, `aas_after_w1_forced`, `w1_sibling_forced`, or
`hall_forces_membership` in the three frozen core/dependency files. Thus E-351 is not a premise of
W. `OwnerFamily` is still a defined structural Prop for the local lemmas; only the periodic and
semantic consequences discharge it by construction.

## Card-to-formal and formal-to-claim audit

- Original Q to Lean: U completeness, positive sign sum, `u0 ∈ U`, `lag u0=11`, `u0 ∉ B`, Hall
  on U, and B sublist U are stronger than needed by the semantic theorem. They provide the theorem's
  donor and B hypotheses; no original assumption is contradicted. The theorem proves the same
  `trueOldestPhase` nonmembership.
- Lean to intended claim: the theorem is only for arbitrary periodic sign words and B windows whose
  minimal lags are 3/7/11. It does not prove general Gate T6, all-lag capacity, U completeness,
  minimal lag for phases outside B, or any Recaman-orbit result.
- W card to Lean: local W is stronger than periodic W, conditional on the exact four OwnerFamily
  fields. The periodic theorem constructs those fields from explicit Hall+tightness+minimal short
  windows. No future sign or oldest ownership occurs in those fields.
- True oldest: `oldestOffset` is 10 for d1/d2/d3/d6 and 11 for d4/d5/d7. The proof calls
  `trueOldestPhase`; it does not replace it by fixed offset 11 or confuse phase equality with
  absolute-clock equality.

## Reproduction results

- `report_vacuity.py --all`: exit 0; 0/21 flagged.
- `harness_gate.py --lint-module`: exit 0; 20/21 substantive; periodic W wrapper is the only
  non-substantive classification.
- `lake env lean Recaman/ShortTightDonorAvoidance.lean`: exit 0.
- `lake build Recaman.ShortTightDonorAvoidance` with a 180-second timeout: exit 0, 110 jobs.
  The three frozen source hashes remained unchanged after the dependency-aware target build. This
  is a supplementary core check, not a substitute for the failed full repository gate.
- `lake env lean Recaman/Audit.lean`: exit 0; the core declarations report only the repository's
  allowed `propext`, `Classical.choice`, and `Quot.sound` axioms.
- Forbidden-term scan of the core and two refactored dependency files: no `sorry`, `admit`,
  `native_decide`, or user `axiom` match.
- `./scripts/check.sh`: exit 1 before the build because the unrelated, explicitly unreviewed
  `Recaman.SS2OldestPattern` is outside the `Recaman` root closure.
- p<=11 finite replay: 1,872 positive-mass words, Q nonempty 52, W occurrences 32, violations 0.
  This is `OBSERVED`, not a proof.
- Local replay: nonempty family members `{-3,0,2}`, words `{AAS,w1,AAS}`, owners
  `{-6,-7,-1}`; removing onto or functional ownership permits next S. The p20 proper-U example
  and the p10 periodic W example replayed.
- Controls replayed: E-240 non-AAS tight B; p15 true offset10/phase8 while fixed offset11/phase7
  is A; p12 SS3 cover counterexample; p8 W without tightness has next S.

The implementation/reproduction pass found no statement drift or hidden conclusion in this frozen
core. This sentence is not the required independent adversarial verdict and must not be used for a
registry promotion.
