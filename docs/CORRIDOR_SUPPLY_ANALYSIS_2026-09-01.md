# P4 paper analysis — branch-A corridor supply/demand and branch-B assessment

Date: 2026-09-01. Analysis only; no repo files touched.
Base: `Recaman/TargetTailResidualKernel.lean` (A/B kernel), `docs/TWO_HOUR_RESEARCH_REPORT_2026-09-01.md`,
`docs/PARALLEL_RESIDUAL_DECOMPOSITION_2026-09-01.md`, `docs/RESET_REPAYMENT_AUDIT_2026-09-01.md`.
A mid-task course correction from the coordinator (strip freezing is free; refocus Q-B on blocker
births) is incorporated throughout; Section 2 records the verification of that correction.

Notation. `d m := nextSubtractionCandidate m = a m - (m+1)` (`Recaman/TargetCandidateTransitions.lean:22`).
Step law (`Recaman/Basic.lean:48`): subtraction iff `m+1 < a m ∧ d m ∉ valuesThrough m`, giving
`a (m+1) = d m` (a fresh first occurrence, `firstAt_succ_of_canSubtract`,
`Recaman/ActualDescent.lean:43`); otherwise `a (m+1) = a m + (m+1)`.
Candidate walk: addition ⟹ `d (m+1) = d m + m`; subtraction ⟹ `d (m+1) = d m - (m+2)`.
After any addition, `d (m+1) = a m - 1` (predecessor of the pre-addition value).
Branch A (`EventualHighCandidateTail target tailStart`, kernel line 142): ∃ cutoff `C ≥ tailStart`,
∀ `n ≥ C`, `target < d (n+1)`; hence the corridor floor `a m > m + 1 + target` for all `m ≥ C+1`.

## 0. Free-fact discipline (applied to both questions)

Three facts hold for the bare recurrence, with no tail hypothesis, and any candidate lemma whose
conclusion is derivable from them is contentless:

- F1. A value `v` can be visited at a clock `> v` only by a legal subtraction, i.e. as a first
  occurrence; so `v` has at most one visit after clock `v` ever. (Additions at clock `c` land
  `a c = a (c-1) + c ≥ c`.)
- F2. Any band `[0, E]` receives at most `E+1` subtraction landings ever (fresh landings are
  first occurrences of distinct values) and additions land in it only at clocks `≤ E`. Hence
  "the orbit eventually exceeds `E`" is free for every fixed `E`, and so is "only finitely many
  comb entries `< E`" (entries are distinct first occurrences).
- F3. Consequently `liminf a = ∞` is free; no contradiction can be extracted from divergence of
  the orbit against a fixed bound, and no conclusion of the shape "orbit/entries eventually
  exceed a fixed `w`" carries content.

Every finding below was audited against F1–F3. What survives is exactly the material whose
conclusions are either (a) against the *moving* cone `clock + target`, (b) existence of
permanently missing values, or (c) exact membership demands at prescribed clocks.

## 1. Q-A findings (branch A)

### 1.1 Provenance of consumed candidates; what is special about the corridor

In the corridor every forced addition at clock `m+1` consumes a visited value `d m > target`
(positivity is automatic: `d m > target ≥ 1` gives `m+1 < a m`; so forced ⟺ visited). Consumed
values have exactly three provenances:

1. pre-corridor history: at most `C+1` values, all `≤ upperTri C` — finite, bounded;
2. corridor subtraction landings: value `> clock + target + 2` at birth (P3's bound; equivalently,
   the corridor at the next clock forces `d m > m + target + 2` for a legal subtraction at `m+1`);
3. corridor addition outputs: value `= a (m) + m + 1 > 2m + 2 + target` at birth (may be revisits).

Hence **every corridor visit has birth clock `< value - target`**, and (by F1) a fixed value can be
freshly landed at most once late. Two structural consequences that are *not* free:

- (No late low landings.) For `m ≥ C+1`, a subtraction at `m+1` needs `d m > m + target + 2`; so a
  landing of any *fixed* value `v` at late clocks is impossible (`v ≤ m + target + 2` eventually).
  This is P3's contrapositive; I treat it as available, not new.
- (Cone freezing.) For `m ≥ C+1` and `u ≤ m + 1 + target`: if `u ∉ valuesThrough m` then `u` never
  occurs (later additions land `> clock + target ≥ u`; later subtractions land above the cone).
  Content beyond F1 is exactly the exclusion of the single allowed late fresh landing — small but
  real, and it is the engine of 1.3.

### 1.2 Main find: the liminf dichotomy and the rigid recurrence pattern

The corridor's candidate walk `d` satisfies a total dichotomy: either `d` diverges, or its liminf
is a finite integer `c > target` attained unboundedly often. The non-divergent branch is far more
rigid than the raw definition suggests. Take `c` := the **least** value that recurs unboundedly as
a candidate at corridor clocks (well-ordering; the set is nonempty by infinite pigeonhole on the
finite band `(target, K]` supplied by non-divergence). Since each value in `(target, c)` recurs
only boundedly and the band is finite, there is `M₁` with `d m ≥ c` for all `m > M₁`. Then for
every "use clock" `m > max(M₁, c) + 2` with `d m = c`:

- (P-a) `c ∈ valuesThrough m`, and the step at `m` is a **forced addition**. Otherwise subtraction
  lands `a (m+1) = c`, and `d (m+1) = c - (m+2) = 0 < target` (Nat truncation, `m ≥ c`) breaks the
  corridor.
- (P-b) The step `m-1 → m` is a **legal subtraction**, so `a m = c + m + 1` is a fresh first
  occurrence (`FirstAt a (a m) m`). An addition would force `a (m-1) = c + 1`, below the corridor
  floor `a (m-1) > m + target`.
- (P-c) `d (m+1) = a m - 1 = c + m` must be **visited by clock `m+1`**. Otherwise it is landed at
  `m+2` and `d (m+2) = (c+m) - (m+3) ≤ c - 3 < c` (truncation covers `c < 3` since `c > target ≥ 1`),
  contradicting `d ≥ c` past `M₁`.

So the non-divergent corridor contains an infinite stream of events, each consisting of: a fresh
landing exactly on the diagonal `value = clock + c + 1`, immediately followed by a forced addition
consuming the same fixed value `c`, immediately followed by a second forced addition whose
candidate `c + m` was **already visited**. The per-use demand `c + m ∈ valuesThrough (m+1)` is the
genuinely new supply/demand object:

- it cannot be met by the pre-corridor history for late `m` (values `≤ upperTri C`);
- it cannot be met by the stream's own entries: the entry at use `m'` is `c + m' + 1`, equal to
  `c + m` only if `m' = m - 1`, and `m-1` is a subtraction clock (P-b), never a use clock;
- it **can** be met by the stream's own forced-addition outputs: the first output of use `m'` is
  `c + 2m' + 2 = c + m` iff `m = 2m' + 2` (and the second output `c + 3m' + 4` similarly), so
  self-supply is possible only along a doubling/tripling clock lattice — precisely the
  `upperTri`-shaped skeleton of the seeded no-go family, now forced to be *generated by the
  canonical orbit itself* rather than seeded.

This does not yet close branch A, and I do not claim it does. Its value: it is the first
consequence of the *infinite* corridor that (i) is not free by F1–F3, (ii) is immune to the
seeded-corridor no-go (its hypotheses and conclusions quantify over arbitrarily late clocks; every
seeded object is finite), and (iii) converts the "generation-versus-reuse chronology" reopening
gate from a slogan into a concrete infinite ladder: each use clock `m` demands a birth witness
`j(m) ≤ m+1` for the value `c + m` (distinct values ⟹ injective witnesses), with the only
unbounded suppliers being high landings/outputs on prescribed diagonals. The next paper round
after this lemma is the classification of the birth witnesses `j(m)` and whether the doubling
lattice is consistent with `a j ≤ upperTri j` and the landing floor simultaneously — an attack
that finite seeds cannot preempt.

Stress tests (per method requirements):
- Seeded family `L + 2 + upperTri j` (no-go 3): finite pure-addition corridors; the lemma's
  conclusion is about unboundedly many use clocks. Not refutable and not mimicable: an infinite
  corridor with finite liminf *must* exhibit the pattern; a seed only ever exhibits finitely much
  of it, and the demand ledger (P-c) is exactly what a seed satisfies by fiat while the canonical
  orbit must satisfy it by generation. The lemma respects the no-go: it proves no uniform finite
  bound.
- Standard prefix: within real high excursions the mechanism sub-landing → forced-add with
  candidate reuse (documented reuse up to 13×) is exactly the observed shape; P-a–P-c are
  window-local (they need the corridor property only on `[m-1, m+2]` plus `d ≥ c` on a window),
  so no finite prefix can refute them. Honesty note: the eventual-floor input `d ≥ c` is
  available only at infinity, so the lemma's content lives strictly at infinity — by design,
  since no-go 3 kills all finite-window content.
- Vacuity: the dichotomy is total; either disjunct may be vacuous under branch A, which is itself
  a counterfactual — the same status as the kernel.
- Not from ledger/counting: the ledger identities are telescoping equalities and cannot express
  the minimality of `c` or freshness forcing; counting yields only lower bounds. The proof inputs
  are integer well-ordering, step determinism, and the corridor floor — none banned.
- Minimal countermodel that would refute it: an infinite corridor with a recurring candidate `c`
  where some late use has `c + m` fresh at `m+1`. The derivation shows this forces `d (m+2) < c`,
  i.e. the walk dips below its own liminf — impossible. The known countermodels do not apply
  (right ladder is a branch-B macro object; preload is branch-B; seeds are finite).

### 1.3 Secondary find: branch A forces a second permanently missing value

`valuesThrough m` is a list of length `m+1` (one cons per step, `Recaman/Basic.lean:43`), so at
most `m+1` distinct values are visited by clock `m`, while `[0, m + target + 1]` has
`m + target + 2` elements. Hence at every corridor clock `m ≥ max(C+1, tailStart)` at least
`target + 1` values `≤ m + 1 + target` are unvisited; by `below_covered` all of them are
`≥ target`, and at most one of them is `target` itself. By cone freezing (1.1) each is permanently
missing. Since `target ≥ 1`:

**In branch A there exists `u` with `target < u` and `∀ t, a t ≠ u`.**

Audit: the conclusion is an existence of a permanently missing value, not an "eventually exceeds"
statement, so F1–F3 do not trivialize it; the non-free step is exactly the corridor's exclusion of
the one allowed late fresh landing of `u`. The counting is used to *construct* a witness, not to
derive the final contradiction, so no-go 6 does not apply. It is cheap (the repo already has the
counting engine: `coveredBelowCount_le_time`, `Recaman/CoverageTimeBound.lean`), and it is the only
cardinality-type fact that survived the free-fact audit.

What it is for (paper level, not proposed for Lean yet): relative to a missing `u`, the corridor
already provides the below-`u` candidate discipline for free (candidates in `(target, u)` at late
clocks must be visited by P3's contrapositive; candidate `= target` is impossible by
`candidate_ne_target`). So the comb machinery relativizes to level `u`, and branch A splits again:
either candidates eventually exceed `u` (climbing the missing-value chain, whose limit is the
clean isolated residual `a m - m → ∞`), or `u`-low candidates recur unboundedly — which is exactly
the non-divergent case of 1.2 with `c < u`. In other words, 1.2 and 1.3 are two views of the same
reduction: **branch A reduces to (divergent walk residual) ∨ (rigid recurrence at the least
recurring candidate)**. The divergent residual `∀ K` eventually `d > K` is not free (real Recamán
candidates dip: e.g. the certified `a 99734 = 19` is a late landing of a tiny value), and is
recorded as open with no current attack.

## 2. Q-B findings (branch B)

### 2.1 Verification of the course correction: strip freezing and kernel recursion are dead

Confirmed. My initially derived "orbit eventually above root" theorem (from no-escape + comb
extraction + freshness-vs-root) is a complicated proof of free fact F2, and the same holds for
"the strip `(target, root)` receives no new landings after clock ≈ root" — every band statement of
this shape is unconditional. The recursion-on-missing-values program built on it collapses for a
second, independent reason: the level-`v` kernel instance fixes its tail start *after* `v` (it
needs the finitely many `(target, v)` occurrences collected), and by F2 an abstract adversary can
always place the finitely many below-`root_v` entries before any such cutoff. So level-`v`
no-escape certificates are automatically satisfiable by macro models and violate nothing. The one
non-vacuous by-product — at level `v` the branch-A horn is impossible because the outer stream
supplies `v`-low candidates unboundedly — only multiplies satisfiable constraints. Additionally the
adversary may take the strip fully covered, making the recursion vacuous outright. Discarded.

Note the contrast with branch A: there the pigeonhole of 1.3 *proves* missing values exist
(the corridor floor beats F2's per-band finiteness because the cone moves), which is why the
recursion idea has residual value in A but none in B.

### 2.2 Blocker-birth classification (revised Q-B focus) — result: no non-free inequality found

Setting: unbounded stream of `HistoryTerminatedComb (s_j, k_j, b_j)`, entries
`e_j = b_j + k_j + 1 = a s_j`, target-low starts so `e_j < s_j + 1 + target`
(`entry_lt_clock_add_target_of_candidateBelow`), blocker one-use across completed combs, P1/P2
(blockers `≥ root`, unbounded, infinitely many upward resets) assumed available.

Births of blocker values, exhaustively classified:

- (0) pre-tail born (`birth ≤ tailStart`): at most `tailStart + 1` values; with one-use this
  already *forces* infinitely many in-tail births — the proved half of the refuted preload
  argument. Settled; not a lever.
- (E) low-born in tail: born at a clock with target-low candidate; such a birth is itself a comb
  entry (`candidateBelow_entry_first` + comb extraction), sits under the cone
  (`b < birthclock + 1 + target`), and by the Lean-certified interval fact (a later blocker inside
  an old fresh interval cannot be an interior tooth and must equal the old entry — the
  fresh-interval order results around `HistoryTerminatedComb.fresh_intervals_ordered`,
  `Recaman/TargetCandidateTransitions.lean:616`, and the entry-return dichotomy in
  `Recaman/TargetMacroSuccessor.lean`) this channel is exactly **old-entry reuse**. Excluding it
  is precisely the stopped `TargetMacroSuccessor` gated no-return
  (`TargetMacroEntryReturnResidual`, stopped after the reuse-balance/avoidance bisection). The
  right ladder lives entirely in this channel (`b_{j+1} = e_j`); the standard prefix shows
  0/2,655 immediate entry reuse. That mismatch was already mined and stopped; nothing new here.
- (H) high-born in tail: a fresh subtraction landing with high next candidate
  (`b > birthclock + target + 1`) or a fresh forced-addition output
  (`b = a(birth-1) + birth > birthclock + target`, e.g. the preload counterexample's blocker
  `199 = 134 + 65`). Both subclasses give the same inequality `b > birthclock + target`.

Combining (H) with the use-side cone `b = e - k - 1 < s + target - k ≤ s + target` yields the only
inequality the classification produces:

    high-born blockers are born strictly before their use-comb's start:  birth < b - target < s.

This is satisfied by the right ladder under any consistent clock assignment (e.g. `s_j = 6j`,
births `c_j` anywhere below `r + j - target`), and by the preload trace (`65 < 199 - 4 < 207`). No
inequality relating birth value, birth clock, and use clock that an abstract ladder-with-clocks
must violate emerged from any combination I could construct; bounding class-(H) births inside a
no-return corridor is the audit's own "goal restated in different words" trap
(`docs/RESET_REPAYMENT_AUDIT_2026-09-01.md`, Decision section). **Stating this plainly per the
course correction: within this round's budget, Q-B yields no non-free proof input.** The
classification is a clean map of the wall — channel (E) is a stopped residual, channel (H) is the
restated goal — not a door. Recommendation: leave branch B parked on P1/P2's formalized outputs;
add no macro wrappers; reopen only on an input that survives the F1–F3 audit *and* the ladder.

## 3. Ranked recommendation: next Lean targets (at most 2)

**Target 1 (branch A) — `Recaman/TargetCorridorRecurrence.lean`:**

```lean
/-- In an eventual-high corridor the candidate walk either diverges or has a
least unboundedly recurring value `c`, and every sufficiently late use of `c`
is a fresh diagonal landing followed by two forced additions whose second
candidate `c + m` was already visited. -/
theorem EventualHighCandidateTail.candidate_diverges_or_rigidRecurrence
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hhigh : EventualHighCandidateTail target tailStart) :
    (∀ bound, ∃ cutoff, ∀ m, cutoff ≤ m → bound < nextSubtractionCandidate m) ∨
    ∃ c, target < c ∧
      ∀ start, ∃ m, start < m ∧
        nextSubtractionCandidate m = c ∧
        a m = c + m + 1 ∧
        FirstAt a (a m) m ∧
        ¬ CanSubtract (m + 1) (stateAt m) ∧
        c + m ∈ valuesThrough (m + 1)
```

Proof plan: (i) from non-divergence extract `K` and infinitely many corridor clocks with
`d ∈ (target, K]`; (ii) infinite pigeonhole by strong induction on the band to get an unboundedly
recurring value, then least such `c` by well-ordering; (iii) `M₁` from the bounded recurrence of
the finitely many values in `(target, c)`, giving `d ≥ c` late; (iv) payload facts P-a/P-b/P-c by
`omega` from the step dichotomy (`a_succ_of_canSubtract` / `a_succ_of_not_canSubtract`), corridor
floor, and truncation. Risks: the infinite-pigeonhole engineering (no mathlib; do induction on
`K - target` with explicit bounds) and index shifts in `EventualHighCandidateTail`'s `n+1`
convention. One module, one round.

**Target 2 (branch A) — `Recaman/TargetCorridorSecondMissing.lean`:**

```lean
/-- An eventual-high corridor leaves a second permanently missing value above
the target. -/
theorem EventualHighCandidateTail.exists_missing_above_target
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hhigh : EventualHighCandidateTail target tailStart) :
    ∃ u, target < u ∧ ¬ ∃ t, a t = u
```

Proof plan: fix `m₀ ≥ max(cutoff + 1, tailStart)`; `valuesThrough m₀` has length `m₀ + 1` while
`[0, m₀ + target + 1]` has `m₀ + target + 2` values — reuse the `coveredBelowCount` machinery
(`coveredBelowCount_le_time`, `exists_newBelow_of_missingBelowCount_strict`-style helpers) at
level `m₀ + target + 2` to extract `≥ target + 1 ≥ 2` unvisited values, all `≥ target` by
`below_covered`, hence one `> target`; permanence: a later addition lands `> clock + target ≥ u`,
a later subtraction landing `u` at clock `j` forces `u > j + 1 + target > m₀ + 1 + target ≥ u` via
the corridor at `j`. Cheap; independent of Target 1; supplies the level-relative structure for the
round after next.

No branch-B Lean target is recommended this round (Section 2.2).

## 4. Explicitly rejected ideas (with reasons)

1. **Strip freezing / orbit-eventually-above-root (B and A fixed-band versions).** Free by F2;
   my own derivation via no-escape was a decorated proof of an unconditional fact.
2. **Kernel recursion across missing values in branch B.** Level-`v` cutoffs are chosen after
   `v`; by F2 the resulting no-escape certificates are automatically satisfiable by abstract
   models; also vacuous under a fully covered strip. (Its branch-A remnant survives only as the
   paper-level reduction in 1.3, and only because the moving cone defeats F2 there.)
3. **Landmine avoidance as a standalone lemma** (`d m ≠ u₀` for missing `u₀` late): subsumed by
   P3's contrapositive; carries no content beyond it.
4. **Entry-chain exclusion (killing the right ladder via `b₂ ≠ e₁`).** This is the stopped
   `TargetMacroSuccessor` gated no-return; the classification of 2.2 re-derives its exact scope
   and adds nothing — do not reopen.
5. **Bounding post-reset class-(H) blocker births.** The audit's restated-goal trap; confirmed
   that every inequality obtainable from the birth classification is ladder-satisfiable.
6. **Counting-based supply/demand contradictions in the corridor** (injectivity of consumption,
   reuse bounds, density of below-cone visited values): banned by no-go 6 and refuted by the
   reuse/multiplicity data; the rigidity lemma deliberately extracts membership demands instead.
7. **`liminf a = ∞` (or any fixed-bound divergence) as a contradiction source.** Free by F3.
8. **Immediate contradiction from the successor demand `c + m ∈ V (m+1)`** ("the stream cannot
   supply itself"): false as stated — forced-addition outputs supply the demand along a doubling
   clock lattice (`m = 2m' + 2`); the correct next step is the birth-witness classification, not a
   one-line contradiction.
9. **Uniform corridor bounds of any kind.** No-go 3 (seeded corridors of arbitrary finite length);
   both targets were checked to prove nothing of this shape.
