# H-20260920-02 candidate packet, 2026-09-23 01:30 JST

## Conclusion first

Candidate for independent semantic audit, not a promotion: the existing
`short_tight_avoids_ss2_window` appears to state and prove H-20260920-02 for
every positive period and integer donor clock, without donor minimality or
donor current A. The member windows remain minimal P2 of lag 3/7/11. I have
not certified this conclusion independently. The different Sol must attack
the exact source SHA below before the parent changes the card or registry.

## Frozen question and stopping condition

Question: does the exact Lean signature match all quantifiers in H-02 and do
the existing proof and finite table exclude the nonminimal lag-11 SS2 donor's
true oldest S from the concrete neighborhood of every short tight B?
Acceptance: literal signatures and four-field OwnerFamily expansion, a
nonempty nonminimal witness, negative controls, all 12 SS2 words, dependency
audit, Lean diagnostics and an independent adversarial audit of this version.
Stop on a full-premise counterexample, a hidden conclusion hypothesis, a
failed dependency, or an unverified check at the deadline. No scope weakening.

## Exact target signature

Source `Recaman/ShortTightDonorAvoidance.lean`, theorem at line 486. The
fully elaborated literal `#check` result is in `diagnostic.stdout`; source
text below is copied verbatim from the frozen file:

```lean
theorem short_tight_avoids_ss2_window (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat) (hBn : B.Nodup)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p)
    (hBA : ∀ b ∈ B, e (b : Int) = true)
    (hlag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hP : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hmin : ∀ b ∈ B, ∀ d, d < lag b → 0 < d → ¬ P2 ((past e (b : Int) (lag b)).take d))
    (u0 : Int) (hPdon : P2 (past e u0 11))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e u0 11) = 2) :
    phase p (u0 - (oldestOffset (past e u0 11) : Int)) ∉ neighborhood e p B lag := by
```

`P2 w` is `mass w = 1 ∧ moment w = 0`; `past e u d` is newest-first
`[e(u-1),...,e(u-d)]`; `ssCount` counts overlapping adjacent SS pairs;
`oldestOffset` selects the largest one-based S offset. `neighborhood` is the
actual filtered subtraction phases covered modulo p by B's windows, not an
independent arbitrary set. The target names e, p, B, windows and phase;
there is no defined Prop premise concealing the conclusion.

## Dependencies and possible attack points

1. `short_window_hall`: existing shortOff is injective on short supplied
   phases and its charge lies in each actual chosen P2 window. This discharges
   Hall for all sublists of B without assuming ambient U, full-U or mass sign.
2. E-358/E-359 `tight_owner_family`: Hall and tightness yield an Int-lifted
   OwnerFamily. Its four fields expand to `window` in the 20 minimal words,
   `addA`, `own_mem` (one owned S per member), and `onto` (every S in any
   member window is owned by a member). No injectivity is needed downstream.
   Its construction uses B as U and only B's minimal lag 3/7/11 premises.
3. E-357 excludes lag11 and w2 members, leaving AAS/w1. Existing
   `w1_owns_oldest` and `w1_future_aas_member` use `onto`, bit compatibility,
   and single-valued `own` to force member t+2, lag3, AAS, owner t-1.
   This future-member theorem is an existing dependency, not a new result of
   this slot. E-351's conditional future-AAS premise is not used in this proof.
4. `mem_ss2Windows` puts every P2/SS2 length-11 word into `ss2Windows` with
   no minimality. `ss2_oldest_cover_table` uses `decide` on the actual 2048
   binary words: 12 qualify, five are nonminimal. It checks both w1 overlap
   and the three A bits needed to exclude AAS at the covered oldest S.
5. `owner_member_avoids_ss2_window` separates AAS from w1 and compares the
   donor's true `oldestOffset` to an actual covering clock. The periodic target
   lifts a covered phase to an integer clock and applies this line theorem.
   Check phase transport for negative clocks and p=1 carefully.

No theorem in the chain assumes the target conclusion, `H → H`, `x=x`,
positive period mass, complete supply U, donor current A, or donor minimality.
This is not a pure Nat/Int arithmetic theorem or a wrapper-only proof.
Lean acceptance and heuristic lint do not establish those semantic findings;
the audit Sol must verify them against source and countermodels.

## Falsification evidence (author's, not independent certification)

`recheck.py` examines all 2048 length-11 words without donor current A. Raw
output is `recheck.jsonl`: 12 P2/SS2 words, 7 minimal and 5 nonminimal;
compatible covers AAS 0, w1 5, w2 2. Every w1 cover clashes with the forced
future AAS member's current/past A bits. Translations -101,-1,0,1,101 give
the same clash. The w2 possibilities remain visible and are removed by E-357,
not silently omitted from the table.

Concrete nonempty nonminimal control: period 13 `AASSSAAAASSSS`, u0=10,
donor `SAAAASSSAAS`, donor current S, proper P2 prefix length 7, true oldest
offset 11 and phase 12. B=[7] has minimal AAS and N(B)=[4], so tightness and
avoidance both hold. This demonstrates the extra scope is inhabited but is
not a proof of the universal statement. A w1-only model with `mem={0}` and
future signs SS is consistent after removing `onto`; this is a weakened
history control, not a counterexample to all four OwnerFamily fields.

The historical p13/p14 exhaustive runs were rerun from the frozen prior
script (`old_holdout.jsonl`) and remain **known data**, not a fresh holdout:
8192/16384 cycles, 221/532 nonminimal donor-tight B checks, 143/658
nonpositive-mass checks, 0 violations. `old_local.jsonl` reproduces the
12-word table. The 01:00 independently audited H-04 lag15 counterexample
does not satisfy lag11 and must not be folded into this claim. E-240 refutes
pure AAS forcing but allows w1 here; E-069 refutes a global oldest-S injection
but the proof uses a short injection and avoids only one donor S; E-345 is the
SS>=3 deletion countercontrol. E-180 is unrelated collision-slack-linear.

The first two versions of `recheck.py` failed because I guessed a prefix3 and
then phase0 for the p13 example. The actual values are prefix7 and phase12.
`recheck_v1.py` / `recheck_v2.py` are post hoc reconstructed sources and their
rerun stdout/stderr, while `recheck.stderr` / `recheck_after_fix.stderr` are
the original failure outputs. The original pre-run source files and SHA were
not captured, a provenance limitation the audit must see. These
were errors in the new checker expectations, not a repair of H-02 or the
original card. The older Lean 2-bit clash failure and its single 3-bit
correction remain archived in `docs/data/issue73_20260920/daytime/`.

## Scope and state

H-02 stays `CONJECTURED` until separate Sol audit and parent review. E-360
already registers the minimal donor Q/W only. H-03, H-05,
`SS2OldestPattern`, all-lag B, full-U capacity E-070, general Gate T6 and
actual Recaman orbit claims are not dependencies or consequences.
Historical daytime work lacked the required independent preformalization
entrance check; this later review cannot retroactively fix that omission.
The original card is untouched. `proposed_card_final.md` is a candidate for
the parent only after independent audit.
