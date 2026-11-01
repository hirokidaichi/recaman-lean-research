# Verbatim statement and dependency audit

Target SHA-256: `a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de`.
This audit is limited to the following three declarations.

```lean
theorem moment_ending_A_budget (w : List Bool) (q : Nat)
    (hss : ssCount (w ++ [true]) ≤ q) :
    (q : Int) + 1 ≤ moment (w ++ [true]) + q * (w ++ [true]).length
```

```lean
theorem moment_ending_AA_ss2 (w : List Bool)
    (hss : ssCount (w ++ [true, true]) ≤ 2) :
    5 ≤ moment (w ++ [true, true]) + (w ++ [true, true]).length
```

```lean
theorem ss2_intervening_prefix (w : List Bool)
    (hm : mass (w ++ [true]) = 0)
    (hM : moment (w ++ [true]) + (w ++ [true]).length ≤ 0)
    (hss : ssCount (w ++ [true]) ≤ 2) :
    ∃ u v : List Bool, w ++ [true] = (u ++ [false]) ++ v ∧
      P2 (u ++ [false]) ∧ v ≠ []
```

`P2 z` unfolds to `mass z = 1 ∧ moment z = 0`; `true` is A and `false`
is S. Thus the conclusion is exactly a strict (`v != []`) prefix ending S
which is P2. Conversely every finite word ending A is `w ++ [true]`, so the
paper lemma and Lean statement imply one another without an extra case.

## Direct proof chain

`moment_ending_A_budget` structurally inducts on `w`. It applies the existing
proved `mass_ending_A` to the full A-ended suffix and the induction hypothesis
to the tail. This is the paper identity that moment is the sum of suffix masses:
all suffix masses are at least `-q`, while the last A has mass 1, giving
`moment + q*length >= q+1`. There is no fixed word-length premise.

`moment_ending_AA_ss2` structurally inducts on `w`. Its base word is `AA`, where
the bound is equality. For each prepended bit, the full suffix mass is at least
`-1`: remove the final A, apply `mass_ending_A` at SS budget 2, then restore A.
Hence `moment+length` never decreases below 5. This is the second inequality
in paper section 1 and has no length cutoff.

`ss2_intervening_prefix` is well-founded recursion on `w.length`. Empty `w`
contradicts mass zero. A final `AA` contradicts `moment_ending_AA_ss2`. A final
`SA` strips that pair. If the remaining word ends A, the theorem recurses on a
strictly shorter word with the same three kinds of hypotheses. If it ends S,
the proof derives a mass-one, nonpositive-moment prefix. Its SS budget is at
most one, handled by `lowSS_A_nonpositive_prefix`; the terminal S case consumes
the remaining two adjacent SS edges, yields SS count zero, and uses
`zero_SS_nonpositive_prefix`. Every returned suffix is extended by `SA` or
`SSA`, so `v != []` is constructed rather than assumed.

The direct dependency direction is acyclic. The two inequalities do not call
the target theorem. The low-SS prefix lemmas are in the imported older module
`LowSSEndpoint` and do not import `SS2OldestPattern`. Recursive calls are only
on shorter lists, with explicit termination proof. No defined unproved `Prop`,
OwnerFamily field, stream hypothesis, periodicity, orbit premise, or conclusion
itself occurs among the hypotheses.

## Harness and semantic attacks

The declarations bind structured Bool words and use `mass`, `moment`,
`ssCount`, and `P2`; they are not arithmetic over free Nat/Int variables.
Their bodies perform induction and case analysis, not an intro/exact wrapper,
bare `omega`, `rfl`, `H -> H`, or `x=x`. `report_vacuity --all` flags 0/13 and
module lint calls all 13 declarations substantive, but those are heuristic
checks only. `#print axioms` reports only the repository-allowed core axioms
`propext`, `Classical.choice`, and `Quot.sound` for the target declarations.

All binary words through length 18 give 8 target-premise instances: 3 on
`moment+length=0` and 5 with strict `<0`. The smallest is
`AASASASASSSA` (length 12, mass 0, moment -12, SS 2) and it has P2 prefix
`AAS`. Exhaustive checks also cover 434,721 instances of the q-budget inequality
(q from actual SS count through 4) and 45,976 instances of the AA inequality.
These are finite checks, not proofs.

Removing one premise has a concrete negative control through length 18:

- ending A: `AAASSS`, mass 0, moment+length -3, SS 2, no strict S-ended P2 prefix;
- mass zero: `SASASSSA`, mass -2, moment+length 0, SS 2, no such prefix;
- moment bound: `SA`, mass 0, moment+length 3, SS 0, no such prefix;
- SS bound: `AAASSSSA`, mass 0, moment+length 0, SS 3, no such prefix.

The E-130 canonical `AAASSSASASA` window at standard step 115 is also not a
counterexample: it has current A, SS 2, an old A endpoint, and no S-ended P2
prefix, but it fails this theorem's mass-zero/moment-plus-length premises. This
is why the theorem must not be described as the refuted general SS<=2 prefix
normalization.

## Scope and inclusion

The modified uncommitted `Recaman.lean` imports this module. `Recaman/Audit.lean`
does not name this module or these theorems, and registry E-360 explicitly leaves
`SS2OldestPattern` for separate audit. The source file itself is untracked.
Direct Lean compilation and the full check pass, but there is no registered
row or Audit inclusion for this candidate.

Paper sections 3-5 and source declarations after line 138 are downstream
inventory only: AAS/w1 oldest-S exclusion, actual `past` decomposition,
OwnerFamily/periodic transport, arbitrary-length donor avoidance, deletion,
full-U capacity, and orbit claims were not semantically audited here. In
particular H-02 and H-03 remain `CONJECTURED` with the historical independent
entry gap, and this packet cannot repair that gap or establish H-05 as a whole.

Semantic judgment for the bounded three-declaration candidate: pass, confirmed
by the independent Sol. Novelty judgment: a genuine length-independent local
word lemma, but not yet a stable registered result and not the H-05 conclusion.
The overall H-05 procedural judgment is incomplete, and its card remains
`CONJECTURED`.
