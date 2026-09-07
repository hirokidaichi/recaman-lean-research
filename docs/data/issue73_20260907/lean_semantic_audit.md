# Issue 73: independent Lean semantic audit

- Auditor: entry_barrier; date: 2026-09-07.
- Audited source: `Recaman/ShortPeriodicSupply.lean`.
- Base revision: `b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`.
- Audited final source SHA-256:
  `d6f89f0fedbe89057157dc56ad8dce2409a2a12abae085846871e24f1966763e`.
  Initial read/compile SHA-256 before the parent added module documentation,
  a linter-only proof adjustment, and the long-lag control:
  `2e7c372d4abfbc5f35f3ce7f35df35e9514d83f85cbd1678c0a05aa564ea6a9e`.
- Question: do `periodic_capacity` and
  `exists_phase_without_short_supply` formalize the intended all-period
  short-lag count and obstruction, with the original backward P2 identities?
- Acceptance: exact history/weights/lag range, correct period counts, and an
  unrestricted period telescope; reject any hidden word-horizon assumption or
  a vacuous substitute for the positive-word claim.
- Scope: read-only source audit. No Lean source or shared registry edits.

## Conclusion

**PASS.** The exact source compiles independently and its end statements match
`|U7|<=|D|` and the positive-period existence of an A phase without P2 supply at
lags 1 through 7. The 128-state calculation is a complete local certificate for
the seven-sign window; the subsequent induction proves the result for every
period length. There is no hidden bound on the period.

This audit approves the semantics and standalone Lean check. At this audit's
completion the repository-wide import/Audit integration and `./scripts/check.sh`
were still the parent's next step; the repository's complete `PROVED-LEAN`
publication gate should be recorded only after those pass.

## Exact mathematical reading of the two end statements

Take any Boolean sign function `e: Z -> Bool`, with true interpreted as +1 and
false as -1; any natural p; and any integer origin t. Assume

```
forall x in Z, e(x+p)=e(x).
```

`periodic_capacity` states that, among the p clocks `t,...,t+p-1`, the number
of current +1 signs having a backward P2 lag between 1 and 7 is at most the
number of current -1 signs. For p>0 these p clocks represent each residue
class modulo p once, so this is precisely `|U7|<=|D|`. A nonminimal period is
allowed; repeating a fundamental word simply repeats its counts.

If the sign sum over those p clocks is positive,
`exists_phase_without_short_supply` supplies an index `i<p` such that
`e(t+i)=true` and there is no natural d satisfying

```
1<=d<=7,
sum_(j=1)^d sign(e(t+i-j))=1,
sum_(j=1)^d j*sign(e(t+i-j))=0.
```

No arbitrary-lag impossibility follows. The source does not state full Hall,
an injection of all supplied phases, nonperiodicity of an actual greedy orbit,
surjectivity, or nonsurjectivity. The paper consequence “some minimum lag is at
least 11 if every A is supplied” additionally uses the separate d=3 mod 4
arithmetic fact; that fact is not a theorem in this module.

## Window and P2 audit

- `sign true=1` and `sign false=-1`, agreeing with A/S throughout the cards.
- `window e t` explicitly encodes the seven actual values
  `e(t-1),...,e(t-7)`, with the newest value in bit 0. The word is not supplied
  an arbitrary disconnected history state.
- `advance` left-shifts the previous seven-bit state, appends current `e t`
  in bit 0, and discards only the eighth-oldest bit. `encode_advance` checks
  the encoding identity, and `window_advance` proves that this state update
  equals `window e (t+1)` with all integer clock offsets reconciled.
- `window_bit` relates every bit i<7 to `e(t-(i+1))`. The two subsequent lag
  lemmas transfer both sums to that exact source function.
- `List.range d` contains i=0,...,d-1, so weight i+1 corresponds to backward
  distance 1,...,d. `window_lagMoment` explicitly gives integer multiplication
  by the cast of i+1; there is no natural-number truncation of negative signs.
- `supplied` tests k=0,...,6 and d=k+1. `supplied_window_iff` proves both
  directions of equivalence with `1<=d<=7` and the exact P2 definition. The
  bridge does not merely prove a sufficient mask criterion.
- There is no current-positive hypothesis inside P2 itself, which is correct:
  P2 is a backward arithmetic property. `suppliedCount` separately requires
  both current `e(t+n)=true` and a supplied window, so S phases cannot be
  accidentally counted as supplied additions.

## Potential, induction and count audit

`potential_step` proves, for every `Fin 128` state and both possible current
signs,

```
potential(old) + charge(old,current) <= potential(new).
```

The proof uses ordinary `decide`, not `native_decide`, on this genuinely finite
domain. It is a local universally quantified Lean theorem, not an assertion
that sampled words or periods were checked. The hardcoded potential values
are an independently checkable certificate; their derivation is not assumed
as an axiom.

The charge is +1 for a supplied current A, 0 for an unsupplied current A, and
-1 for every current S. `chargeSum_eq_counts` proves the signed difference
`suppliedCount-subtractionCount`. The analogous `signSum_eq_counts` proves
`additionCount-subtractionCount`; these are cast to Int before subtraction.

Every recursive count at n+1 adds exactly clock `t+n`, hence n clocks means
`t,...,t+n-1`. There is no duplicated endpoint or omitted first phase.
`chargeSum_le_potential` inducts over arbitrary n and uses `window_advance` at
clock `t+n`, yielding

```
chargeSum(t,n) <= potential(window(t+n))-potential(window(t)).
```

Global periodicity implies equality of the endpoint windows, including all
seven preceding signs, even when p<7. Substituting n=p cancels the potential
and gives the intended count inequality. No assumption such as p>=7, p<=128,
or an enumerated maximum period appears. The number 128 bounds only local
states, and 7 bounds only supplier lag.

Finally, if every A in the p clocks were supplied,
`suppliedCount_eq_additionCount_of_all` would equate the two counts. Capacity
would then give additions<=subtractions, contradicting the positive sign sum.
The contradiction proof constructs exactly the negated P2 existential in the
stated lag range; it does not switch to a weaker conclusion.

## Boundary and semantic controls

- p=0 is permitted by `periodic_capacity` and gives 0<=0. In the existence
  theorem `signSum e t 0=0`, so its positive-sum hypothesis is impossible.
  This harmless zero case does not make the p>=1 theorem vacuous.
- Period 1 with all A is a nonvacuous positive example. Every candidate moment
  is `d(d+1)/2>0`, so its only phase is the required unsupplied A. Period 1
  with all S has zero supplied A and one subtraction, and cannot satisfy the
  positive-sum hypothesis.
- Period `SAAA` is a sharp capacity example: only its last A is short supplied,
  with newest-first signs A,A,S giving `1+1-1=1` and `1+2-3=0` at d=3. Thus
  suppliedCount=1 and subtractionCount=1, while additionCount=3. Reversing the
  weights/order would instead give `-1+2+3=4`; the formal window lemmas exclude
  precisely that error.
- If the weighted equation were dropped, all-A words would be supplied via
  d=1 and violate capacity. The actual `P2` and Boolean equivalence both keep
  the weighted equation, so this weakened control is correctly excluded.
- Since e is defined on all Int, negative-time windows are well-defined.
  The global-period hypothesis is appropriate for a pure periodic word. It
  does not assert that an arbitrary finite preperiod of an actual orbit is
  periodic backwards. Applying this theorem to an eventual-periodic tail
  still requires the separate reduction/periodic-extension argument; the
  module does not silently formalize that connection.
- The added `longLagControl` is the modulo-12 periodic word `SSSSAAAASAAA`.
  At phase 7 its current sign is A. `lag_eleven_survives_short_exclusion`
  proves the exact P2 identity at d=11 while excluding every d from 1 through
  7 via the same `supplied_window_iff` bridge. This is a useful formal guard
  against interpreting short-supply exclusion as absence of every supplier.
  Independently, the positive offsets are `{1,2,3,8,9,10}` and the negative
  offsets are `{4,5,6,7,11}`: there are six versus five signs, and both offset
  sums equal 33. It does not assert that this word is a realizable Recaman
  continuation.

These controls were evaluated symbolically from the definitions; this audit
does not claim a new finite computation or a new holdout range.

## Validation and remaining work

Command run independently:

```
lake env lean Recaman/ShortPeriodicSupply.lean
```

Initial version exit status: 0. Exact initial output:

```
Recaman/ShortPeriodicSupply.lean:49:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
```

During the parent's additions, intermediate SHA-256
`8c21f308bc740b6de84763bac72b7841597e4ef0f2fed969caddcd976a46b762`
failed the same independent command with exit status 1 and exact output:

```
Recaman/ShortPeriodicSupply.lean:66:46: error: No goals to be solved
Recaman/ShortPeriodicSupply.lean:248:4: error: failed to synthesize
  Decidable (P2 longLagControl 7 11)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

The parent corrected the first local proof to `by exact i.isLt` and unfolded
`P2` before the guard's `decide`. I reread those exact corrections and reran
`lake env lean Recaman/ShortPeriodicSupply.lean` on the final hash recorded
above: **exit status 0, empty output**. These repairs change neither theorem's
statement or the audited mathematical claim.

Also read the full module, obtained its SHA-256 with `shasum -a 256`, and
searched for forbidden proof escapes. None occurs in the audited module.
Only this audit file was written by the auditor. Parent should finish Audit
imports and full repository validation. No mathematical repair is requested.
