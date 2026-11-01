# Hypothesis card: can a long A run force nesting of minimal supplies?

- ID: `H-20260909-07`
- Owner: Codex, four roles sequentially
- Created: 2026-09-09, within the one-hour research run
- Status: `REFUTED`; arbitrary-r counterfamily `PROVED-PAPER`, r=2 `PROVED-LEAN`
- Base revision: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Bounded question and stop

If a newest-first word w has at least m≥3 leading A signs and its first
P2 prefix is w itself, must every P2 prefix of A++w have length>|w|+4?
This asks whether H-05's containment assumption can be removed even for
one added A and minimal supply. No period or orbit assumption is present.
Stop on a counterexample; do not raise the minimum run length as a repair.

The intended positive consequence would be a monotone lag across an A run.
The earlier proofs do not provide it: they explicitly require containment.

## Falsifier and candidate counterfamily, fixed before execution

Analytic construction suggests the following family. For r≥2 let m=r²−1,
let V be sharpFamily(m+1) with its first A removed, and set

```text
T = A^(2r) S A S^(2r−1),     w = V T.
```

Predictions to check: w is minimal P2 of length 4r²+4r−1 with leading run m;
A++w has minimal P2 prefix sharpFamily(m+1), of length 4r²−1. Thus one A
reduces the minimum lag by 4r despite an arbitrarily long initial A run.

- Discovery r=2..8; holdout r=9..64, using every prefix and exact moments.
- Weakened history is the full arbitrary-sign model; no freshness is assumed.
- Boundary r=1 is excluded; m=0 would not test the stated conjecture.
- Acceptance: exact finite counterexample to the conjecture, plus a complete
  paper proof if claiming the arbitrary-r family. Finite tests cannot supply r's quantifier.
- Source identity and exact outputs must be frozen. No parameter search after a failure.

## Evidence and decision

### Counterexample and complete counterfamily argument

For r=2, the newest-first word is `AAASSSASSSSAAAAAAASASSS`.
Its first P2 lag is 23 and its leading run is 3. Prepending A gives
first P2 lag 15. `nonnested_lag_drop_certificate` checks both moments,
all shorter prefixes at both times, and the leading A prefix in Lean.
Its axiom report is empty. This is a counterexample to the proposed
nesting/monotonicity claim, not to periodic capacity E-070.

For every r≥2, m=r²−1≥3. Put n=|V|=4m+2. Removing the leading A from
the P2 word sharpFamily(m+1) gives mass(V)=0 and moment(V)=−1.
The tail T has mass 1. Moving the last A of A^(2r+1) S^(2r) one place
right gives T, so its moment is

```text
(2r+1)(2−(2r+1))+2 = 3−4r² = −4m−1.
```

Therefore mass(VT)=1 and moment(VT)=−1+n−4m−1=0. Its length is
`4m+2+4r+1=4r²+4r−1`.

To prove minimality, consider a P2 prefix of w of length d≤n. For d<m
it is all-A, hence impossible. For d≥m, H-03 gives d≥4m−1. The P2
parity equations give d≡3 (mod 4), leaving only d=4m−1 in this range.
But V ends in at least three A signs, so that prefix has mass −3,
not 1. For prefixes extending into T, the tail's signed sum first
equals 1 at its first A, and next equals 1 only at its final S:
the intermediate minimum after the isolated S is 2r−1≥3. At the
first A the whole prefix moment is −1+(n+1)=n>0. Thus the only P2
prefix of w is its whole length.

After prepending A, the first 4m+3 signs are sharpFamily(m+1), whose
minimality is already proved uniformly in H-03. The minimum lag drops
by 4r. Both the initial run r²−1 and the drop 4r are unbounded.
This is a complete paper proof, not an extrapolation from r≤64.

The family also embeds in a **positive-sum periodic** sign model. Put w
at times −|w|,...,−1, choose A at times 0 and 1, and periodically repeat
this block of length p=|w|+2=4r²+4r+1. It has signed sum 3. None of the
tested prefixes wraps across this block's boundary, so the same minimal
lags hold at both A phases. Thus positive periodicity does not repair
the nesting claim either; actual Recamán reachability is still absent.

Before the additional periodic replay: verify this embedding for discovery
r=2..8 and holdout r=9..64, reconstructing signs through modular indices
and checking every prefix through one full period at t=0 and t=1.
This is a new deterministic audit of the derived embedding, not a new
search or a revised conjecture.

Final scope control, fixed to r=2 only: use the repository's existing
all-lag periodic formula and its independent direct replay to count the
supplied A phases of this 25-phase embedding. This prevents confusing
the minimal-lag counterexample with an all-lag capacity counterexample.
No period or r search is authorized by this control.

### Evidence and decision

`COMPUTED`: all prefixes pass for discovery r=2..8 and holdout r=9..64.
The last case has leading run 4,095 and minimum lag 16,639→16,383.
The family was analytically proposed before this replay; discovery is
a parameter split, not a claim of blinded validation.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/nonnested_lag_drop.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/verify_nonnested_periodic.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/verify_lag_drop_scope.py
./scripts/check.sh
```

Exact output: [nonnested_lag_drop.txt](data/issue73_20260909/nonnested_lag_drop.txt).
Independent periodic output: [nonnested_periodic_verify.txt](data/issue73_20260909/nonnested_periodic_verify.txt),
with the same discovery/holdout split and zero embedding failures.
The [r=2 scope control](data/issue73_20260909/lag_drop_scope_control.txt)
finds 5 supplied A phases, 14 A phases and 11 S phases; the existing all-lag
formula agrees with direct replay. This particular periodic word violates
neither E-067 nor E-070. No such all-r capacity conclusion is inferred.
The r=2 certificate is in the full 1,265-declaration audit. The general
minimality proof remains paper-only. **Decision: stop the monotone-lag
route, including attempts to repair it merely by requiring a longer A run.
Future overlap arguments must preserve containment or explicitly handle
the short-window resets exhibited by this family.**
