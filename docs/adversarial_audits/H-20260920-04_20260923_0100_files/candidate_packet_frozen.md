# H-20260920-04: 2026-09-23 01:00 candidate packet

## Conclusion first (independent audit pending)

The single frozen literal `SAAASSSASASASAAA` at period 16 is a candidate
counterexample to extending short-tight SS=2 donor avoidance from donor length
11 to a **nonminimal** donor window of length 15. It satisfies even positive
period mass, donor current-A, and Hall on its full finite supplied set. The
claimed true-oldest avoidance and the associated deletion Hall inequality both
fail for `B=[3]`. Proposed scope: stop only this nonminimal length-15
replacement. The author's recomputation and Lean acceptance are not an
independent audit, and this packet is not a new registry result.

## Frozen question, acceptance, stop

The proposed universal claim has `e : Int → Bool`, `p : Nat`, `0<p`,
`∀ x : Int, e (x+p)=e x`; a nodup list `B : List Nat`; `lag : Nat → Nat`;
`|N_e,p(B,lag)|=|B|`; every `b∈B` is `<p`, has `e b=true`, and has a P2 window
whose lag is 3, 7, or 11 (H-03 also allows nonminimal B windows); and a donor
`u0` whose length-15 past is P2 with `ssCount=2`. It imposes **no** donor
minimality. The avoidance conclusion is
`trueOldestPhase e p u0 15 ∉ neighborhood e p B lag`. The deletion form asserts
`B.length ≤ (deletedNeighborhood e p B lag (trueOldestPhase e p u0 15)).length`.
The donor's current sign, its exclusion from B, positive period mass, assumed
Hall, and an ambient full U are not required premises. We check all of these
stronger properties where applicable. An explicit literal meeting every
premise and negating avoidance is acceptance for a counterexample; one such
literal stops this exact extension. No repair or different donor hypothesis is
made in this slot.

`statement_signatures.txt` quotes the existing E-360 Q and the literal Lean
certificate verbatim. The latter is a concrete conjunction, not itself the
universal false extension. In particular, its explicit conjuncts do not say
`B.Nodup`, `B` minimal, or Hall; the independent literal checker verifies those
additional obligations. The actual `donorLength15Stream` definition is at
`Recaman/ShortTightDonorAvoidance.lean:643`; the certificate is at line 651.

## Premise to witness map

| Universal premise / conclusion | Literal check |
|---|---|
| `p>0`, periodicity | `p=16`; Lean certificate proves `∀ t : Int, e(t+16)=e t`. Python indexes the literal modulo 16. |
| `B.Nodup`, in range, current A | `B=[3]`, `3<16`, `e 3=A`. Donor `u0=15` is outside B and current A. |
| B lag, P2, minimality | `lag 3=3`; `past e 3 3=AAS`, P2 `(mass,moment)=(1,0)`; neither positive proper prefix 1 nor 2 is P2. |
| B tightness and local Hall | `N([3])=[0]`, so `|N|=|B|=1`; Hall also holds on `[]` and `[3]`. |
| Donor P2/SS2 | `past e 15 15=AASASASASSSAAAS`; mass 1, moment 0, overlapping SS count 2. |
| Donor nonminimality | Its positive proper P2 prefixes are exactly `[3]`; this invalidates donor minimality and no other stated premise. |
| True oldest phase | Largest 1-based S offset is 15, so `(15-15) mod 16=0`; this is an S at phase 0. Fixed offset 11 gives phase 4 and is **not** the true oldest. |
| Negated avoidance | `0∈N([3])=[0]`; the proposed `0∉N` is false. |
| Negated deletion Hall | `N([3])\{0}=∅`, so `1≤0` is false. |
| Stronger periodic controls | Period mass is 2. Finite full U at inclusive cutoff `p(p+1)=272` is `{1,3,11,15}` with least lags 11,3,39,3. All 16 of its subsets meet Hall. |

`check_literal.py` recomputes directly from the one string; it does not import
the discovery or prior verifier. The exact JSON stdout is `literal.stdout`.
The full-U test is an exhaustive finite test for this particular word with a
stated cutoff; calling it *full* also uses the existing E-181
`Recaman.PeriodicSupplyBound.supply_lag_bound`, which reduces any positive-mass
periodic P2 supply to lag `≤p(p+1)`. The period mass is 2 here. This is not an
all-period Hall theorem or new holdout. One literal
counterexample needs no separate discovery/holdout split; the old census
32768/85/46, the second w1 witness, and any optimality of p or lag are outside
this certification.

## Meaning and adversarial controls

The informal dependency chain for the proposed extension would be: tight
short B gives an owner family; short AAS/w1 structure constrains covering the
donor's oldest S; conclude noncoverage, then deletion Hall. The weakest new
edge beyond E-360 is the donor-cover classification at length 15 **without**
minimality. This literal refutes that edge because AAS at phase 3 covers the
oldest S of the nonminimal donor. The existing lag-11 Q and W remain as
registered; H-02/H-03's lag-11 nonminimal claims are not certified here.

The source statement mentions an actual periodic sign word and P2 windows,
not `a` or `stateAt`. It is an abstract periodic-sign countermodel, not a
Recamán orbit. `P2` expands to concrete mass and moment equalities; no defined
unproved `Prop`, self-implication, conclusion-equivalent premise, or free
arithmetic wrapper appears in the target question. The literal has nonempty B
and a current-A donor, so the antecedent is realizable. Changing the conclusion
to the fixed offset-11 phase would make this witness fail to refute it, but
that would change the intended true-oldest claim. Adding donor minimality would
exclude the witness; this is a different question and is not adopted as a
repair. Removing B minimality or ambient/full Hall cannot explain away the
collision, since the witness has both. The theorem's `decide` proof of concrete
equalities and the independent string recomputation are separate checks of
the same witness, not a new symbolic generalization.

Controls from the portfolio remain distinct: E-240 refutes pure-AAS forcing;
E-069 refutes global oldest-S injectivity; E-180 refutes the linear
collision-slack charge `slack≥c`, **not** donor deletion. The SS≥3 deletion
countermodel mentioned in earlier notes is a separate control; no ID is
assigned here without source verification. E-351's future-AAS premises are not
used to create this literal. A false offset can sometimes still pass Hall;
this packet uses the computed true offset and checks membership directly.

## Evidence and boundaries

HEAD is recorded in `run_metadata.json`; uncommitted source SHA-256 values,
argv, cwd, timeout, exit and stdout/stderr hashes are in `run_metadata.json`
and `commands.json`. Each `*.stdout` and `*.stderr` is the complete raw stream,
including empty stderr files. No random seed, no new range, no holdout. The
existing module-wide vacuity/lint classifications cover 21 declarations; they
are not a semantic verdict on this one symbol. The target symbol is separately
read in source, quoted verbatim, checked by Lean, and paired with the literal
recomputation. `./scripts/check.sh` and existing E-360 statement audit are
compared only for the registered baseline. No new G5 row is proposed.

Pending independent Sol attack and parent verdict: no registry or proof-map
promotion, no claim of minimum p/lag, no general T6, no all-lag capacity, no
actual-orbit conclusion. If the independent audit finds any unmet premise or
an incorrect phase/definition correspondence, leave H-04 at its preexisting
self-reported status without using this packet as established evidence.
