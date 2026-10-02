# Independent entry audit: H-20261002-01

2026-10-02 JST. Separate explicitly authorized read-only research auditor `/root/issue81_auditor`. Base `8ee8588f1015955c2474674ba1656cb296f8157c`; branch `codex/ss2-lowss-tight-avoidance`. Repository sources and Git state were not modified.

## Verdict and exact scope

**PASS to formalize the stated bounded unit.** The all-length route is sound, with no additional conjecture or hidden Hall/OS premise. The weakest structural edge is the generic P2-suffix extension of E-366's AAS lemma. It supplies new real word content: the current-A endpoint of any low-SS P2 window cannot equal the true oldest S of a minimal SS2 donor, with no lag cutoff.

The final proposed statement concerns a positive-period sign stream, a nodup in-range list B of current-A P2 windows with SS≤1 and a tight concrete neighborhood. B windows need not be minimal. Donor length and member lengths are all unrestricted. The donor is minimal P2 with exactly two overlapping SS pairs; its current sign need not be A. The conclusion uses the existing actual `oldestOffset`, not full donor length.

The planned quantitative corollary is **one** extra subtraction beyond the injective low-SS image when at least one such donor exists. It does not supply one distinct phase per donor. General high-SS tight families, all-lag capacity, deletion Hall, orbit realization and protected claims remain outside this unit.

## Independent proof-chain challenge

Write Y=x++[A] and W=Y++v++A^n, with both W and v P2 and SS(W)≤2. Existing append equations give mass(Y)=−n and

`M(Y)+|Y|+(|Y|+|v|)*n+M(A^n)=0`.

SS(Y)≤2 is derived by append monotonicity. When n=0, mass(Y)=0 and M(Y)+|Y|=0. E-366's `ss2_intervening_prefix` derives prefix ceiling2 from actual suffix mass bounds and then derives a proper P2 prefix of Y via E-362. This prefix is proper in W. When n>0, `moment_ending_A_budget x 2` gives M(Y)+2|Y|≥3. Splitting n=1+m in the exact equation leaves only nonnegative additional terms, contradicting zero. No restriction on the literal content of v is used beyond P2. P2 also excludes an empty v, though the already proper prefix of Y suffices for properness in W.

The low-SS condition belongs to chronology: `oldest_cover_clock_lt` proves that a putative covering window ending at the donor's true oldest S has an earlier current clock; otherwise SS2 would be contained as a suffix of an SS≤1 word. `past_oldest_cover_decomposition` then supplies Y and v from the same actual stream. Donor minimality contradicts the generic suffix lemma. No assumption that the alleged cover is earlier is silently added to the final endpoint result.

For modular endpoint equality, shift the covering current clock by a multiple of p so its endpoint equals the actual integer oldest clock. Periodicity preserves the covering current-A, P2 and SS count. This uses no p/lag comparison and no positivity of period mass.

E-128 `stream_S_witness` shortens each actual low-SS window to a P2 prefix of length f with 0<f≤lag, SS≤1 and actual S endpoint. Consequently normalization works even for nonminimal or A-ended original member windows. `endpoint_mod_injective` gives an injective map from B into subtraction phases. Crucially its image lies in **the original N(B)** because f≤lag. The image is nodup and has |B| entries; tightness and neighborhood nodup imply it equals N(B). This is a derived equality for the low-SS class, not an assumed general oldest-S ownership theorem. Endpoint disjointness therefore implies the required neighborhood avoidance.

For the strict-slack corollary, append the donor's oldest phase to the injective normalized endpoint image. Endpoint disjointness ensures distinctness. An additional explicit implementation obligation is to prove the recursive oldestOffset is positive and actually selects S for an arbitrary P2 donor, so the appended phase belongs to D. Existing generic tail splitting alone is not this fact, and lag11/#82-specific oldest-bit certificates do not cover arbitrary donors. A direct recursion or P2 terminal decomposition can supply this edge. No novel conjecture is needed.

## Existing-source and novelty audit

I inspected `LowSSEndpoint` and `LowSSPeriodicSupply` signatures. E-128 provides precisely same-history S-prefix normalization and all-length modular endpoint injection without member minimality, NoSAAS or positive drift. It proves non-strict capacity but no disjoint extra SS2 phase or all-length tight avoidance.

`LowSSTwoSSJointCapacity.ss_le1_two_endpoint_mod_disjoint` additionally restricts zero-SS suppliers to lag3 and the SS2 side to lag<15. Its joint capacity theorem assumes the selected full endpoints are S. It does not use arbitrary true oldest S of a minimal SS2 donor. Thus the present statement is not a wrapper of that old restricted capacity result. E-366 limits B to lags3/7/11; the proposed low-SS class removes that cutoff. Do not register the finite-cardinality helper as the advance: the generic prefix contradiction and arbitrary-lag endpoint disjointness are the substantive edge.

## Frozen falsification evidence

The three frozen hashes match exactly: new script `ss2_lowss_tight.py`, its imported `ss2_short_tight.py`, and `protocol.frozen.md`. Source base and JSON base match 8ee8588. Discovery lengths3/7/11/15/19 and holdout23 are explicitly reused, not fresh data.

Independent command `python3 /tmp/LowSSTightEntryIndependent.py` uses integer prefix sums to compute suffix mass and shifted moment, rather than importing either experiment's data/cover routine. It reproduces all P2 counts (1,4,29,263,2724,30554), minimal SS2 counts (0,0,7,46,216,647), terminal-tail counts, and current-A candidate counts (0,0,38,355,2124,7689). Across 916 donors and 10,206 current-A suffix candidates there are zero low-SS endpoint violations. The same fixed-range scan also found zero P2 earlier suffix covers of any SS count, as predicted by the generic structural lemma. Output: `/tmp/LowSSTightEntryIndependent.json`.

The extra check of the generic earlier-cover statement is an independent audit control within the same fixed ranges, not a retroactive change to the frozen experiment. Computation remains COMPUTED, not the all-length proof.

The predeclared donor-minimality negative control has proper P2 prefix3 and shares its oldest endpoint with AAS. Dropping donor SS2 admits `AAASSSSAAAS` (SS3), whose current-offset8 AAS ends at its oldest S. The same donor as its own endpoint cover refutes removing the cover low-SS condition from the **intermediate endpoint theorem**; it is not by itself a counterexample to the final tight-neighborhood theorem. The p17 w1 singleton from E-366's audit is the appropriate no-tightness countermodel to the final claim.

Neither frozen range contains an earlier current-S low-SS covering suffix of a minimal SS2 donor; my independent scan agrees. Therefore the experiment has not established covering-current-A necessity for this new endpoint statement. State that absence honestly; do not conflate it with E-128's separate current-A counterexample or expand the census to force one.

## Nonvacuity and longer-member control

I independently verified the card's fixed concatenation construction: period36 stream `SASASASSAAAASASASASASASSAAASSAAASASA`. At current15, lag15 gives `SASAAAASSASASAS`, a minimal SS1 P2 word, with endpoint phase0. At current35, lag19 gives `SASAAASSAAASSASASAS`, a minimal SS2 P2 donor, with true oldest phase16. Both current signs are A; there are16 subtraction phases. Thus endpoint and one-unit-slack statements have an explicit nonempty longer-than11 instance. Recorded in `/tmp/LowSSTightLongMemberControl.json`.

The singleton U=[15] in that construction is **not tight**: its original neighborhood has seven phases. Use it for endpoint/strict-slack kernel applications, not to claim the tight-avoidance theorem's hypotheses are satisfied. A separate already established p18 nonempty tight example with w1 members provides the positive tightness control. Final source audit should also test a nonminimal low-SS member to verify the advertised normalization scope is not lost.

## Continuation gate

Proceed to one substantive module with the generic prefix lemma, exact integer/modular endpoint theorem, normalized low-SS tight avoidance, and one-donor slack consequence. Keep all exact hypotheses/quantifiers. Stop if a cutoff, unknown owner/distance statement, generic Hall, or unproved S-ended assumption is required, or if the bounded route gate expires without a complete proof chain. Final acceptance still needs independent binder/RWCT/source audit, theorem-applied kernel controls, G5/Audit and full repository checks.
