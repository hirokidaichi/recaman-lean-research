# Hypothesis card: common-endpoint rigidity and joint low-SS capacity

- ID: `H-20260910-28`
- Owner: Codex, proposer/falsifier/formalizer/auditor performed sequentially.
- Created: 2026-09-10, one-hour continuation starting 09:15 UTC.
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa` with the existing
  September 9–10 research working tree. Initial diff and status retained
  in `/tmp/recaman-hour-20260910/` during the run.
- Status: `PROVED-LEAN` (E-128); direct two-SS normalization extension `REFUTED` (E-130).
- Inherited working tree preserved as commit `2ed8606dc5948bb05ac7547acc6065b36a10bfb7`.

## Exact bounded question

For every two-sided sign stream e, two current A sources t,u with P2
windows of lengths d,f, each containing at most one adjacent SS, cannot
share the oldest position unless t=u. No periodicity, minimum-lag,
NoSAAS, canonical reachability, or drift premise is proposed for this
rigidity lemma.

Consequently, for every positive period p and every finite set U of its A
phases, if every member has a P2 window with SS count at most one whose
oldest sign is S, then |U| is at most the number of S phases. All lags and
all signs of the period mass are included.

The initial application was the **joint** class of clean and one-SS
minimum windows in NoSAAS streams. The existing paper classifications
E-109/E-121 say these windows end S. The original acceptance gate required proving this inclusion in Lean or explicitly retaining the paper dependency.
The final theorem proves a stronger inclusion: every P2 window with at most
one SS has an S-ended P2 prefix, without NoSAAS or minimality. Thus the
final capacity theorem has no end-S premise and uses no paper classification.

## Why it would matter

E-069 already refuted the unrestricted oldest-S map at period12 SSSSAAAASAAA;
its colliding lag11 window has three SS and is outside this claim. E-073
already refuted unrestricted minimum S-ending with SAAASAASSSA (two SS).
These stopped branches are retained as negative controls, not silently reopened.
E-127 gives only the one-SS class capacity, and its preceding-run S map
collides with the clean map for every family B. One shared endpoint map
would give actual union capacity. It is not a new offset table, a
constant budget per SS, or the full E-070 conjecture.

## Dependency chain before formalization

1. Every nonempty word ending A has mass at least minus its SS count
   (pair each S with the following A, leaving only SS defects).
2. If that count is at most one, all nonempty suffixes have mass at least
   -1; the final A gives `moment(word)+length(word) >= 2`.
3. Shared endpoints give a decomposition newerWindow = v ++ olderWindow.
   The old source is A, so the nonempty v ends A. Both P2 identities force
   `mass(v)=0` and `moment(v)=-length(v)`, contradicting step 2.
4. Lift equal endpoint residues in a periodic stream to equal integer
   endpoints; obtain an injection into the S phases.
5. Audit the original clean/SS1 minimum class against the end-S premise.

Step 2 is the weakest new lemma changing the overlap frontier. It has a
complete informal argument independent of the paper two-family theorem.

## Falsification plan and stopping condition

- Exploratory discovery: NoSAAS binary periods 1..18, direct P2 moment
  scan, no endpoint collisions and no joint capacity violations.
- Frozen independent C++ protocol: all binary periods 1..13 discovery,
  14..22 holdout, all mass signs, including words with SAAS. Scan all
  S-ended low-SS witnesses and test the endpoint map, not just a maximum
  matching or one chosen lag.
- Also test finite common-history words, boundaries, the existing
  centered-map controls, and dropped-current-A / two-SS controls.
- Record source hashes, command, revision, parameters, and exact output.
- Stop the endpoint claim at the first actual counterexample. At most one
  repair, justified by the failed premise. Do not switch to arbitrary
  offsets or extend lag tables. Leave unproved classification implications
  at `PROVED-PAPER`; computation is never the proof.

## Evidence log

- Initial `./scripts/check.sh`: 1,583 audited declarations, passed.
- `COMPUTED`: frozen C++ periodic scan, all 8,388,606 binary periods1..22,
  13,594,274 S-ended witnesses, violations0; SAAS allowed, all mass signs.
  The exact source hash and command are in `endpoint/periodic_falsifier.txt`.
- New informal strengthening before its Lean implementation: the final-pair
  induction gives an S-ended P2 prefix. Zero SS/nonpositive moment is the
  base lemma; an A-ended one-SS word either ends AA (positive moment) or SA.
  In the latter case recurse, or the boundary uses the unique SS and leaves
  a zero-SS prefix. This removes both the end-S assumption and paper dependency.
- `PROVED-LEAN`: `LowSSEndpoint`, `LowSSPeriodicSupply`; full repository
  check and audit: 1,617 declarations. Main theorem:
  `Recaman.LowSSPeriodicSupply.periodic_lowSS_capacity`.
- `COMPUTED`: independent finite-word semantic regression through length19,
  1,048,575 words, no violation. This is not a relabeled holdout.
- `COMPUTED`: standard10^7 replay, 992,184 low-SS supplied A, all endpoints S
  and pairwise distinct. Prior replay counts and checkpoints match. The
  75.39988% is a finite P2 diagnostic, not a theorem about infinite coverage.
- `REFUTED`, kernel-certified: canonical step115 has minimum lag11 word
  AAASSSASASA, two SS, NoSAAS, old endpoint A, and no S-ended P2 prefix.
  E-130 strengthens E-073 to actual canonical reachability.
- Inherited proof/data bundle: baseline2ed8606, 495 manifest entries and
  47 logged source identities verified before root/audit changes.

## Semantic audit

The rigidity conclusion alone does not ensure the endpoint is S. A word
such as AASASSA is P2, has one SS, and ends A; its shorter prefix AAS is
P2. This prompted the explicit prefix-normalization proof: the original witness
need not end S, but an S-ended prefix can be selected. No minimum-lag or
NoSAAS premise remains. The endpoint theorem retains current-A and the
SS-count bound, with explicit negative controls for both. The current-A
control refutes the endpoint rule, not every conceivable broader capacity rule.

The new class adds70,208 standard finite sources beyond old U≤11/clean but
misses7 old short sources. Do not claim it contains the old theorem or add
their capacities. Periodic lifting handles negative integer endpoints and
arbitrarily wrapped windows; Nat subtraction is not used for sign times.

## Decision

Complete the H-28 unit and commit/push the audited result. Stop direct
extension of the S-ended-prefix method to two SS: even canonical NoSAAS
fails at step115. A new common-history allocation inequality for SS≥2 is
required before continuing; no offset tables or lag extensions.
E-067/E-070, union with old short capacity, and both surjectivity alternatives
stay open. Detailed proof and evidence: `LOW_SS_ENDPOINT_CAPACITY_2026-09-10.md`.
