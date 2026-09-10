# Hypothesis card: unbounded demand at a single SS defect

- ID: `H-20260910-23`
- Status: `PROVED-LEAN` (E-122), with canonical measurement `COMPUTED` (E-123)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Four roles sequential.

## Exact bounded question

The H22 family A subfamily j=k+1,z=k+2,n=4k+3 is
`W_k=(SA)^k SAAAASS (AS)^(3k)`.
For EVERY K, does one finite sign history contain K+1 distinct current-A
positions whose minimum P2 windows are W_0,...,W_K, all crossing the SAME
unique SS pair? If yes, no bounded number of slots at an SS pair can pay
for all such supply events, even with no SAAS and only one A gap4.

Acceptance: exact construction/embedding/P2/current-A/unique-SS in Lean;
minimum-lag and NoSAAS may use the complete paper classification with their
scope explicitly labeled. Do not claim canonical reachability of this
all-K family. Stop if windows use different SS pairs or some current sign
is S. This is a countermodel to defect-local capacity, not to E-070.

## Dependency chain before Lean

W_k has mass1 and moment0: the SA prefix contributes k, the core contributes0
and acquires a2k offset, and the AS tail contributes−3k. Also
`W_K=(SA)^(K−k) W_k (AS)^(3(K−k))`.
In the common newest-first history `A W_K`, source positions2(K−k) are A;
window starts immediately after them. Every W_k has its SS pair at local
positions2k+5,2k+6 (zero-based), hence common absolute history positions
2K+6,2K+7. H22 gives minimum lag8k+7 and NoSAAS.

## Frozen falsifier

Build W_k directly for k0..32 discovery,k33..256 holdout; independently
scan ALL P2 prefixes and verify SS1/NoSAAS. Embed all k≤K for K0..32
and K64,128,256, checking distinct current A positions and the exact common
SS location. An unrestricted infinite-history toy is not used.
A separate actual-orbit measurement may be added only with a frozen
protocol; the construction itself is a finite weakened-history countermodel.

## Evidence

- `COMPUTED`: every frozen window and common-history embedding passed; `one_ss_multiplicity.txt`.
- `PROVED-LEAN`: `OneSSMultiplicity` directly proves all-k minimum P2 (every proper prefix), NoSAAS, exactly one SS pair, shared SS coordinates, K+1 distinct current-A positions, and the common finite-history embeddings. These facts no longer rely on paper-only minimality.
- `unbounded_SS_demand` exceeds any proposed constant demand budget per SS pair. The word still has4k+3 S signs: this is NOT a counterexample to total S capacity E-070.
- Full `./scripts/check.sh`: PASS,1,560 audited declarations; `check23_one_ss_multiplicity.txt`.
- `COMPUTED` canonical addendum: through10^7,70,375 one-SS minimal P2 windows, all family A in that range, across546 SS pairs. The maximum is2,796 supplied A times using pair9,337,064/9,337,065; sources9,342,711..9,348,301 with lags5,647..28,007. Exact lists and histogram: `orbit_one_ss_census.txt`.
- The canonical all-k claim is not proved. The zero family-B count was tested separately and later overturned in H25; do not promote the10^7 absence to an exclusion.

## Frozen canonical census addendum (before execution)

Measure the actual10,000,000-step prefix, with discovery1..100,000 and
holdout continuations100,001..1,000,000 and1,000,001..10,000,000.
Use the already independently verified exact prefix-key minimum-P2 lookup.
For each SS1 minimum window, verify the H22 A/B equations using cumulative
S counts and the unique internal A3/A4 run. Count supplied A positions per
actual SS pair, and report the maximum with exact source times and lags.
No finite threshold is claimed to extrapolate; this is a new statistic on
the same deterministic trajectory, not independent trajectory samples.
