# H-20261117-OFP: formal audit of the old-floor area producer

Frozen 2026-11-17 21:59:20 JST before implementation (filesystem birth time; the initial rounded22:00 text was corrected before the repair). Status PROVED-PAPER for the formula in the main note; Lean implementation subsequently accepted as E736; see final outcome. This is a validation subunit of the M5 work, not a new M or a generalization-tracker reset.

Question: for every original f and bridge [s,s+K] ending at a minimum m, can the exact area envelope and parity used by the p<=2 old-source admission be derived from the original walk and A count, without assuming the envelope itself? All K, original heights and A counts remain unrestricted.

Let j=H(s)-m, r=A[s,s+K), C=Ar(s,K). Under H(s+K)=m and H(s+i)>=m for all i<=K, prove
`-j(j+1)/2+r(1-2j)<=C<=r^2-j(j+1)/2` and `(C-r+j(j+1)/2)%2=0`.
Dependency: telescope x(x-1) across every actual step -> exact area in terms of the sum of original A-start heights -> nonnegative and rank upper bounds on that sum -> envelope/parity. A p<=2 admission corollary may consume the actual original A count, but no raw admission premise.

Falsifier already preceded implementation: the frozen old-area-spectrum audit checked this exact potential identity on all nonnegative bridges in discovery j0..3/r0..2 and holdout j4..6/r0..3, including empty bridges and floor contacts. These are reused verification data, not a new holdout. The full paper derivation is in the main note section2. Dropping the floor destroys the lower bound; the new formal theorem must retain it. The all-three-contiguous classification and E729/E730 are outside this unit and stay PAPER.

Acceptance: original f/Fw/Ar/cN binders, no desired envelope/admission among assumptions, ordinary Lean proof, lint/vacuity/G5/Audit/full checks. Initial source and at most one cause-based repair are frozen separately. Same60CPU/90wall/-j1/-M512 cap as the accepted consumer; no resource/tactic/import/split-only revival after a cap. Hard stop22:25 JST, preserving >=20 minutes of audit and5 minutes publication before23:00. Failed code stays packet-only. A successful helper is formal validation, not another independent arbitrary-depth result.

## Result

E736 PROVED-LEAN: original_floor_area_spectrum proves the full all-K/all-r original floor envelope and parity; the exact walk identity and both A-height bounds are checked. One parser/normalization repair, accepted0.551CPU/0.709wall. Initial scripts/lakew launch failed before Lean because its toolchain path is absent; the established PATH lake ran identical source under the same cap. Both events retained. Module vacuity0FLAG/0unknown/5theorems. This is formal audit of the M5 producer, not separate generalization credit.
