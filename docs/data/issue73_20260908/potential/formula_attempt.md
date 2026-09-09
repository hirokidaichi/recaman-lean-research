# H-20260908-02 handoff: closed-form all-L potential

- Unit: `H-20260908-02`
- Role: proposer / falsifier
- Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`
- Date: 2026-09-08
- Status of this formula class: `STOPPED`
- Parent existence claim (some F, some class): still `CONJECTURED`

## Conclusion

No closed-form or uniformly inductive potential F, independent of L, survived
falsification. The only candidate that recovered the known least potentials on
L=3 and L=7 — the Lean L=7 potential of the newest 7 bits — is invalid at L=11
on every lag-11-only supplied A-edge. The one permitted repair (add a +1 boost
when the newest 11 bits extend a Lean-P=2 7-bit shape) fails both those same
A-edges and 96 S-edges that drop the boost and the 7-bit value at once.

Horizon extension is not acceptance. L=23 was not used as a coefficient source
and is not an E-070 certificate; the log at
`docs/data/issue73_20260908/potential/L23.txt` already shows a crashed run.

This unit does not refute E-070. It stops the formula class of short-window
embeddings of a fixed Lean potential, plus a local longer-AAA boost.

## Evidence label

`STOPPED` for this formula class.

Supporting checks below are `COMPUTED` (exact finite windows, frozen L=3,7,11
payloads, and L=15,19 all-A / max-P / max-future-harvest reads). None is a
theorem. E-075 remains `REFUTED` and was not reused.

## Exact F if any

None. No F is claimed.

The frozen proposal, before L=11, was:

```text
F_embed7(w) = Lean7(newest 7 bits of w),
padding oldest bits by S if |w|<7, ignoring bits older than 7 if |w|>7.

Lean7(m) = 2 if m ∈ {55,63,95,111,119,127}
         = 1 if m ∈ {7,15,23,31,39,47,59,61,62,71,79,87,91,93,94,103,110,123,125,126}
         = 0 otherwise
```

Newest = LSB, A=1, same encoding as `Recaman/ShortPeriodicSupply.potential`.
On L=3 (pad) and L=7 this equals the least automaton potential, all edges tight
or slack-nonnegative. It is not valid for L=11.

## Failed formulae with counter-windows

Windows are newest-first. Charge is +1 on a P2-supplied A (any lag ≤ L), 0 on
an unsupplied A, −1 on S. Validity is `F(s)+charge ≤ F(advance(s,b))`.

### 1. Number of P2 hits already in the window

`REFUTED` as a formula for P, already in `decode.txt`. L=7 counter-windows:

- `AAAAAAA` has 0 P2 hits and P=2
- `AASAAAA` has 1 P2 hit (lag 3) and P=1

P is not a function of the in-window hit count.

### 2. All-A future-debt `F_L` (E-075)

Do not reuse. Independently, the dual `P = C − F_L` is false because `P+F_L` is
not constant: L=7 `AAAAASS` has P=1 and `F_7=0`; `AAAAAAA` has P=2 and `F_7=0`.
Max all-A harvest from any seed is strictly below max P once L≥11:

| L | max P = P(all-A) | max F_L (all-A future supplies) |
|---|---:|---:|
| 3 | 1 | 1 |
| 7 | 2 | 2 |
| 11 | 3 | 2 |
| 15 | 4 | 3 |
| 19 | 4 | 3 |

So the extra unit of P at L≥11 is not realised by any all-A continuation.
Canonical L=11 witness for P=3 uses an intermediate S: from `AASSSSAAASS`
(P=0) the word `AASAAA` harvests lags 3,11, then S, then 7,3 and ends at
`AAASAAAASSS` with net 3.

### 3. Newest A-run height, including modulo 4 / loop-closing `SAAA`

`F = floor((r+1)/4)` with r = newest A-run. L=7 `AAASAAA` has r=3 so F=1 but
P=2. Any F that vanishes on a newest S also fails the S-edge
`AAAAAAA --S--> SAAAAAA` once F(all-A)≥2, because the least potential has
P(`SAAAAAA`)=1.

L=19 kills the length-only stacking `F(A^L)=(L+1)/4`: that predicts 5, but
P(A^19)=4 (`COMPUTED`).

### 4. Replay / prefix-height / in-window P2 packing from the zero (all-S) seed

L=7 mismatches against the least potential: replay 25/128, max prefix-height
34/128, in-window supplied-A count 29/128. `AAAAAAA` replays to height 1, not 2.
A mixed prehistory is required already at L=7 (seeds `ASAASAS` and `SAAAASS`,
each lag-7 supplied, then a lag-3 supplied A).

### 5. Max k with newest 4k−1 bits AAA and at most k−1 S, all at positions ≥4
(`F1`)

L=7: 15/128 mismatches. Counter-windows include `AAAAASS` (F1=2, P=1) and
`AASAAAA` (F1=0, P=1). The min-gap repair `F1b` has 20/128 mismatches.

### 6. Proposal `F_embed7` — newest 7 bits of Lean L=7 potential

- L=3 exhaustive: 0 failures, equals least P (8/8).
- L=7 exhaustive: 0 failures, equals least P (128/128).
- L=11 exhaustive: 0 S-failures, **15 A-failures**, all lag = [11] only.

The 15 counter-windows (F does not rise on a supplied A):

```text
 1 SSAAAAAASSS --A--> ASSAAAAAASS  F 0→0  P 0→1  lags=[11]
 2 SASAAAASASS --A--> ASASAAAASAS  F 0→0  P 0→1  lags=[11]
 3 SAASAASAASS --A--> ASAASAASAAS  F 0→0  P 0→1  lags=[11]
 4 ASSAAASAASS --A--> AASSAAASAAS  F 0→0  P 0→1  lags=[11]
 5 SAAASSAAASS --A--> ASAAASSAAAS  F 0→0  P 0→1  lags=[11]
 6 ASASASAAASS --A--> AASASASAAAS  F 0→0  P 0→1  lags=[11]
 7 SAASAAASSAS --A--> ASAASAAASSA  F 0→0  P 0→1  lags=[11]
 8 ASSAAAASSAS --A--> AASSAAAASSA  F 0→0  P 0→1  lags=[11]
 9 ASASAASASAS --A--> AASASAASASA  F 0→0  P 0→1  lags=[11]
10 ASAASSAASAS --A--> AASAASSAASA  F 0→0  P 0→1  lags=[11]
11 AAASSSSAAAS --A--> AAAASSSSAAA  F 1→1  P 1→2  lags=[11]
12 SAAASAASSSA --A--> ASAAASAASSS  F 1→1  P 0→1  lags=[11]
13 ASASAAASSSA --A--> AASASAAASSS  F 0→0  P 0→1  lags=[11]
14 AAASSSASASA --A--> AAAASSSASAS  F 1→1  P 1→2  lags=[11]
15 AAASSASSSAA --A--> AAAASSASSSA  F 1→1  P 1→2  lags=[11]
```

Row 12 is the already-known newest-first word `SAAASAASSSA` (E-069 / endpoint
no-go), here used only as an embed7 inequality counterexample.

### 7. One repair: `F_embed7(w) + 1` if newest 11 bits have AAA and Lean7=2

Intended to pay for nested lag-11 harvest on A-heavy windows.

- L=3,7: still valid (boost never fires).
- L=11: **96 S-failures and the same 15 A-failures**.

S-counter-window (drop by 2, boost and 7-bit value lost together):

```text
AAASAASSSSS --S--> SAAASAASSSS  F 3→1
```

The 15 lag-11-only precursors are not AAA/Lean7=2, so the boost never applies
to the edges that killed the proposal. A leading-S variant of the same boost
has the same 111 failures and is not a second repair.

## Combinatorial picture (not a formula)

`COMPUTED` observations that any later F must respect:

1. Overlapping, not edge-disjoint, P2 contacts. L=7 max P=2 is a lag-7 contact
   immediately followed by a lag-3 contact sharing S-support
   (`ASAASAS -A-> AASAASA -A-> AAASAAS`). Disjoint packing is too weak: it
   cannot force F to rise twice without an S, so it fails the same A-edges
   `F_embed7` gets right at L=7.
2. A catalytic S is required for P=3 at L=11. All-A harvest caps at 2; the
   witness word `AASAAA` from `AASSSSAAASS` inserts one S between two harvest
   pairs. Future-debt and “A-run modulo SAAA” both miss this.
3. No max-P state is supplied (else an A-self-extension would demand maxP+1).
   L=7 max-P windows: `AAAAAAA, AAAAAAS, AAAAASA, AAAASAA, AAASAAA, AAASAAS`.
4. P(all-A)=maxP plateaus at 4 on L=15 and L=19. That is a hint, not a bound
   for all L, and not a closed form.

The prize interpretation “max number of edge-disjoint pending contacts” is
therefore `REFUTED` as a reading of P. “Height of an A-run modulo a loop-closing
word” is `REFUTED` as F. What remains is overlapping nested P2 harvest with
occasional catalytic S, which is currently only the automaton itself.

## Commands, sources, hashes

```sh
python3 experiments/issue73_20260908/potential_formula.py
python3 experiments/issue73_20260908/potential_witness.py
python3 experiments/issue73_20260908/potential_falsify.py
python3 experiments/issue73_20260908/potential_list_embed7_fails.py
```

- revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`
- `potential_formula.py` SHA-256 `e92388f6515f1ba4170111fe57eb776febdbe2ea8b8c7ac7633fc3466b514268`
- `potential_witness.py` SHA-256 `7655e4f6a9b0bae9afdba32ac2a488f164ec7332bd6279cb13b88ac145169bf6`
- `potential_falsify.py` SHA-256 `cf1331d851852a34ada2249b9ba7b9aef15e884d7abb7549e9eb920773a1ed20`
- `potential_list_embed7_fails.py` SHA-256 `b41981c15870b3a97b541311a4ae7d36e8cb63e18237cb91abbaa3d1a6dfe67e`
- frozen potentials: `docs/data/issue73_20260907/automaton_L{3,7,11,15,19}_potential.txt.gz`
  (L=7 matches Lean; L1 distance 0, already in `decode.txt`)

No Lean, Audit, registry, frontier, ROADMAP, or `recaman-visualizer/` edits.
L=23 was read, not killed, not restarted.

## Remaining uncertainty

- Existence of some other F, in a different class, is open. The least
  potentials P_L still exist for L∈{3,7,11,15,19} (`COMPUTED`, E-077) and
  prove |U_L|≤|D| at those caps only.
- Whether max P_L is bounded by 4 for all L is unknown. L=19 is a plateau, not
  a theorem. L=23 did not produce a potential: `automaton_Ln.py` emptied its
  queue and then failed the A-edge assertion after one progress line
  (`max_potential: 3`). That is an incomplete run, not a positive cycle and
  not a no-cycle certificate.
- The 15 L=11 embed7 failures are exactly the lag-11-only supplies. A uniform
  rule that scores every d≡3 (mod 4) with a nesting law might exist; it was
  not found in one proposal plus one repair.

## Next decision

**Stop this formula class.** Do not add another finite vector (L=11 table, L=15
table, or L=23). Do not treat a larger horizon as progress.

Reopen only if a new structural statistic is named that, on the 15 windows
above, raises F on the lag-11 A-step, and on `AAASAASSSSS` (and the six L=7
max-P windows) drops F by at most 1 on S — without encoding P_L itself. The
statistic must be tested first on L=3 and L=7 exhaustively, then on those 15
L=11 edges, before any new L.
