# Issue 73: S-inventory for supplied-A F-descent

- Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`.
- Owner: independent geometry/inventory worker; no Lean, Audit, registry,
  frontier, ROADMAP, or `recaman-visualizer/` edits.
- Four roles sequential: proposer → falsifier → paper formalizer → auditor.
- LoopClosingSubtraction restatements are not used as input.

## Bounded question (frozen)

The paper identity `F_a + F_j - 2 F_s = -R + λ(d-1) < 0` for `λ≤0` gives a
two-child descent at every supplied A, but the descent can sink at an S phase
where no matching two-child inequality exists. Is there a single new
S-inventory inequality, with exact quantifiers, that makes every S pay for
incoming supplied-A descents and implies `|U|≤|D|`? If you propose one,
falsify it on `SAAA`, `SSSSAAAASAAA`, `AAASSASSSAA`, the escape family
`A^5 S^4 (AS)^8`, and all-A / all-S before any census. One repair only.
Stop on a counterword to the inequality (that is a stop of this inventory,
not of E-067 unless the word also has `U=A`).

Acceptance: `PROVED-PAPER` inequality, or `REFUTED` inequality with exact
word, or `STOPPED` class.

## Conclusion

**This inventory class is `STOPPED`. The two-child S-descent injection is
`REFUTED`. Its one permitted repair, charging every lower-κ S in the least
P2 window together with the actual next phase, is also `REFUTED`. Neither
counterword has `U=A`.**

The 2026-09-07 identity at a supplied A-phase `s`, with actual next phase
`a=s+1` and least-P2 supplier `j=s-d`, remains `PROVED-PAPER` and was
recomputed on every test word:

```text
u_a − u_s = R−1,     u_j − u_s = d−R,     κ_a + κ_j − 2κ_s = −R,
F := κ + λu  (λ≤0)   ⇒   F_a + F_j − 2F_s = −R + λ(d−1) < 0.
```

That identity does not by itself produce an S-payment rule. The unique
κ-minimum can be an S, as already recorded on `SSASAAA`, and two distinct
supplied A-phases can have that same S as their only payable descent child.

## Exact attempted inequality I_inv

Quantifiers: for every integer `p≥1` and every cyclic word
`ε: ℤ/pℤ → {+1,−1}` with period sum `Σ = ∑_r ε_r > 0`, write

```text
D = {r : ε_r = −1},
A = {r : ε_r = +1},
U = {t ∈ A : some d≥1 satisfies P2 at t},
```

and for each `t∈U` let `d_t` be the least P2 lag, `a_t = t+1`,
`j_t = t−d_t` (indices mod `p`). Let `κ` be the phase invariant of the
periodic formal-value path (`λ=0`, so `F=κ`).

**I_inv.** There exists an injection `φ: U → D` such that for every
`t∈U`,

```text
φ(t) ∈ {a_t, j_t} ∩ D     and     κ_{φ(t)} < κ_t.
```

If true, `|U|≤|D|`. The paper identity already forces `min(κ_a, κ_j) < κ_t`;
I_inv additionally requires that some strictly lower child is an S-phase
and that those S-phases can be chosen injectively. This is not a lag-by-lag
gap-type matching, not an oldest-S map, and not an all-A future-debt bound.

`λ<0` is not part of I_inv. On the frozen escape word it already destroys
existence of an S-child in `{a,j}` at the `d=3` supply (see below), so the
only remaining candidate in the `λ≤0` family is `F=κ`.

## Frozen-list check, before any census

Words are forward cyclic, phase 0 = first letter. All-A and all-S are
vacuous: `U=∅`. Identities were checked with exact rationals.

| word | `p` | `Σ` | `U` | `|D|` | I_inv |
|---|---|---|---|---|---|
| `SAAA` | 4 | 2 | `{3}` `d=3`, `a=j=0` | 1 | holds, `φ(3)=0` |
| `SSSSAAAASAAA` | 12 | 2 | `{6,7,9,11}` | 5 | holds, `φ=(6↦3,7↦8,9↦2,11↦0)` |
| `AAASSASSSAA` | 11 | 1 | `{0,5}` | 5 | holds, `φ=(0↦8,5↦4)` |
| `A^5 S^4 (AS)^8` | 25 | 1 | `{0,2}` | 12 | holds, `φ=(0↦6,2↦24)` |
| all-A (`A`, `AAAA`) | 1,4 | `p` | `∅` | 0 | vacuous |
| all-S (`S`, `SSSS`) | 1,4 | `−p` | `∅` | `p` | vacuous |
| `SSASAAA` (S-sink control) | 7 | 1 | `{6}` | 3 | holds, `φ(6)=0` |

On `SAAA` the two children coincide, which is allowed: `κ_0+κ_0−2κ_3=−2=−R`.
On the escape word, `t=2` has both a lower-κ A-child and a lower-κ S-child;
I_inv uses the S-child, not the unique minimiser of `{κ_a,κ_j}`.

## I_inv is REFUTED

Two independent failure modes, each with an exact positive-sum word.
Neither word has `U=A`.

### Counterword H1: Hall collision on the unique κ-min S

```text
AASAAASS
p=8, Σ=2, R=4, A-phases {0,1,3,4,5}, D={2,6,7}, U={1,5}.
```

Phase invariants:

```text
r :  0A   1A   2S   3A   4A   5A   6S   7S
κ :  −2    1    1    0    2    1   −3    0
u :  −4   −1    2   −3    0    3    6    1
```

Unique κ-minimum: phase 6, an S.

- `t=1`, least `d=11`, P2 sums `(1,0)` independently recomputed.
  `a=2S` has `κ=1=κ_1` (no strict drop); `j=6S` has `κ=−3<1`.
  Unique S-descent child: `6`.
- `t=5`, least `d=3` (`AAS`), P2 sums `(1,0)`.
  `a=6S` has `κ=−3<1`; `j=2S` has `κ=1=κ_5` (no strict drop).
  Unique S-descent child: `6`.

The bipartite neighbourhood of `{1,5}` is `{6}`, so no injection. Both
two-child identities are degenerate in the same way: one child ties
`κ_s` and the whole strict drop `−R=−4` lands on the unique κ-min S.

### Counterword H2: both two-children are A

```text
ASSSAASAAASAA
p=13, Σ=3, U={0,9,11}, D={1,2,3,6,10}.
```

At `t=11`, least `d=11`, P2 sums `(1,0)`, `a=12A`, `j=0A`.
Both children are A-phases and both strictly drop κ
(`κ_11=23/312`, `κ_12=−27/104`, `κ_0=−1225/312`).
The S-descent set is empty, so I_inv fails on existence, before Hall.
This is the geometric content of E-073 (min-lag endpoint need not be S)
plus a following A; it is not a reuse of the E-073 selector claim.

## One repair I_win, then STOPPED

The two-child pair `{a,j}` is too small: `j` can be A, and even when `j`
is S it need not be the unique lower-κ S that the window can offer.
The single permitted repair enlarges the payable set to the least-P2
certificate, still with a strict κ-drop.

**I_win.** Same quantifiers as I_inv. For `t∈U` let
`N_t = {t−i : 1≤i≤d_t, ε_{t−i}=−1}` and

```text
C_t = {σ ∈ ({a_t} ∪ N_t) ∩ D : κ_σ < κ_t}.
```

There exists an injection `φ: U → D` with `φ(t)∈C_t` for every `t∈U`.

This still implies `|U|≤|D|`. It is not a gap-type lag classification:
the image is any strictly lower-κ S in the actual next phase or the
least supplier window.

Frozen list and both I_inv counterwords pass I_win. In particular
`AASAAASS` gets `C_1={7,6}`, `C_5={6}`, and `ASSSAASAAASAA` gets
`C_11={10,6,3,2,1}`.

### Repair counterword H3

```text
ASASASAAASS
p=11, Σ=1, R=11, A-phases {0,2,4,6,7,8}, D={1,3,5,9,10}, U={0,8}.
U ≠ A (unsupported A-phases 2,4,6,7).
```

Phase invariants:

```text
r :   0A     1S     2A     3S     4A     5S     6A     7A     8A     9S    10S
κ : −11/8   −3/8  −19/8    5/8  −27/8   13/8  −35/8   21/8   −3/8 −107/8  −11/8
u : −11/2    9/2  −15/2    5/2  −19/2    1/2  −23/2   −3/2   17/2   37/2   13/2
```

Unique κ-minimum: phase 9, an S, `κ=−107/8`.

- `t=8`, least `d=3` (`AAS`), P2 sums `(1,0)`.
  `a=9S` drops; `N_8={5}` has `κ_5=13/8>κ_8=−3/8`.
  `C_8={9}`.
- `t=0`, least `d=35`, P2 sums `(1,0)` independently recomputed; no
  shorter P2 lag. The window uses every S-phase, but the only strict
  drop is the global min:
  `κ_9<κ_0`, while `κ_10=κ_0=−11/8` and `κ_1,κ_3,κ_5>κ_0`.
  Next phase `a=1S` also fails the strict drop.
  `C_0={9}`.

Hall fails: `|⋃_{t∈{0,8}} C_t| = |{9}| = 1 < 2`. The two-child identities
still hold (`κ_a+κ_j−2κ_s=−11=−R` at both supplies). I_win only fails as
an inventory: both supplied A-phases must charge the same S-sink.

## What was not claimed

- Not a counterword to E-067 or E-070: on H1, `|U|=2≤3=|D|` and `U≠A`;
  on H3, `|U|=2≤5=|D|` and `U≠A`.
- Not a period-horizon census. After the frozen list, only explicit
  algebraic counterwords were used. No p-extension is offered as evidence.
- Not a second repair. Nonstrict `κ_σ≤κ_s` on the window would save H3
  (`C_0` would gain phase 10) and was not tried. Capacity-two at a
  κ-min S, λ-tuning, and lag-by-lag gap maps are outside the one-repair
  gate.
- Escape selector, oldest-S, second-moment rank, all-A future debt, and
  hole-only models were not reused.

## Evidence log

| Claim | Label | Content |
|---|---|---|
| two-child identity for `F=κ+λu`, `λ≤0` | `PROVED-PAPER` | unchanged from 2026-09-07 geometry attempt; exact-rational regression on every word in this note |
| I_inv on the frozen list | `COMPUTED` | holds, including vacuous all-A / all-S |
| I_inv | `REFUTED` | `AASAAASS` (Hall); `ASSSAASAAASAA` (no S-child) |
| I_win on the frozen list and on both I_inv counterwords | `COMPUTED` | holds |
| I_win | `REFUTED` | `ASASASAAASS` |
| this inventory class | `STOPPED` | one repair used |
| E-067 / E-070 | unchanged, `CONJECTURED` | no `U=A` word |

## Reproduction

Exact integer P2 sums and rational `κ` for the three counterwords can be
recomputed from the cyclic words above: P2 is
`∑_{i=1}^d ε_{t−i}=1` and `∑_{i=1}^d i ε_{t−i}=0`; `κ_r=C_r−B_r^2/(4A)`
with `A=pΣ/2` and the standard period-polynomial recurrence
`B ← B+pε`, `C ← C+(r+1)ε`. Independently checked values include
`(t,d,sum,moment)=(1,11,1,0)` and `(5,3,1,0)` on `AASAAASS`,
`(11,11,1,0)` on `ASSSAASAAASAA`, and `(0,35,1,0)`, `(8,3,1,0)` on
`ASASASAAASS`.

Changed files: only this note.

## Remaining uncertainty and next decision

The S-sink of F-descent is real, but it is not a 1-per-S resource. A
global κ-minimum S can be the unique strict descent child of several
supplied A-phases, even after the payable set is enlarged from the
two-child pair to the whole least-P2 window. That oversubscription is
compatible with `|U|≤|D|`.

Stop this inventory. Do not retune `λ`, do not relax `<` to `≤`, and do
not assign capacity `>1` at the κ-min as a second repair of the same
charge. Reopen a geometric inventory only with a genuinely different
payment (for example a signed mass identity that does not factor through
an injection into lower-κ S-phases). E-067 remains open; H3 is not a
reopening signal for lag-by-lag matching.
