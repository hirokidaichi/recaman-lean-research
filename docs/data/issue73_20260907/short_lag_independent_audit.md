# Issue 73: independent audit of the short-lag injection

- Auditor: entry_barrier; date: 2026-09-07.
- Base revision: `b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`.
- Input: `macro_proof_attempt.md`, Gate 3; H-20260907-09.
- Bounded question: does the proposed map inject all positive phases with a P2
  lag at most 7 into negative phases, for every finite period including small
  periods and repeated appearances of the same phase in a backward window?
- Acceptance: all local types exhausted, well-defined injection on the cyclic
  quotient proved, and the consumer kept strictly to the short-lag subclass.
- Stop: a missed local type, a map collision, or an unjustified quotient step
  retracts the claim. No full-P2 theorem is being audited here.

## Conclusion and exact statement

**`PROVED-PAPER`, independently audited:** for every integer p>=1 and every
p-periodic `epsilon: Z -> {-1,+1}`, put

```
A = {t mod p : epsilon(t)=+1},
D = {t mod p : epsilon(t)=-1},
U7 = {t in A : there exists 1<=d<=7 with
      sum_(i=1)^d epsilon(t-i)=1 and
      sum_(i=1)^d i*epsilon(t-i)=0}.
```

Then `|U7| <= |D|`. The period need not be minimal and its sign sum need not be
positive. The proposed injection is valid. There is no claim of a Lean proof.

When the period sum is positive, `|A|>|D|`, so at least one A phase has no P2
supplier of lag at most 7. If every A phase nevertheless has a P2 supplier, some
A phase has minimum P2 lag at least 11. This does **not** prove `U!=A` for the
unrestricted/bounded-all-lags U of H-09, its Hall assertion, eventual-sign
nonperiodicity, surjectivity, or nonsurjectivity.

## Independent reconstruction of the local classification

For any P2 lag d, let k be the number of negative occurrences in the window.
The unweighted equation gives `d=2k+1`. The weighted equation gives

```
sum(negative offsets) = d(d+1)/4.
```

As d is odd, integrality requires `d=3 mod 4`. Thus d<=7 is either 3 or 7;
there is no d=1,2,4,5,6 boundary case. At d=3 there is one negative offset and
it is exactly 3. In particular the most recent negative is at `t-3`.

For a phase in U7, choose its minimum P2 lag d. If d=7, exactly three negative
occurrences appear. List the negative times bi-infinitely as strictly increasing
`s_l`, let `s_l` be the last one before t, and write

```
h=t-s_l >=1,
c=s_l-s_(l-1) >=1,
b=s_(l-1)-s_(l-2) >=1.
```

Their offsets are `h, h+c, h+c+b`. The two necessary conditions become

```
3h+2c+b=14,       h+b+c<=7.
```

The first gives h<=3. If h=3, the last three signs are backward AAS, so d=3
already supplies t, contradicting the choice of minimum d. For h=1, the
conditions `2c+b=11`, `b+c<=6`, b,c>=1 imply c>=5 and c<=5, giving `(b,c)=(1,5)`.
For h=2, `2c+b=8`, `b+c<=5` imply c>=3 and c<=3, giving `(b,c)=(2,3)`.
These exhaust the minimum-lag-7 cases. Their negative offsets are respectively
`{1,6,7}` and `{2,5,7}`. Both signatures really satisfy P2 and have no d=3.

Minimality is necessary for this three-type classification. For example the
length-eight chronological word `SAASSAAA`, with t at its last A, has negative
offsets `{3,4,7}` and satisfies P2 at d=7, but it already has d=3. This is a
direct symbolic control, not a claim based on trajectory computation.

## Injection and cyclic wrap

Write `delta_l=s_(l+1)-s_l`. For the three types use this map:

| Minimum lag and type | Image negative occurrence | Following gap of image |
|---|---|---|
| d=3, h=3 | s_l | delta_l>=4 |
| d=7, h=1, (b,c)=(1,5) | s_(l-2) | delta_(l-2)=1 |
| d=7, h=2, (b,c)=(2,3) | s_(l-1) | delta_(l-1)=3 |

The first gap bound includes the hypothesis that the current time t is A:
all of `s_l+1,s_l+2,s_l+3` are positive. The other gap identities are the
classified values of b and c. Therefore images of distinct types cannot be
the same negative phase: the following negative gap is a phase invariant and
the sets `>=4`, `=1`, `=3` are disjoint.

For completeness, let m=|D|>0. Periodicity gives
`s_(l+m)=s_l+p`; consequently `delta_(l+m)=delta_l`. Two negative occurrences
have the same phase modulo p if and only if their indices differ by a multiple
of m. In one fixed type the image has index l+r for fixed r in `{0,-2,-1}`.
If two images have equal phase, their indices l+r and l'+r differ by a
multiple of m, hence so do l and l'. Therefore `s_l` and `s_l'` have equal
phase. The value h is fixed inside the type, so `t=s_l+h` and `t'=s_l'+h`
also have equal phase. This proves injectivity on phase sets, without assuming
that p is a fundamental period or that each negative phase occurs only once
inside every possible backward interval.

Each image also belongs to the negative phases in the chosen minimum-lag
interval. Thus the same map proves Hall for every subset of U7 with the
minimum-lag domains N_t of H-09. This restricted Hall statement does not extend
to phases whose minimum lag is at least 11 by the present argument.

## Small-period and repeated-phase checks by argument

- D empty: all signs are positive, so the weighted sum is positive for every
  d>=1 and U7 is empty. A empty is likewise vacuous. These cover period 1.
- One negative phase per period: all delta values equal p. Neither `(b,c)=(1,5)`
  nor `(2,3)` is possible. Only d=3 can occur, and its image gap p>=4 and its
  unique offset h=3 allow at most one supplied A phase.
- Two negative phases per period: `delta_l=delta_(l-2)=b`. In either d=7 type,
  b=h, so `s_(l+1)=s_l+h=t` would itself be negative, contradicting t in A.
  Hence here also only d=3 occurs.
- A minimum-lag-7 phase consequently requires at least three negative phases.
  The three distinct consecutive gaps b, c, delta_l occur in a period, and
  `delta_l>=h+1` because t is A. Thus
  `p>=b+c+h+1=8` in either d=7 type. In particular all periods p<=7 have only
  d=3 supply. There is no hidden repeated-negative-phase case at d=7.
- Sharpness: period `SAAA` has one negative phase and exactly one U7 phase,
  its last A. Both lag identities are `1+1-1=1`, `1+2-3=0`.
- For realizability of the two new types, periods `SSAAAASA` and `SASAASAA`
  have at their final A the two minimum-lag-7 signatures respectively. Their
  images have following gaps 1 and 3 exactly as required.

These are symbolic small/boundary controls. No actual-history assumption is
used, so weakened histories neither enter nor invalidate this word theorem.

## Evidence and handoff

I read the exact regression script `macro_short_lag_injection.py` and its saved
output `macro_short_lag_injection.txt`. The script checks the same direct sums,
minimum lags, classified offsets, gaps and image uniqueness, including every
word of periods 1..14 and deterministic random words of periods 15..80. Its
recorded SHA-256 is
`56a9ed00034f429e03d987764c2ecbd58a400d1fe4e36678e7fc04ec703eeb17`.
No independent new computation or holdout was claimed by this audit; the paper
argument above supplies the all-period conclusion. Commands here were reads
of H-09, the proof attempt, the script/output, and `git rev-parse HEAD`.

This changes the frontier by proving the all-period count for the d<=7
subclass, whereas existing LoopClosingSubtraction supplies local arithmetic
and the previous periodic census supplies finite-period evidence. It does not
complete the full positive-drift obstruction. The next precise question is
whether the new minimum-lag-11 types admit a compatible extension of this
injection or force rearranging its previous images. Do not infer that a failed
extension at d=11 refutes the full Hall/count conjecture.
