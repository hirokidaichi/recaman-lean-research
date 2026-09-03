# Arc death-rule probe — horizon 1e10

Program: `experiments/arc_death_rule_probe.cpp`.
Run: `deathrule 10000000000 t1e10/`, 216 s, plain one-clock-per-iteration run with the
interval-set history and the exact step rule. Outputs in `t1e10/` (archived as `docs/data/deathrule/h1e10_*.txt`; `comb_ends.txt` 7.3 MB and `exceptions_a.txt` 5.3 MB are reproducible and not archived): `summary.txt`
(all tables), `comb_ends.txt` (one line per comb end, 30 columns), `arcs.txt`,
`exceptions_a.txt` (every exception to prediction (a)), `fresh_end_windows.txt`,
`break_notcont_windows.txt`, `other_lock_windows.txt` (100 sampled step windows each).

## Validation

* First 19 landings: PASS (1=1 2=3 4=2 10=11 16=8 31=14 64=26 131=4 222=47 403=92
  770=111 1409=181 2652=150 4825=371 9078=361 16773=781 30768=828 56827=366 99734=19).
* Completed arcs through 1e10: 39. Comb ends: 44,422 in total, 42,908 in completed arcs
  (all tables below use only these), 1,514 in the open arc (excluded).
* Exact facts re-checked at every comb end: a(c+3) = 3c+v+6 in 44,422/44,422; step c+4 is an
  addition iff the test value 2c+v+2 is visited in 44,422/44,422. Inside every lock: the
  level-3 value at clock c+5+2i equals 3c+v+5-i (0 mismatches), the levels are 3/4 as stated
  (0 mismatches), the residue at a break equals v-13-7*i_obs and the level at a break is 2 in
  15,926/15,926 breaks; at the 8 wraps i_obs equals i_wrap(v) = min{i : v < 13+7i} in 8/8.
* Run bookkeeping: h_prev = v0+1+3*J_obs in 42,896/42,896 comb ends with a run; the sweep
  values 2c0+v0-j (j <= min(J_obs,64)) are all visited at time c (0 failures); the value
  2c0+v0-(J_obs+1) is visited at time c iff the run's first level-1 clock was reached by a
  subtraction, 42,896/42,896 (it is the level-2 value a(c0-2-2J) just before the run start;
  that clock is a subtraction in 42,893 of 42,896 runs).

## Definitions used

* Comb: consecutive late landings v0, v0-1, ... two clocks apart; T = number of teeth; the
  comb end is the last tooth (c, v) with v-1 visited; c0 = c-2(T-1), v0 = v+T-1.
* Run (J_obs, h_prev): the maximal alternation L1(sub) L2(add) L1(sub) ... L1 ending at
  c0-1, where a level-1 clock reached by a subtraction from a level-2 clock that was reached
  by an addition from a level-1 clock of the run completes a pair; any other level-1 clock
  starts a run; a late landing or a level >= 3 clock breaks it. J_obs = pairs of that run,
  h_prev = height a-m at its first level-1 clock m (after a late landing w this is w).
  hasRun = false (c0-1 not a level-1 clock of a run) for 12 comb ends, all fresh.
* Lock outcome for blocked comb ends: "break" = subtraction at a clock c+6+2i (to level 2),
  "wrap" = residue increase (arc end) at any clock after c, "l3blocked" = addition at a clock
  c+5+2i (the level-3 value 3c+v+5-i was visited; the orbit goes to level 5),
  "interrupted" = late landing while locked (never happened). i_obs = completed pairs.
* i_pred = min{i : 3i+1 > J_obs} = floor((J_obs+2)/3).
* Algebraic identities behind the extra columns: with T teeth the lock candidates
  2c+v-1-3i equal 2c0+v0-1+3(T-1-i); for i <= T-2 they are the test values 2c_t+v_t+2 of the
  earlier teeth t = T-2-i, and for i >= T-1 they are the sweep values 2c0+v0-j with
  j = 3(i-T+1)+1. J_eff = J_obs + [run start was a subtraction],
  i_gen = (T-1) + floor((J_eff+2)/3) is the first candidate that is neither an earlier
  tooth's test value nor a sweep value. candMask = visited status at time c of the first 64
  candidates.
* Wrap condition derived from the residues: at the level-4 clock c+4+2i r = v-6-7i (needs
  >= 4), at the level-3 clock c+5+2i r = v-10-7i (needs >= 3), so a lock that would break at
  pair i* wraps first iff v < 13 + 7 i*. Tested with i* = i_pred: predicted wrap iff
  v < 13 + 7*i_pred (equivalently 7*i_pred > v-13). The literal 7*i_pred > v-6 was tested too.

## 1. Counts

* blocked = 19,386, fresh = 23,522.
* continued (a later late landing in the same arc): blocked 19,365 / not continued 21;
  fresh 23,507 / not continued 15. All 36 not-continued comb ends are the landings (arc
  minima) of their arcs; the 3 arcs without any comb end are arcs 1, 2, 4 (landings 1=1,
  2=3, 10=11). In all 36 arcs that have a comb end, the last comb end is the landing.
* endedEarly (arc ends before c+4): 2 (c=4 v=2 and c=131 v=4, both fresh).
* Teeth: T=1: 5,140 (fresh 1,726 / blocked 3,414); T=2: 1,995 (679 / 1,316); T>=3: 35,773;
  max T = 10,837,267.
* J_obs = 0: 18,929; J_obs >= 1: 23,979; max J_obs = 2,584,047.

## 3. Lock outcomes (19,386 blocked comb ends)

* break 15,926; wrap 8; l3blocked 3,452; interrupted 0.
* i_obs at breaks: median 5,484, max 1,665,489. i_obs at the 8 wraps: 124, 342, 345, 760,
  2114, 2301, 2585, 3603.
* l3blocked: i_obs = 0 (the very first level-3 value 3c+v+5 is visited) in 2,890;
  1 <= i_obs < i_gen in 514; i_obs >= i_gen in 48. The step is to level 5 in all 3,452. In
  the 100 sampled windows the six steps after that are `5A 4S 5A 4S 5A 4S` in 85,
  `3S 4A 3S 4A 3S 4A` in 11, `5A 6A 5S 6A 5S 6A` in 2, other in 2. Continued 3,450, not
  continued 2 (c=99734 v=19, c=588583 v=4802, both arc landings). The preceding comb end of
  the same arc was fresh in 347, blocked-l3blocked in 754, blocked-break in 2,351.

## 4(a). Break index

Literal prediction i_obs = i_pred = floor((J_obs+2)/3), over the 15,926 breaks:

* holds for 1,735 (10.9%). By teeth: T=1 1,732 of 2,658; T=2 0 of 1,012; T>=3 3 of 12,256
  (the three: c=321202 v=14517 T=51 J=54 i=18; c=511407787 v=294478 T=157 J=0 i=0;
  c=887655210 v=33884113 T=1218 J=177 i=59).
* exceptions: i_obs > i_pred in 13,767, i_obs < i_pred in 424.
* For T=1: i_obs - i_pred = 0 in 1,732, = 1 in 794, larger in 132.
* i_obs equals the index of the first fresh candidate at time c in 347/347 breaks with
  i_obs < 64 (the mask covers 64 candidates).

First 10 exceptions (c v T J_obs h_prev i_obs i_pred i_gen mask, 1 = candidate visited at c):

```
c=111        v=40    T=1  J=0   h=41    i_obs=1  i_pred=0 i_gen=1  mask=10000000
c=1345       v=255   T=1  J=12  h=292   i_obs=5  i_pred=4 i_gen=5  mask=11111000
c=2418       v=475   T=2  J=13  h=516   i_obs=6  i_pred=5 i_gen=6  mask=111111000
c=4135       v=1314  T=10 J=0   h=1324  i_obs=10 i_pred=0 i_gen=10 mask=1111111111000
c=4645       v=637   T=5  J=11  h=675   i_obs=8  i_pred=4 i_gen=8  mask=11111111000
c=8216       v=1592  T=8  J=11  h=1633  i_obs=11 i_pred=4 i_gen=11 mask=11111111111000
c=13507      v=4926  T=7  J=0   h=4933  i_obs=7  i_pred=0 i_gen=7  mask=1111111000
c=16773      v=781   T=12 J=3   h=802   i_obs=13 i_pred=1 i_gen=13 mask=1111111111111000
c=23972      v=10320 T=28 J=0   h=10348 i_obs=28 i_pred=0 i_gen=28 mask=1111...1000 (28 ones)
c=28322      v=4801  T=1  J=6   h=4820  i_obs=3  i_pred=2 i_gen=3  mask=11100000
```

Generalized index i_gen = (T-1) + floor((J_eff+2)/3):

* holds for 12,777 of 15,926. T=1: 2,523 of 2,658 (all 135 exceptions have i_obs > i_gen);
  T=2: 974 of 1,012 (all 38 exceptions have i_obs > i_gen); T>=3: 9,280 of 12,256
  (2,551 with i_obs < i_gen, 425 with i_obs > i_gen).
* All 2,551 cases with i_obs < i_gen have i_obs <= T-2 (the fresh candidate is an earlier
  tooth's test value); none has i_obs >= T-1. Among T>=2 breaks, the candidates i <= T-2
  are all visited at c in 13,193 of 13,268 (mask limited to 64 candidates); in the 75 with a
  fresh one among the first 64, i_obs is that first fresh index in 31/31 cases with i_obs < 24.
* Of the 598 cases with i_obs > i_gen: i_obs - i_gen = 1 in 29, > 1 in 569.

First 10 exceptions to i_gen (all have runStartSub = 1):

```
c=30498     v=1275   T=31  J=71  i_obs=3   i_gen=54  mask=111000000000000000000000011111...
c=137277    v=60567  T=102 J=68  i_obs=56  i_gen=124 mask=(56 ones)00000000
c=144897    v=51107  T=246 J=0   i_obs=69  i_gen=246 mask=(64 ones)
c=250024    v=109636 T=663 J=11  i_obs=0   i_gen=666 mask=(64 zeros)
c=321202    v=14517  T=51  J=54  i_obs=18  i_gen=69  mask=111111111111111111011111...
c=470515    v=170386 T=466 J=14  i_obs=438 i_gen=470 mask=(64 ones)
c=558551    v=51956  T=173 J=234 i_obs=125 i_gen=251 mask=(64 ones)
c=561385    v=45575  T=233 J=0   i_obs=27  i_gen=233 mask=111111111111111111111111111001...
c=572779    v=28716  T=54  J=964 i_obs=45  i_gen=375 mask=(45 ones)00000000111...
c=575509    v=24289  T=70  J=0   i_obs=23  i_gen=70  mask=(23 ones)0000...
```

## 4(b). Wrap prediction (breaks and wraps only; the 3,452 l3blocked are excluded)

Exact form, predicted wrap iff v < 13 + 7*i_pred:

|                | predicted wrap | predicted break |
|----------------|---------------:|----------------:|
| observed wrap  |              7 |               1 |
| observed break |              0 |          15,926 |

The literal form 7*i_pred > v-6 and the form with i_gen give the identical table.
The single exception: c=101762018 v=25231 T=1 J_obs=7932 h_prev=49028, i_pred=2644,
i_gen=2645, observed wrap at i_obs=3603 = i_wrap(v) (offset c+7212, residue 0 at level 3
before the wrap); its first 64 candidates are all visited at c.

The 8 wraps (c, v, T, J_obs, i_obs, i_pred, i_gen, wrap offset, level/residue before the
wrap step):

```
c=328002     v=879   T=1 J=506   i_obs=124  i_pred=169  i_gen=169  off=254  k=3 r=1
c=1787013    v=5329  T=1 J=3333  i_obs=760  i_pred=1111 i_gen=1112 off=1525 k=4 r=3
c=18394609   v=18107 T=1 J=8577  i_obs=2585 i_pred=2859 i_gen=2860 off=5176 k=3 r=2
c=32144188   v=16114 T=2 J=10644 i_obs=2301 i_pred=3548 i_gen=3550 off=4607 k=4 r=1
c=101762018  v=25231 T=1 J=7932  i_obs=3603 i_pred=2644 i_gen=2645 off=7212 k=3 r=0
c=904032692  v=14804 T=1 J=6727  i_obs=2114 i_pred=2243 i_gen=2243 off=4233 k=4 r=0
c=1610186343 v=2426  T=1 J=4025  i_obs=345  i_pred=1342 i_gen=1342 off=696  k=3 r=1
c=2789149734 v=2405  T=1 J=11105 i_obs=342  i_pred=3702 i_gen=3702 off=690  k=3 r=1
```

## 4(c). Death rule

Blocked comb ends, "arc ends here (not continued)" vs lock outcome:

|                | wrap | break  | l3blocked |
|----------------|-----:|-------:|----------:|
| not continued  |    8 |     11 |         2 |
| continued      |    0 | 15,915 |     3,450 |

The 11 "break & not continued" comb ends (all arc landings; i_obs = i_gen in all 11; gap =
clocks from c to the arc end, i.e. to the residue wrap, with no late landing in between):

```
c=16773      v=781    T=12  J=3     i_obs=13   gap=451
c=30768      v=828    T=3   J=100   i_obs=36   gap=454
c=1032996    v=3378   T=1   J=65    i_obs=22   gap=1843
c=3220128    v=9462   T=1   J=578   i_obs=193  gap=5791
c=10201340   v=18954  T=159 J=1506  i_obs=661  gap=10871
c=58055311   v=4202   T=1   J=1388  i_obs=463  gap=1565
c=173367175  v=60240  T=1   J=3509  i_obs=1170 gap=28745
c=302844912  v=92404  T=1   J=11805 i_obs=3936 gap=45837
c=511518279  v=92188  T=1   J=18761 i_obs=6254 gap=42942
c=4910724199 v=89386  T=1   J=17103 i_obs=5702 gap=34199
c=8416516444 v=110522 T=2   J=10984 i_obs=3663 gap=63911
```

Fresh comb ends: continued 23,507, not continued 15. The 15 (all arc landings) and what
follows them, from the step windows and an independent Python replay of the orbit to
5.8e6 (K = pairs of the level-2/3 ping-pong `3A 2S` after landing the test value at c+4,
P = pairs `2A 1S` of the level-1/2 sweep after the exit to level 1, "wrap" = the step at
which the residue increases, with level k and residue r just before it):

```
c=4       v=2     T=1  J=0   h=1     gap=3     steps 1A 2A then wrap at c+3 (k=2 r=1, add -> k=2 r=6)
c=16      v=8     T=3  J=1   h=4     gap=6     c+4 lands test value; K=0; c+5 3A; wrap at c+6 (k=3 r=0, sub -> k=1 r=19)
c=31      v=14    T=5  J=0   h=19    gap=9     K=1; exit 1S at c+7; P=0; c+8 2A(r=0); wrap at c+9 (sub -> late landing 38)
c=64      v=26    T=13 J=0   h=1     gap=13    K=4; wrap at c+13 (k=2 r=0, sub -> late landing 75)
c=131     v=4     T=2  J=4   h=18    gap=4     steps 1A 2A 3A then wrap at c+4 (k=3 r=1, sub -> k=1 r=133)
c=222     v=47    T=14 J=1   h=64    gap=27    K=4; exit c+13; P=6 (sweep ends c+25); 2A(r=0); wrap at c+27 (sub -> late landing 247)
c=403     v=92    T=19 J=7   h=132   gap=51    K=6; exit c+17; P=15 (ends c+47); 2A 3A 4A; wrap at c+51 (k=4 r=3, sub -> k=2 r=453)
c=770     v=111   T=2  J=1   h=116   gap=75    K=0; exit c+5; P=34 (ends c+73); 2A(r=0); wrap at c+75 (add -> k=2 r=843)
c=1409    v=181   T=24 J=0   h=205   gap=112   K=7; exit c+19; P=46 (ends c+111); wrap at c+112 (k=1 r=0, add -> k=1 r=1520)
c=2652    v=150   T=1  J=7   h=172   gap=101   K=0; exit c+5; P=47 (ends c+99); 2A(r=0); wrap at c+101 (sub -> late landing 2751)
c=4825    v=371   T=6  J=2   h=383   gap=221   K=1; exit c+7; P=96 (ends c+199); 2A 3A 4A ...; wrap at c+221 (k=4 r=1, sub -> k=2 r=5043)
c=9078    v=361   T=5  J=25  h=441   gap=240   K=1; exit c+7; P=116 (ends c+239); wrap at c+240 (k=1 r=0, add -> k=1 r=9317)
c=56827   v=366   T=1  J=153 h=826   gap=245   K=0; exit c+5; P=119 (ends c+243); 2A(r=0); wrap at c+245 (sub -> late landing 57070)
c=181653  v=61    T=1  J=2   h=68    gap=41    K=0; exit c+5; P=17 (ends c+39); 2A(r=1); wrap at c+41 (sub -> late landing 181693)
c=5771203 v=32102 T=1  J=1   h=32106 gap=13383 K=0; exit c+5; P=3078 (ends c+6161); 2A 3A 4A ...; wrap at c+13383 (k=2 r=1, add -> k=2 r=5784585)
```

In all 15 the arc ends by a residue wrap with r in {0, 1, 3} before the wrap step; 6 of the
wrap steps are late landings (value n-2 in 5, n-1 in 1), the other 9 land level 1 or 2 with
residue n-1, n-2 or n-3. The two endedEarly cases wrap before c+4; the other 13 land the
test value at c+4 and run K = 0..7 pairs of the 2/3 ping-pong; 2 of them (c=16, c=64) wrap
without reaching level 1; the remaining 11 exit to level 1, run P = 0..3078 sweep pairs, and
wrap 1 to 7,222 clocks after the sweep ends (1 or 2 clocks in 8 of the 11; 4, 22 and 7,222
in the other three, after climbing 2A 3A 4A ...).

## 5. Ratio v / h_prev (comb ends with a run; bins of width 0.05)

| bin        | all: continued | all: not continued | blocked: continued | blocked: not continued |
|------------|---------------:|-------------------:|-------------------:|-----------------------:|
| 0.05-0.10  |              1 |                  1 |                  0 |                      1 |
| 0.15-0.20  |              0 |                  1 |                  0 |                      1 |
| 0.20-0.25  |              0 |                  1 |                  0 |                      0 |
| 0.30-0.35  |              1 |                  2 |                  0 |                      2 |
| 0.35-0.40  |              0 |                  1 |                  0 |                      1 |
| 0.40-0.45  |              0 |                  4 |                  0 |                      3 |
| 0.45-0.50  |              2 |                  0 |                  1 |                      0 |
| 0.50-0.55  |              1 |                  2 |                  1 |                      2 |
| 0.55-0.60  |              1 |                  0 |                  0 |                      0 |
| 0.60-0.65  |              7 |                  2 |                  1 |                      2 |
| 0.65-0.70  |              3 |                  1 |                  2 |                      0 |
| 0.70-0.75  |              2 |                  4 |                  2 |                      2 |
| 0.75-0.80  |             10 |                  1 |                  6 |                      1 |
| 0.80-0.85  |             21 |                  3 |                 11 |                      2 |
| 0.85-0.90  |             36 |                  4 |                 27 |                      1 |
| 0.90-0.95  |            151 |                  1 |                 90 |                      1 |
| 0.95-1.00  |         42,627 |                  5 |             19,224 |                      2 |

(No ratio >= 1; all comb ends: 42,863 continued, 33 not continued; blocked: 19,365 / 21.)
Smallest ratio among blocked continued comb ends: 0.491. Ratios of the 21 blocked not
continued: 0.067 0.167 0.335 0.348 0.367 0.404 0.413 0.423 | 0.502 0.515 0.621 0.635 0.723
0.732 0.770 0.802 0.845 0.851 0.945 0.974 0.975 (7/16 = 0.4375 separates the groups).

Blocked comb ends, "not continued" vs v < (7/16) h_prev:

|                | v < 7h/16 | v >= 7h/16 |
|----------------|----------:|-----------:|
| not continued  |         8 |         13 |
| continued      |         0 |     19,365 |

The 8 with v < 7h/16 are 7 of the 8 wraps plus the l3blocked c=99734 (v=19, h=47); the 13
with v >= 7h/16 are the 11 breaks, the wrap c=101762018 (v/h = 0.515) and the l3blocked
c=588583 (v/h = 0.975). Over all comb ends with a run: not continued & v < 7h/16 = 9,
not continued & v >= 7h/16 = 24, continued & v < 7h/16 = 2, continued & v >= 7h/16 = 42,861.
