# Arc potential probe: Phi, drops at comb ends, blocked test values, and Phi decreases (canonical orbit, horizon 10^10)

Date: 2026-09-02. Program: `experiments/arc_potential_probe.cpp` (new file; simulator core, interval-set
history, exact step rule and Chaffin's residue-increase arc detector copied from
`experiments/arc_trace_probe.cpp`). Run: `arcpot 10000000000 potential/h1e10` (plain steps, one clock per
iteration, 228.5 s, 105347 intervals at the horizon, mex 1355, final value 16705983634). Outputs in
`potential/h1e10/`: `summary.txt`, `arcs.txt`, `marked_comb_ends.txt` (22483 rows), `lowdrop_blocked.txt`
(318 rows), `watch_values.txt`, `watch.txt`, `decreases.txt` (69 windows), `blocked_windows.txt` (40
windows). All numbers below are copied from these files.

## 0. Definitions used by the program (exact)

- a(0) = 0, history {0}. At clock n >= 1 the candidate is a(n-1) - n; subtract iff a(n-1) > n and the
  candidate is not in the history, else add n. a(n) = k(n) n + r(n), 0 <= r < n.
- Arc: maximal stretch of clocks with no residue increase (the wrap clock starts the next arc). Landing:
  the arc's minimum value, at the first clock attaining it. Late landing: a(n) < n (k = 0).
- Comb end: a late landing a(c) = v with v-1 visited at time c. Test value: 2c+v+2. Blocked: the test value
  is visited at time c+3. (The values visited at c+1, c+2, c+3 are c+v+1, 2c+v+3, 3c+v+6, none equal to
  2c+v+2, so the program looks the test value up at time c; it verifies at clock c+3 that a(c+3) = 3c+v+6
  and at clock c+4 that the step is an addition iff blocked.)
- Level-1 clock m: k(m) = 1 (m <= a(m) < 2m). Phi(m) = a(m) + m = 2m + h(m). Phi* = running maximum of Phi
  over the level-1 clocks of the current arc, reset at the arc start. At a comb end (c, v): a(c-1) = c+v,
  Phi(c-1) = 2c+v-1, the test value is Phi(c-1)+3, and drop = Phi* - (2c+v-1) with Phi* over the level-1
  clocks <= c-1 of the arc (drop is undefined if the arc has no level-1 clock before c; this happened once,
  at the comb end c=4, v=2 of arc 3).
- Continued: the arc has a later late landing after the comb end. Since a comb end is itself a late
  landing, the arc's last late landing is never continued and every other comb end is continued.
- Depth class of a comb end (c, v): 0 if 10v >= c; 1 if 10v < c <= 100v; 2 if 100v < c <= 1000v; 3 if
  1000v < c. Class 3 is exactly the traced regime of `arc_trace_probe.cpp` (r*1000 < n at a k = 0 clock);
  the 6 deep arcs have 5+18+33+44+47+66 = 213 class-3 comb ends, the same 213 comb ends as in
  `docs/ARC_TRACE_2026-09-02.md`.
- Phi decrease: a level-1 clock m whose Phi(m) is below the Phi of the previous level-1 clock of the same
  arc; size = the difference; gap = distance between the two level-1 clocks; maxk = the largest k at the
  clocks strictly between them.

## 1. Validation

- Checkpoint (first 19 landings): PASS. `first landings: 1=1 2=3 4=2 10=11 16=8 31=14 64=26 131=4 222=47
  403=92 770=111 1409=181 2652=150 4825=371 9078=361 16773=781 30768=828 56827=366 99734=19`.
- All 39 completed arcs (start clock, end clock, start value, landing index, landing value, late-landing
  count, last late landing) agree with `docs/data/arctrace/h1e10_arcs_all.txt` (checked for the 22 arcs of a
  10^6 run field by field; the 39-arc table below reproduces the same landings as the arctrace ledger,
  including 1610186343=2426, 2789149734=2405, 4910724199=89386, 8416516444=110522).
- Independent Python re-implementation (`potential/crosscheck.py`) of the arc/comb-end/Phi bookkeeping on
  the prefix 10^6: 22 arcs, 0 mismatches in (start, end, start value, landing, late count, level-1 count,
  comb ends, blocked, drop>=3, decreases, decrease sum); the 120 comb ends that are blocked or have drop
  >= 3 are identical (arc, clock, value, class, drop, blocked).
- Step-rule verification inside the 10^10 run: a(c+3) = 3c+v+6 at all 44422 comb ends (0 mismatches);
  step c+4 is an addition iff blocked at all 44422 comb ends (0 mismatches).
- Cross-check against `arc_trace_probe` (rebuilt, run to 1610187100, file `lates_1610186343.txt`, arc 36):
  33 late landings with v-1 visited (= class-3 comb ends), 31 of them with next8 starting A,A,A,A (blocked
  at +4), 2 with A,A,A,B; of the 31, 30 have a later late landing in the arc (nextLate present) and 1 (the
  landing 1610186343=2426) has none. The potential probe reports for arc 36: class-3 comb ends 33,
  blocked 31, blocked & continued 30, blocked & not continued 1.

## 2. Comb ends: totals

44422 comb ends in the 39 completed arcs (comb ends of the open arc 40 that were followed by a later late
landing are also included in the tables of sections 3-5, since they are resolved online; only the last comb
end of the open arc is unresolved and excluded; the 40th arc had 1514 comb ends at the horizon, 352 blocked,
none in class 3). Blocked: 19738. Fresh: 24684. Drop undefined: 1 (fresh). Drop negative: 0.

Comb ends by depth class: class 0: 33601; class 1: 9224; class 2: 1330; class 3: 267.

## 3. (i) blocked x continued

| | continued (a later late landing in the arc) | not continued | total |
|---|---|---|---|
| blocked | 19717 | 21 | 19738 |
| fresh | 24669 | 15 | 24684 |
| total | 44386 | 36 | 44422 |

By class (blocked & continued / blocked & not continued / fresh & continued / fresh & not continued):
class 0: 11893 / 0 / 21700 / 8; class 1: 6580 / 2 / 2638 / 4; class 2: 1054 / 6 / 268 / 2;
class 3: 190 / 13 / 63 / 1.

The 36 not-continued comb ends are exactly the 36 landings of the 36 arcs that have a comb end (arcs 1, 2,
4 have no late landing; "landing is a comb end: 36; of these blocked: 21", "landing is the last late
landing: 36"). Of the 15 fresh & not continued, 2 are comb ends whose arc ended before clock c+4 (arcs 3
and 5). Among the 44386 continued comb ends, 19717 are blocked.

In class 3 (267 comb ends): 203 blocked, of which 190 continued and 13 did not; the 13 are the landings of
arcs 19, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39. The 64 fresh class-3 comb ends: 63 continued, 1
did not (the landing 181653=61 of arc 20).

Gap (clocks) from a continued comb end to the next late landing, binned by powers of two (bin b:
2^b <= gap < 2^(b+1)):

- blocked class 3 (190): b7=4 b8=3 b9=2 b10=8 b11=5 b12=19 b13=35 b14=46 b15=37 b16=14 b17=13 b18=4
  (smallest gap >= 128).
- blocked class 2 (1054): b4=2 b5=1 b6=3 b7=6 b8=11 b9=16 b10=39 b11=75 b12=120 b13=140 b14=159 b15=178
  b16=140 b17=95 b18=47 b19=21 b20=1.
- blocked class 1 (6580): b3=1 b4=3 b5=6 b6=16 b7=29 b8=52 b9=130 b10=216 b11=393 b12=611 b13=891
  b14=1098 b15=1051 b16=916 b17=570 b18=345 b19=171 b20=73 b21=7 b22=1.
- blocked class 0 (11893): b4=7 b5=27 b6=47 b7=122 b8=177 b9=345 b10=534 b11=820 b12=1206 b13=1589
  b14=1754 b15=1759 b16=1527 b17=1031 b18=602 b19=238 b20=88 b21=18 b22=2.
- fresh class 3 (63): b3=2 b5=4 b6=3 b7=4 b8=3 b9=3 b10=11 b11=7 b12=12 b13=6 b14=3 b15=3 b16=1 b17=1.
- fresh class 0 (21700): b2=94 b3=9 b4=44 b5=62 b6=143 b7=269 b8=425 b9=779 b10=1139 b11=1706 b12=2301
  b13=2749 b14=3137 b15=2960 b16=2359 b17=1597 b18=1057 b19=519 b20=236 b21=87 b22=27 b23=1 (class 1 and 2
  rows in `summary.txt`).

## 4. (ii) blocked x drop >= 3 (44421 comb ends with a defined drop)

| | drop >= 3 | drop < 3 | total |
|---|---|---|---|
| blocked | 19420 | 318 | 19738 |
| fresh | 2745 | 21938 | 24683 |
| total | 22165 | 22256 | 44421 |

By class (blocked & drop>=3 / blocked & drop<3 / fresh & drop>=3 / fresh & drop<3):
class 0: 11596 / 297 / 1145 / 20562; class 1: 6562 / 20 / 1320 / 1322; class 2: 1059 / 1 / 219 / 51;
class 3: 203 / 0 / 61 / 3.

The same table with the threshold drop >= 2: blocked & drop>=2 = 19421, blocked & drop<2 = 317,
fresh & drop>=2 = 2745, fresh & drop<2 = 21938 (only one comb end has drop = 2 and one has drop = 1).

Blocked comb ends with drop < 3: 318 (317 with drop 0, 1 with drop 2; class 0: 297, class 1: 20,
class 2: 1, class 3: 0). All 318 are listed in `lowdrop_blocked.txt`. The first 20, with the first-visit
clock of the test value 2c+v+2 from the watch-mode second pass (`watch.txt`, stopped at clock 1500189):

| # | arc | c | v | class | drop | test value 2c+v+2 | arc start clock | first visit clock of the test value | k at first visit | step at first visit | first visit before the arc start? |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 20 | 144897 | 51107 | 0 | 0 | 340903 | 99742 | 76106 | 4 | A | yes |
| 2 | 21 | 250024 | 109636 | 0 | 0 | 609686 | 181694 | 137283 | 4 | A | yes |
| 3 | 22 | 572779 | 28716 | 1 | 0 | 1174276 | 328256 | 274300 | 4 | A | yes |
| 4 | 23 | 999644 | 57842 | 1 | 0 | 2057132 | 589933 | 473219 | 4 | A | yes |
| 5 | 23 | 999824 | 57540 | 1 | 0 | 2057190 | 589933 | 473335 | 4 | A | yes |
| 6 | 23 | 1008266 | 45415 | 1 | 0 | 2061949 | 589933 | 475177 | 4 | A | yes |
| 7 | 23 | 1020130 | 27495 | 1 | 0 | 2067757 | 589933 | 478785 | 4 | A | yes |
| 8 | 24 | 1567529 | 349831 | 0 | 0 | 3484891 | 1034839 | 773018 | 4 | A | yes |
| 9 | 25 | 2815176 | 616108 | 0 | 0 | 6246462 | 1788538 | 1400535 | 4 | S | yes |
| 10 | 25 | 2886558 | 522483 | 0 | 0 | 6295601 | 1788538 | 1424529 | 4 | A | yes |
| 11 | 25 | 2896294 | 511135 | 0 | 0 | 6303725 | 1788538 | 1427945 | 4 | A | yes |
| 12 | 25 | 2926318 | 475199 | 0 | 0 | 6327837 | 1788538 | 1439701 | 4 | A | yes |
| 13 | 25 | 2927114 | 474231 | 0 | 0 | 6328461 | 1788538 | 1440949 | 4 | A | yes |
| 14 | 25 | 3014040 | 367542 | 0 | 0 | 6395624 | 1788538 | 1474423 | 4 | A | yes |
| 15 | 25 | 3061810 | 296179 | 1 | 0 | 6419801 | 1788538 | 1486121 | 4 | A | yes |
| 16 | 25 | 3066322 | 287241 | 1 | 0 | 6419887 | 1788538 | 1486293 | 4 | A | yes |
| 17 | 25 | 3076288 | 267686 | 1 | 0 | 6420264 | 1788538 | 1487047 | 4 | A | yes |
| 18 | 25 | 3094960 | 238604 | 1 | 0 | 6428526 | 1788538 | 1490075 | 4 | A | yes |
| 19 | 25 | 3124974 | 195595 | 1 | 0 | 6445545 | 1788538 | 1498397 | 4 | A | yes |
| 20 | 25 | 3126994 | 192451 | 1 | 0 | 6446441 | 1788538 | 1500189 | 4 | A | yes |

In all 20 cases the test value was first visited before the arc started (in an earlier arc), at a clock of
about 0.47-0.53 c, as a k = 4 value (19 by an addition, 1 by a subtraction).

Fresh comb ends with drop >= 3: 2745. Their drops are all > 20 (smallest: 270 in class 1, 363 in class 0,
25968 in class 2, 52220 in class 3; the full class:drop list is in `summary.txt`, line "fresh & drop>=3
detail").

## 5. Drop histogram at comb ends (defined drops, all classes)

| drop | total | blocked | fresh | continued | not continued |
|---|---|---|---|---|---|
| 0 | 22254 | 317 | 21937 | 22240 | 14 |
| 1 | 1 | 0 | 1 | 1 | 0 |
| 2 | 1 | 1 | 0 | 1 | 0 |
| 3 | 2 | 2 | 0 | 2 | 0 |
| 4 | 1 | 1 | 0 | 1 | 0 |
| 5 | 1 | 1 | 0 | 1 | 0 |
| 6 | 2 | 2 | 0 | 2 | 0 |
| 7 | 1 | 1 | 0 | 1 | 0 |
| 8 | 4 | 4 | 0 | 4 | 0 |
| 9 | 1 | 1 | 0 | 1 | 0 |
| 10 | 1 | 1 | 0 | 1 | 0 |
| 11 | 0 | 0 | 0 | 0 | 0 |
| 12 | 2 | 2 | 0 | 2 | 0 |
| 13 | 1 | 1 | 0 | 1 | 0 |
| 14 | 0 | 0 | 0 | 0 | 0 |
| 15 | 4 | 4 | 0 | 4 | 0 |
| 16 | 1 | 1 | 0 | 1 | 0 |
| 17 | 2 | 2 | 0 | 2 | 0 |
| 18 | 2 | 2 | 0 | 2 | 0 |
| 19 | 1 | 1 | 0 | 1 | 0 |
| 20 | 1 | 1 | 0 | 1 | 0 |
| > 20 | 22138 | 19393 | 2745 | 22117 | 21 |

Drops 1..20 occur at 29 comb ends in total (27 of them blocked); every other comb end has drop 0 (22254) or
drop > 20 (22138).

Class 3 only: drop 0: 3 (0 blocked, 3 fresh; 2 continued, 1 not); drop > 20: 264 (203 blocked, 61 fresh;
251 continued, 13 not). No class-3 comb end has 1 <= drop <= 20.

## 6. Per-arc table (39 completed arcs)

Columns: clocks of the arc; landing index=value; landing class (0..3 as above, of the landing (index,
value)); steps from the landing to the arc end; late landings; level-1 clocks; comb ends; blocked comb
ends; comb ends with drop >= 3; class-3 comb ends / class-3 blocked; first comb end with drop >= 3
(c=v:drop); first blocked comb end (c=v:drop); first class-3 blocked comb end; the landing's own comb-end
record (drop:blocked/fresh); three equality flags; max drop over the arc's comb ends (-1 = no defined
drop); Phi decreases in the arc; largest decrease.

| arc | clocks | landing index=value | landing class | steps after landing | late landings | level-1 clocks | comb ends | blocked | drop>=3 | class-3 comb ends / blocked | first drop>=3 (c=v:drop) | first blocked (c=v:drop) | first class-3 blocked (c=v:drop) | landing comb end (drop:state) | landing = first blocked | landing = first drop>=3 | landing = first class-3 blocked | max drop | Phi decreases | max decrease |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 1..1 | 1=1 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 / 0 | none | none | none | notCombEnd | N | N | N | -1 | 0 | 0 |
| 2 | 2..3 | 2=3 | 0 | 1 | 0 | 1 | 0 | 0 | 0 | 0 / 0 | none | none | none | notCombEnd | N | N | N | -1 | 0 | 0 |
| 3 | 4..6 | 4=2 | 0 | 2 | 1 | 1 | 1 | 0 | 0 | 0 / 0 | none | none | none | undef:fresh | N | N | N | -1 | 0 | 0 |
| 4 | 7..11 | 10=11 | 0 | 1 | 0 | 2 | 0 | 0 | 0 | 0 / 0 | none | none | none | notCombEnd | N | N | N | -1 | 0 | 0 |
| 5 | 12..21 | 16=8 | 0 | 5 | 3 | 3 | 1 | 0 | 0 | 0 / 0 | none | none | none | 0:fresh | N | N | N | 0 | 0 | 0 |
| 6 | 22..39 | 31=14 | 0 | 8 | 5 | 7 | 1 | 0 | 0 | 0 / 0 | none | none | none | 0:fresh | N | N | N | 0 | 1 | 1 |
| 7 | 40..76 | 64=26 | 0 | 12 | 13 | 13 | 1 | 0 | 0 | 0 / 0 | none | none | none | 0:fresh | N | N | N | 0 | 0 | 0 |
| 8 | 77..134 | 131=4 | 1 | 3 | 15 | 21 | 3 | 1 | 1 | 0 / 0 | 111=40:3 | 111=40:3 | none | 0:fresh | N | N | N | 3 | 2 | 6 |
| 9 | 135..248 | 222=47 | 0 | 26 | 32 | 44 | 2 | 0 | 0 | 0 / 0 | none | none | none | 0:fresh | N | N | N | 0 | 3 | 5 |
| 10 | 249..453 | 403=92 | 0 | 50 | 54 | 79 | 3 | 0 | 0 | 0 / 0 | none | none | none | 0:fresh | N | N | N | 0 | 3 | 8 |
| 11 | 454..844 | 770=111 | 0 | 74 | 109 | 152 | 4 | 0 | 0 | 0 / 0 | none | none | none | 0:fresh | N | N | N | 0 | 3 | 24 |
| 12 | 845..1520 | 1409=181 | 0 | 111 | 182 | 248 | 4 | 1 | 1 | 0 / 0 | 1345=255:28 | 1345=255:28 | none | 0:fresh | N | N | N | 28 | 5 | 33 |
| 13 | 1521..2752 | 2652=150 | 1 | 100 | 322 | 471 | 8 | 1 | 1 | 0 / 0 | 2418=475:8 | 2418=475:8 | none | 0:fresh | N | N | N | 8 | 9 | 47 |
| 14 | 2753..5045 | 4825=371 | 1 | 220 | 665 | 857 | 8 | 2 | 2 | 0 / 0 | 4135=1314:95 | 4135=1314:95 | none | 0:fresh | N | N | N | 95 | 9 | 122 |
| 15 | 5046..9317 | 9078=361 | 1 | 239 | 1203 | 1642 | 12 | 1 | 1 | 0 / 0 | 8216=1592:4 | 8216=1592:4 | none | 0:fresh | N | N | N | 4 | 13 | 100 |
| 16 | 9318..17223 | 16773=781 | 1 | 450 | 2318 | 3002 | 22 | 2 | 2 | 0 / 0 | 13507=4926:156 | 13507=4926:156 | none | 51:blocked | N | N | N | 156 | 23 | 174 |
| 17 | 17224..31221 | 30768=828 | 1 | 453 | 3905 | 5314 | 32 | 9 | 9 | 0 / 0 | 23972=10320:189 | 23972=10320:189 | none | 141:blocked | N | N | N | 335 | 33 | 270 |
| 18 | 31222..57071 | 56827=366 | 2 | 244 | 7470 | 9771 | 39 | 12 | 13 | 0 / 0 | 33931=28312:91 | 33931=28312:91 | none | 0:fresh | N | N | N | 302 | 39 | 403 |
| 19 | 57072..99741 | 99734=19 | 3 | 7 | 11308 | 15660 | 51 | 16 | 18 | 1 / 1 | 75684=37948:35 | 75684=37948:35 | 99734=19:741 | 741:blocked | N | N | Y | 1153 | 47 | 1092 |
| 20 | 99742..181693 | 181653=61 | 3 | 40 | 22832 | 31414 | 71 | 17 | 16 | 3 / 0 | 109517=89747:58 | 109517=89747:58 | none | 0:fresh | N | N | N | 480 | 77 | 1062 |
| 21 | 181694..328255 | 328002=879 | 2 | 253 | 41894 | 54296 | 93 | 25 | 24 | 0 / 0 | 196464=165764:277 | 196464=165764:277 | none | 963:blocked | N | N | N | 996 | 107 | 2004 |
| 22 | 328256..589932 | 588583=4802 | 2 | 1349 | 75128 | 97758 | 130 | 29 | 29 | 0 / 0 | 355141=297983:1596 | 355141=297983:1596 | none | 364:blocked | N | N | N | 3387 | 130 | 4381 |
| 23 | 589933..1034838 | 1032996=3378 | 2 | 1842 | 119469 | 163259 | 158 | 68 | 65 | 0 / 0 | 633862=544865:5066 | 633862=544865:5066 | none | 58:blocked | N | N | N | 5066 | 143 | 5315 |
| 24 | 1034839..1788537 | 1787013=5329 | 2 | 1524 | 203276 | 267492 | 185 | 84 | 91 | 0 / 0 | 1099287=964428:4436 | 1099287=964428:4436 | none | 2538:blocked | N | N | N | 12160 | 182 | 9258 |
| 25 | 1788538..3225918 | 3220128=9462 | 2 | 5790 | 403064 | 543835 | 269 | 88 | 80 | 0 / 0 | 1833076=1743236:4516 | 1833076=1743236:4516 | none | 3569:blocked | N | N | N | 5568 | 272 | 17423 |
| 26 | 3225919..5784585 | 5771203=32102 | 2 | 13382 | 718529 | 958959 | 444 | 97 | 100 | 0 / 0 | 3255003=3194846:1995 | 3255003=3194846:1995 | none | 0:fresh | N | N | N | 29306 | 421 | 23712 |
| 27 | 5784586..10212210 | 10201340=18954 | 2 | 10870 | 1270213 | 1602791 | 410 | 230 | 250 | 0 / 0 | 6135064=5427582:3459 | 6135064=5427582:3459 | none | 40704:blocked | N | N | N | 56142 | 479 | 59820 |
| 28 | 10212211..18399784 | 18394609=18107 | 3 | 5175 | 2318984 | 3085167 | 653 | 196 | 210 | 1 / 1 | 10770003=9646848:25772 | 10801651=9600342:10276 | 18394609=18107:21335 | 21335:blocked | N | N | Y | 27687 | 640 | 54633 |
| 29 | 18399785..32148794 | 32144188=16114 | 3 | 4606 | 3842572 | 4931132 | 696 | 328 | 365 | 1 / 1 | 18759248=18043264:8896 | 18759248=18043264:8896 | 32144188=16114:155315 | 155315:blocked | N | N | Y | 164447 | 778 | 106289 |
| 30 | 32148795..58056875 | 58055311=4202 | 3 | 1564 | 7316473 | 9858907 | 1420 | 275 | 301 | 5 / 2 | 32511351=31786118:15141 | 32511351=31786118:15141 | 58047427=26232:44575 | 50837:blocked | N | N | N | 95170 | 1264 | 126816 |
| 31 | 58056876..101769229 | 101762018=25231 | 3 | 7211 | 11965236 | 15978226 | 1411 | 499 | 556 | 5 / 2 | 59453334=56641939:60409 | 59453334=56641939:60409 | 101743538=58171:289640 | 285620:blocked | N | N | N | 299377 | 1379 | 181958 |
| 32 | 101769230..173395919 | 173367175=60240 | 3 | 28744 | 19105500 | 25167545 | 1412 | 705 | 833 | 9 / 9 | 103663831=99876752:87622 | 103663831=99876752:87622 | 173312631=169634:513942 | 514248:blocked | N | N | N | 517338 | 1410 | 278844 |
| 33 | 173395920..302890748 | 302844912=92404 | 3 | 45836 | 35599428 | 47168382 | 2321 | 901 | 1044 | 14 / 14 | 174022458=172772169:10634 | 173397430=173394149:0 | 302738034=297415:899179 | 890434:blocked | N | N | N | 902084 | 2272 | 504410 |
| 34 | 302890749..511561220 | 511518279=92188 | 3 | 42941 | 55979450 | 72238262 | 2229 | 1458 | 1659 | 20 / 16 | 306112817=299583711:26603 | 306112817=299583711:26603 | 511307121=498703:2263317 | 2247516:blocked | N | N | N | 2268262 | 2412 | 721489 |
| 35 | 511561221..904036924 | 904032692=14804 | 3 | 4232 | 111017793 | 143461654 | 3413 | 1551 | 1706 | 18 / 18 | 512613664=510503544:5040 | 512613664=510503544:5040 | 903615930=867127:2239310 | 2258109:blocked | N | N | N | 2263980 | 3512 | 723890 |
| 36 | 904036925..1610187038 | 1610186343=2426 | 3 | 695 | 202844334 | 259599033 | 5233 | 1915 | 2164 | 33 / 31 | 906338885=901751323:4078 | 906338885=901751323:4078 | 1609443239=1574792:8200661 | 8286819:blocked | N | N | N | 8290847 | 5352 | 1323188 |
| 37 | 1610187039..2789150423 | 2789149734=2405 | 3 | 689 | 327754080 | 421893987 | 5636 | 2650 | 3020 | 44 / 31 | 1615228266=1605153127:4707 | 1615228266=1605153127:4707 | 2787920370=2552293:10587852 | 10679012:blocked | N | N | N | 10691123 | 6125 | 2786318 |
| 38 | 2789150424..4910758397 | 4910724199=89386 | 3 | 34198 | 602335220 | 773308948 | 7742 | 3473 | 3842 | 47 / 27 | 2796887475=2781392128:315375 | 2796887475=2781392128:315375 | 4908711921=4861543:20943143 | 21690744:blocked | N | N | N | 21704211 | 8045 | 4844816 |
| 39 | 4910758398..8416580354 | 8416516444=110522 | 3 | 63910 | 958574394 | 1238489809 | 8790 | 4752 | 5400 | 66 / 50 | 4914559232=4906962436:42242 | 4914559232=4906962436:42242 | 8412512202=8374765:37235892 | 37491651:blocked | N | N | N | 37500573 | 9130 | 5437352 |

Summary over the 39 arcs (from `summary.txt`):

- arcs with >= 1 comb end: 36; with >= 1 blocked comb end: 29; with >= 1 comb end with drop >= 3: 29;
  with >= 1 class-3 blocked comb end: 13.
- landing == first blocked comb end (clock and value): 0 of 39.
- landing == first comb end with drop >= 3: 0 of 39.
- landing == first class-3 blocked comb end: 3 of the 14 arcs whose landing is in class 3 (arcs 19, 28, 29;
  the other 11 class-3-landing arcs are 20 (landing fresh, no class-3 blocked comb end) and 30-39, whose
  first class-3 blocked comb end precedes the landing by 7884 (arc 30), 18480 (31), 54544 (32), 106878 (33),
  211158 (34), 416762 (35), 743104 (36), 1229364 (37), 2012278 (38), 4004242 (39) clocks; the per-arc lists
  of class-3 blocked comb ends are in `marked_comb_ends.txt`, class column = 3).
- landing is a comb end: 36 of 36 arcs with comb ends; the landing comb end is blocked in 21 arcs
  (16, 17, 19, 21-25, 27-39) and fresh in 15 (3, 5-15, 18, 20, 26).
- first blocked comb end == first comb end with drop >= 3 (same comb end): 27 of the 29 arcs with a blocked
  comb end (exceptions: arc 28, first drop>=3 at 10770003=9646848:25772 vs first blocked at
  10801651=9600342:10276; arc 33, first drop>=3 at 174022458=172772169:10634 vs first blocked at
  173397430=173394149:0).
- Open arc 40 at the horizon: start 8416580355, minimum so far 6705983634 at clock 9999999999,
  576099553 late landings so far, comb ends 1514, blocked 352, drop >= 3: 362, class-3 comb ends 0,
  Phi decreases 1539, Phi* 26706627328.

## 7. Phi decreases at level-1 clocks

Total 45859 (44320 in the 39 completed arcs, 1539 in the open arc), sum of sizes 2579391150
(mean 56246).

Size histogram (size:count): 1:71 2:14 3:78 4:20 5:22 6:23 7:14 8:16 9:30 10:15 11:15 12:19 13:23 14:17
15:17 16:15 17:15 18:20 19:12 20:13 (469 decreases of size <= 20); > 20: 45390.

Height h(m) at the decrease clock, by decade (10^d <= h < 10^(d+1), d:count): 0:1 1:7 2:30 3:101 4:394
5:1291 6:3538 7:8309 8:19720 9:12468.

Largest k between the previous level-1 clock and the decrease clock (maxk:count): 3:21316 4:18157 5:5276
6:1037 7:66 8:7. No decrease has maxk <= 2: a decrease never occurs across a stretch that stays in
k in {0, 1, 2} (pure k=1/2 ping-pong and combs).

Size-versus-gap identities checked at every decrease: with maxk = 3, size = gap/2 - 2 in 21316 of 21316;
with maxk = 4, 2*size = 3*gap - 12 in 16110 of 18157.

Most frequent (gap, maxk, size) patterns (33056 distinct; top 12 by count): (6,3,1):71 (6,4,3):52
(10,3,3):26 (14,3,5):22 (22,3,9):22 (30,3,13):21 (12,3,4):20 (118,3,57):19 (96,3,46):18 (554,3,275):18
(58,3,27):17 (48,3,22):16 (full top-40 list in `summary.txt`).

Step pattern at the decreases (the 8-step windows m-4..m+3 of the first 10 decreases, from
`decreases.txt`; columns: clock a h k r Phi(level-1 only) step candidate candidateState class; the
decrease clock is marked *):

```
decrease at clock 38 arc 6 size 1 gap 6 maxk 3
  34 113 79 3 11 - A 45 blocked -
  35 78 43 2 8 - S 78 fresh band
  36 114 78 3 6 - A 42 blocked -
  37 77 40 2 3 - S 77 fresh band
* 38 39 1 1 1 77 S 39 fresh band
  39 78 39 2 0 - A - none -
  40 38 -2 0 38 - S 38 fresh late
  41 79 38 1 38 120 A - none -
decrease at clock 110 arc 8 size 3 gap 10 maxk 3
  106 369 263 3 51 - A 157 blocked -
  107 262 155 2 48 - S 262 fresh band
  108 370 262 3 46 - A 154 blocked -
  109 261 152 2 43 - S 261 fresh band
* 110 151 41 1 41 261 S 151 fresh band
  111 40 -71 0 40 - S 40 fresh late combEnd
  112 152 40 1 40 264 A - none -
  113 265 152 2 39 - A 39 blocked -
decrease at clock 120 arc 8 size 6 gap 8 maxk 4
  116 378 262 3 30 - S 378 fresh band
  117 495 378 4 27 - A 261 blocked -
  118 377 259 3 23 - S 377 fresh band
  119 258 139 2 20 - S 258 fresh band
* 120 138 18 1 18 258 S 138 fresh band
  121 259 138 2 17 - A 17 blocked -
  122 137 15 1 15 259 S 137 fresh band
  123 260 137 2 14 - A 14 blocked -
decrease at clock 185 arc 9 size 5 gap 14 maxk 3
  181 635 454 3 92 - A 273 blocked -
  182 453 271 2 89 - S 453 fresh band
  183 636 453 3 87 - A 270 blocked -
  184 452 268 2 84 - S 452 fresh band
* 185 267 82 1 82 452 S 267 fresh band
  186 453 267 2 81 - A 81 blocked -
  187 266 79 1 79 453 S 266 fresh band
  188 454 266 2 78 - A 78 blocked -
decrease at clock 193 arc 9 size 3 gap 6 maxk 4
  189 643 454 3 76 - A 265 blocked -
  190 833 643 4 73 - A 453 blocked -
  191 642 451 3 69 - S 642 fresh band
  192 450 258 2 66 - S 450 fresh band
* 193 257 64 1 64 450 S 257 fresh band
  194 451 257 2 63 - A 63 blocked -
  195 256 61 1 61 451 S 256 fresh band
  196 60 -136 0 60 - S 60 fresh late
decrease at clock 235 arc 9 size 4 gap 12 maxk 3
  231 722 491 3 29 - A 260 blocked -
  232 490 258 2 26 - S 490 fresh band
  233 723 490 3 24 - A 257 blocked -
  234 489 255 2 21 - S 489 fresh band
* 235 254 19 1 19 489 S 254 fresh band
  236 490 254 2 18 - A 18 blocked -
  237 253 16 1 16 490 S 253 fresh band
  238 491 253 2 15 - A 15 blocked -
decrease at clock 306 arc 10 size 8 gap 20 maxk 3
  302 1097 795 3 191 - A 493 blocked -
  303 794 491 2 188 - S 794 fresh band
  304 1098 794 3 186 - A 490 blocked -
  305 793 488 2 183 - S 793 fresh band
* 306 487 181 1 181 793 S 487 fresh band
  307 180 -127 0 180 - S 180 fresh late
  308 488 180 1 180 796 A - none -
  309 179 -130 0 179 - S 179 fresh late
decrease at clock 352 arc 10 size 5 gap 14 maxk 3
  348 1186 838 3 142 - A 490 blocked -
  349 837 488 2 139 - S 837 fresh band
  350 1187 837 3 137 - A 487 blocked -
  351 836 485 2 134 - S 836 fresh band
* 352 484 132 1 132 836 S 484 fresh band
  353 837 484 2 131 - A 131 blocked -
  354 483 129 1 129 837 S 483 fresh band
  355 838 483 2 128 - A 128 blocked -
decrease at clock 420 arc 10 size 6 gap 16 maxk 3
  416 1312 896 3 64 - A 480 blocked -
  417 895 478 2 61 - S 895 fresh band
  418 1313 895 3 59 - A 477 blocked -
  419 894 475 2 56 - S 894 fresh band
* 420 474 54 1 54 894 S 474 fresh band
  421 895 474 2 53 - A 53 blocked -
  422 473 51 1 51 895 S 473 fresh band
  423 896 473 2 50 - A 50 blocked -
decrease at clock 527 arc 11 size 7 gap 18 maxk 3
  523 1940 1417 3 371 - A 894 blocked -
  524 1416 892 2 368 - S 1416 fresh band
  525 1941 1416 3 366 - A 891 blocked -
  526 1415 889 2 363 - S 1415 fresh band
* 527 888 361 1 361 1415 S 888 fresh band
  528 360 -168 0 360 - S 360 fresh late
  529 889 360 1 360 1418 A - none -
  530 359 -171 0 359 - S 359 fresh late
```

Read off the windows: with maxk = 3 the clocks between the previous level-1 clock m0 and m are
A (to k=2), A (k=2->1 candidate blocked, to k=3), then p pairs S (k=3->2, fresh band landing) A (k=2->1
candidate blocked, to k=3), then S (k=3->2) S (k=2->1) arriving at m; gap = 2p + 4 and size = p (the
identity size = gap/2 - 2 above). With maxk = 4 (e.g. clocks 113..120 and 188..193): A A A (up to k=4),
then pairs S A at k=3/4, then S S S down to k=1; 2*size = 3*gap - 12 holds in 16110 of the 18157 maxk=4
cases.

## 8. Windows around class-3 blocked comb ends

The 16-step windows c-3..c+12 of the first 4 class-3 blocked comb ends (three arc landings and the first
continued one, from `blocked_windows.txt`):

```
blocked comb end c=99734 v=19 class 3 drop 741 arc 19
  99731 99754 23 1 23 199485 S 99754 fresh band
  99732 199486 99754 2 22 - A 22 blocked -
  99733 99753 20 1 20 199486 S 99753 fresh band
* 99734 19 -99715 0 19 - S 19 fresh late combEnd
  99735 99754 19 1 19 199489 A - none -
  99736 199490 99754 2 18 - A 18 blocked -
  99737 299227 199490 3 16 - A 99753 blocked -
  99738 398965 299227 4 13 - A 199489 blocked -
  99739 498704 398965 5 9 - A 299226 blocked -
  99740 398964 299224 4 4 - S 398964 fresh band
  99741 498705 398964 5 0 - A 299223 blocked -
  99742 398963 299221 3 99737 - S 398963 fresh band
  99743 498706 398963 4 99734 - A 299220 blocked -
  99744 398962 299218 3 99730 - S 398962 fresh band
  99745 498707 398962 4 99727 - A 299217 blocked -
  99746 398961 299215 3 99723 - S 398961 fresh band
blocked comb end c=18394609 v=18107 class 3 drop 21335 arc 28
  18394606 18412717 18111 1 18111 36807323 S 18412717 fresh band
  18394607 36807324 18412717 2 18110 - A 18110 blocked -
  18394608 18412716 18108 1 18108 36807324 S 18412716 fresh band
* 18394609 18107 -18376502 0 18107 - S 18107 fresh late combEnd
  18394610 18412717 18107 1 18107 36807327 A - none -
  18394611 36807328 18412717 2 18106 - A 18106 blocked -
  18394612 55201940 36807328 3 18104 - A 18412716 blocked -
  18394613 73596553 55201940 4 18101 - A 36807327 blocked -
  18394614 55201939 36807325 3 18097 - S 55201939 fresh band
  18394615 73596554 55201939 4 18094 - A 36807324 blocked -
  18394616 55201938 36807322 3 18090 - S 55201938 fresh band
  18394617 73596555 55201938 4 18087 - A 36807321 blocked -
  18394618 55201937 36807319 3 18083 - S 55201937 fresh band
  18394619 73596556 55201937 4 18080 - A 36807318 blocked -
  18394620 55201936 36807316 3 18076 - S 55201936 fresh band
  18394621 73596557 55201936 4 18073 - A 36807315 blocked -
blocked comb end c=32144188 v=16114 class 3 drop 155315 arc 29
  32144185 32160301 16116 1 16116 64304486 S 32160301 fresh band
  32144186 16115 -32128071 0 16115 - S 16115 fresh late
  32144187 32160302 16115 1 16115 64304489 A - none -
* 32144188 16114 -32128074 0 16114 - S 16114 fresh late combEnd
  32144189 32160303 16114 1 16114 64304492 A - none -
  32144190 64304493 32160303 2 16113 - A 16113 blocked -
  32144191 96448684 64304493 3 16111 - A 32160302 blocked -
  32144192 128592876 96448684 4 16108 - A 64304492 blocked -
  32144193 96448683 64304490 3 16104 - S 96448683 fresh band
  32144194 128592877 96448683 4 16101 - A 64304489 blocked -
  32144195 96448682 64304487 3 16097 - S 96448682 fresh band
  32144196 128592878 96448682 4 16094 - A 64304486 blocked -
  32144197 96448681 64304484 3 16090 - S 96448681 fresh band
  32144198 128592879 96448681 4 16087 - A 64304483 blocked -
  32144199 96448680 64304481 3 16083 - S 96448680 fresh band
  32144200 128592880 96448680 4 16080 - A 64304480 blocked -
blocked comb end c=58047427 v=26232 class 3 drop 44575 arc 30
  58047424 58073658 26234 1 26234 116121082 S 58073658 fresh band
  58047425 26233 -58021192 0 26233 - S 26233 fresh late
  58047426 58073659 26233 1 26233 116121085 A - none -
* 58047427 26232 -58021195 0 26232 - S 26232 fresh late combEnd
  58047428 58073660 26232 1 26232 116121088 A - none -
  58047429 116121089 58073660 2 26231 - A 26231 blocked -
  58047430 174168519 116121089 3 26229 - A 58073659 blocked -
  58047431 232215950 174168519 4 26226 - A 116121088 blocked -
  58047432 174168518 116121086 3 26222 - S 174168518 fresh band
  58047433 232215951 174168518 4 26219 - A 116121085 blocked -
  58047434 174168517 116121083 3 26215 - S 174168517 fresh band
  58047435 232215952 174168517 4 26212 - A 116121082 blocked -
  58047436 174168516 116121080 3 26208 - S 174168516 fresh band
  58047437 232215953 174168516 4 26205 - A 116121079 blocked -
  58047438 174168515 116121077 3 26201 - S 174168515 fresh band
  58047439 232215954 174168515 4 26198 - A 116121076 blocked -
```

In all four the clocks c+1..c+3 are A A A (values c+v+1, 2c+v+3, 3c+v+6), the candidate 2c+v+2 at c+4 is
blocked (A), and clocks c+5.. alternate S (k=3, band) / A (k=4) with the k=3->2 candidates
2c+v-1, 2c+v-4, 2c+v-7, ... blocked at every S clock shown; the continued case (c=58047427, v=26232, arc 30)
reached its next late landing 7884 clocks later (bin b12 of the gap histogram).

## Reproduction

```bash
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/arc_potential_probe.cpp -o /tmp/arcpot
/tmp/arcpot 10000000000 OUTDIR                          # 228 s
/tmp/arcpot 10000000000 OUTDIR --watch OUTDIR/watch_values.txt   # first-visit clocks; stops at 1500189
python3 potential/crosscheck.py 1000000 OUTDIR_1e6      # independent Python check on a 10^6 run
```
