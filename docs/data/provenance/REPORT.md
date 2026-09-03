# Blocker provenance probe (H-20260903-01) — report

Date: 2026-09-03. Source: `experiments/blocker_provenance_probe.cpp` (the only file added to the
repository; nothing else touched, no `lake`, no commit). All outputs are under the scratch
directory `provenance/` (`h8/`, `h9/`, `h10/` = H = 10^8, 10^9, 10^10; each holds
`pass1_summary.txt`, `queries.txt`, `records.txt`, `summary.txt`, `stderr.log`). Every number in
this report is copied from those files (the tables are spliced in verbatim from
`h10/summary.txt`; the census in section 5 is the output of `post.sh h10/records.txt`).

## 1. Program

Two passes over the same horizon, one executable (`provenance HORIZON OUTDIR`), built with
`c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror` (Apple clang 17, clean).

**Pass 1** is the simulator core of `experiments/arc_death_rule_probe.cpp` copied with its
definitions unchanged: interval-set history, exact step rule (subtract iff a(n-1) > n and the
candidate is unvisited), Chaffin's arc detector (residue increase = wrap; arc index = wraps + 1,
first arc at clock 1), late landings, combs, comb ends, the checkpoint of the first 19 landings,
the verification a(c+3) = 3c+v+6 and "step at c+4 is an addition iff blocked", and the level-3/4
lock analysis (i_obs, J_obs, J_eff, i_gen = (T-1) + floor((J_eff+2)/3), outcomes break / wrap /
l3blocked / interrupted, the level-3/4 value and level checks). It emits one query record per
blocking event:

| kind | event | queried value w | c, v | extra columns |
|---|---|---|---|---|
| test | blocked comb end (c, v), open arc included | 2c+v+2 (visited at time c) | comb end | ex1 = i_obs, ex2 = i_gen, lock outcome |
| lockcand | lock breaks with i_obs > i_gen | 2c+v-1-3 i_gen (visited when presented at c+6+2 i_gen) | comb end | ex1 = i_obs, ex2 = i_gen |
| l3 | lock ends by l3blocked | 3c+v+5-i_obs (visited; addition at c+5+2 i_obs) | comb end | ex1 = i_obs, ex2 = i_gen |
| entry23 | fresh comb end whose candidate c+v-3 is visited at time c+4 (checked with the interval set at c+4 and cross-checked against the step type at c+5) | c+v-3 | comb end | ex1 = J_obs, ex2 = h_prev |
| bandexit | level-1 clock n (a(n) = n+h, 2 <= h <= 10^7) whose steps at n+1 and n+2 are both additions (h-1 visited, then the band value a(n)-1 visited) | a(n)-1 | c = n, v = h | ex1 = completed pairs of the run ending at n, ex2 = n - run start |

Band exits are decimated to at most 400,000 records by keeping every k-th one (k a power of two,
doubled when the buffer fills); the decimation was never triggered (6,140 exits, k = 1). Level-1
clocks followed by two additions with h > 10^7 (42,161) and with h < 2 (2; no small candidate)
are counted and excluded.

**Pass 2** reruns the orbit from clock 0 with the set of queried values in an open-addressing
hash table (linear probing, splitmix64 hash, 131,072 slots for 52,197 distinct values) behind a
2^25-bit filter. At the first clock n with a(n) = w it records n, the step type (S/A), q = w / n,
r = w % n, the arc index and arc start clock, a(n-2), a(n-1), and (through a two-clock pending
buffer) a(n+1), a(n+2). Run flags: upperRun = (a(n+2) = w+1 or a(n-2) = w-1), lowerRun =
(a(n+2) = w-1 or a(n-2) = w+1). In a level-p/(p+1) ping-pong the level-p values (reached by
subtraction) decrease by 1 and the level-(p+1) values (reached by addition) increase by 1 every
two clocks, so lowerRun / upperRun say that w is a lower / upper run value.

The passes are joined by w (a value queried by several events keeps every query record, each
joined with the single first-visit record). Two columns were added beyond the task: the arc
distance arcAtC - arcN and q relative to the event level L_kind (L = 2 for test and lockcand,
3 for l3, 1 for entry23 and bandexit), together with a generalized hypothesis (C'):
sameArc => q = L_kind and earlierArc => q > L_kind, reported next to the three original ones,
not instead of them. The split is discovery c < 10^9 / holdout 10^9 <= c < H, c being the comb
end clock (test, lockcand, l3, entry23) or the exiting level-1 clock (bandexit).

`records.txt` columns: `kind w c v T arcAtC ex1 ex2 outcome eventClock | n step q r arcN
arcStart a(n-2) a(n-1) a(n+1) a(n+2) upperRun lowerRun sameArc gap(c-n) n/c`.

## 2. Runs and validation

| H | pass 1 | pass 2 | comb ends | blocked | queries (test / lockcand / l3 / entry23 / bandexit) | unresolved |
|---|---|---|---|---|---|---|
| 10^8 | 2.0 s | 1.9 s | 5,974 | 1,887 | 10,238 (1,887 / 54 / 277 / 3,416 / 4,604) | 0 |
| 10^9 | 20 s | 19 s | 15,967 | 6,676 | 21,816 (6,676 / 237 / 1,136 / 8,036 / 5,731) | 0 |
| 10^10 | 224.7 s | 211.9 s | 44,422 | 19,738 | 52,228 (19,738 / 609 / 3,478 / 22,263 / 6,140) | 0 |

Validation of the full run (H = 10^10, `h10/summary.txt`, reproduced verbatim in section 2.1):

- Checkpoint PASS in both passes: 1=1 2=3 4=2 10=11 16=8 31=14 64=26 131=4 222=47 403=92 770=111
  1409=181 2652=150 4825=371 9078=361 16773=781 30768=828 56827=366 99734=19. Completed arcs 39,
  open arc ordinal 40, in both passes.
- Comb ends 44,422 with 19,738 blocked (1,514 comb ends and 352 blocked ones in the open arc):
  exactly the death-rule probe's counts. Lock outcomes over all blocked comb ends: break 16,252,
  wrap 8, l3blocked 3,478, interrupted 0, still active at the horizon 0.
- a(c+3) = 3c+v+6: 44,422 checked, 0 mismatches. Step at c+4 is an addition iff blocked: 44,422
  checked, 0 mismatches. Fresh comb ends: step at c+5 is an addition iff c+v-3 was visited at
  c+4: 24,684 checked, 0 mismatches. Lock checks (step c+4 addition, pair index, level-3 value,
  level-3 and level-4 levels): 0 mismatches each.
- Breaks: i_obs > i_gen 609, i_obs = i_gen 13,055, i_obs < i_gen 2,588. All 609 lockcand events
  have i_gen >= 64 (the 64-bit candidate mask of the death-rule probe cannot see them).
- Independent cross-check at H = 10^8 against `arc_death_rule_probe.cpp` run on the same horizon
  (its `comb_ends.txt`, all comb ends including the open arc): comb ends 5,974, blocked 1,887,
  break 1,606, wrap 4, l3blocked 277, breaks with i_obs > i_gen 54 — identical to pass 1.
- The H = 10^9 run reproduces the discovery split of the H = 10^10 run line by line (21,816
  queries, same tables), as it must (all first visits precede c).
- Pass 2: 52,197 distinct values, all 52,197 resolved (0 unresolved), every first visit lies
  before the clock at which the value's status mattered (0 violations), every record has a(n+2).
  349,677 of the 10^10 clocks passed the filter and hit the table.

### 2.1 Pass summaries (verbatim from `h10/summary.txt`)

```
blocker-provenance-probe horizon=10000000000 elapsed=436.632s

== pass 1 ==
pass1 horizon=10000000000 elapsed=436.632s intervals=105347 mex=1355 finalValue=16705983634
checkpoint(first 19 landings) PASS
first landings: 1=1 2=3 4=2 10=11 16=8 31=14 64=26 131=4 222=47 403=92 770=111 1409=181 2652=150 4825=371 9078=361 16773=781 30768=828 56827=366 99734=19
completed arcs=39 openArcOrdinal=40
comb ends total=44422 blocked(all)=19738 inOpenArc=1514 blockedInOpenArc=352
teeth T: T=1:5149 T=2:1998 T>=3:37275 maxT=12385428; log2 histogram (floor(log2 T):count): 0:5149 1:2042 2:191 3:134 4:225 5:385 6:636 7:976 8:1495 9:2113 10:3064 11:3749 12:4505 13:4600 14:4444 15:3792 16:2879 17:1885 18:1110 19:609 20:266 21:125 22:39 23:9
lock outcomes (all blocked comb ends): break=16252 wrap=8 l3blocked=3478 interrupted=0 none(active at horizon)=0
verification: a(c+3)=3c+v+6 checked=44422 mismatches=0; step c+4 is addition <=> blocked checked=44422 mismatches=0; fresh: step c+5 is addition <=> c+v-3 visited at c+4 checked=24684 mismatches=0
lock checks: step c+4 not addition=0 pairIndexMismatch=0 level3ValueMismatch=0 level3LevelMismatch=0 level4LevelMismatch=0
lockcand mask check (bit i_gen of the candidate mask at time c set): ok=0 notSet=0 candEqualsC+v+1=0 iGen>=64(unchecked)=609
breaks: i_obs > i_gen=609 i_obs == i_gen=13055 i_obs < i_gen=2588
queries: test=19738 lockcand=609 l3=3478 entry23=22263
band exits (2 <= h <= 10000000): total=6140 kept=6140 samplingFactor=1 (every k-th exit, ordinals 0, k, 2k, ...); level-1 clocks followed by two additions with h > cap=42161 with h < 2=2
band exits kept with >= 1 completed pair before n=647

== pass 2 ==
pass2 elapsed=211.893s intervals=105347 finalValue=16705983634
checkpoint(first 19 landings) PASS
first landings: 1=1 2=3 4=2 10=11 16=8 31=14 64=26 131=4 222=47 403=92 770=111 1409=181 2652=150 4825=371 9078=361 16773=781 30768=828 56827=366 99734=19
completed arcs=39 openArcOrdinal=40 (pass 1: 39, 40)
unique queried values=52197 tableCapacity=131072 filterBits=25 filterHits(clocks whose value passed the filter and was in the table)=349677
resolved=52197 unresolved(must be 0)=0 resolvedWithoutA(n+2)=0
queries total=52228 unresolvedQueries=0 firstVisitNotBeforeEvent(must be 0)=0

```

## 3. Tables (verbatim from h10/summary.txt)

### 3.1 Discovery (c < 10^9)

```
==== discovery (c < 10^9) ====
queries=21816 test=6676 lockcand=237 l3=1136 entry23=8036 bandexit=5731

-- kind=test --
  count=6676 sameArc=6427 earlierArc=249 firstVisitBeforeEvent=6676 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0        0     6427        2      243        1        3     6676
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0        0     6427        0        0        0        0     6427
    earlierArc          0        0        0        2      243        1        3      249
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0        0     4135        2       21        0        0     4158
    A                   0        0     2292        0      222        1        3     2518
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0        2        0        0        0        0        2
    upperOnly           0        0     2288        0      222        1        3     2514
    lowerOnly           0        0     4132        2       21        0        0     4155
    both                0        0        5        0        0        0        0        5
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0        0     6427        0        0        0        0     6427
    prev                0        0        0        2      243        1        0      246
    prev2               0        0        0        0        0        0        3        3
    older               0        0        0        0        0        0        0        0
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:2 q=L+2:243 q>=L+3:4
    sameArc    q<L:0 q=L:6427 q=L+1:0 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):0 [1/4,1/3):0 [1/3,1/2):194 [1/2,2/3):53 [2/3,1):6429 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:6482 1:194
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 3:5 4:7 5:17 6:29 7:38 8:66 9:104 10:155 11:198 12:260 13:351 14:423 15:549 16:678 17:764 18:714 19:680 20:486 21:318 22:287 23:215 24:138 25:10 26:11 27:25 28:146 29:2
  T x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    T=1                 0        0     1205        0       29        0        0     1234
    T=2                 0        0      460        0       12        0        0      472
    T>=3                0        0     4762        2      202        1        3     4970
  T x arc: T=1: sameArc=1205 earlierArc=29; T=2: sameArc=460 earlierArc=12; T>=3: sameArc=4762 earlierArc=208; 
  lock outcome x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    break               0        0     5302        2      226        1        3     5534
    wrap                0        0        6        0        0        0        0        6
    l3blocked           0        0     1119        0       17        0        0     1136
    none/other          0        0        0        0        0        0        0        0
  lock outcome x arc: break: sameArc=5302 earlierArc=232; wrap: sameArc=6 earlierArc=0; l3blocked: sameArc=1119 earlierArc=17; none/other: sameArc=0 earlierArc=0; 
    gap c-n log2 histogram (sameArc & q=2) (floor(log2(c-n)):count): 3:5 4:7 5:17 6:29 7:38 8:66 9:104 10:155 11:197 12:260 13:350 14:423 15:549 16:674 17:764 18:712 19:674 20:461 21:311 22:280 23:213 24:130 25:8

-- kind=lockcand --
  count=237 sameArc=237 earlierArc=0 firstVisitBeforeEvent=237 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0        0      237        0        0        0        0      237
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0        0      237        0        0        0        0      237
    earlierArc          0        0        0        0        0        0        0        0
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0        0      128        0        0        0        0      128
    A                   0        0      109        0        0        0        0      109
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0       20        0        0        0        0       20
    upperOnly           0        0      109        0        0        0        0      109
    lowerOnly           0        0      107        0        0        0        0      107
    both                0        0        1        0        0        0        0        1
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0        0      237        0        0        0        0      237
    prev                0        0        0        0        0        0        0        0
    prev2               0        0        0        0        0        0        0        0
    older               0        0        0        0        0        0        0        0
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:0 q=L+2:0 q>=L+3:0
    sameArc    q<L:0 q=L:237 q=L+1:0 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):0 [1/4,1/3):0 [1/3,1/2):0 [1/2,2/3):0 [2/3,1):237 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:237
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 10:3 11:5 12:11 13:21 14:35 15:41 16:38 17:30 18:24 19:13 20:7 22:5 24:4

-- kind=l3 --
  count=1136 sameArc=1081 earlierArc=55 firstVisitBeforeEvent=1136 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0        0        0     1058       23       48        7     1136
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0        0        0     1058       23        0        0     1081
    earlierArc          0        0        0        0        0       48        7       55
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0        0        0      911        7        3        1      922
    A                   0        0        0      147       16       45        6      214
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0        0        1        0        5        1        7
    upperOnly           0        0        0       18       14       38        5       75
    lowerOnly           0        0        0     1039        9        5        1     1054
    both                0        0        0        0        0        0        0        0
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0        0        0     1058       23        0        0     1081
    prev                0        0        0        0        0       48        7       55
    prev2               0        0        0        0        0        0        0        0
    older               0        0        0        0        0        0        0        0
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:0 q=L+2:48 q>=L+3:7
    sameArc    q<L:0 q=L:1058 q=L+1:23 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):0 [1/4,1/3):0 [1/3,1/2):7 [1/2,2/3):58 [2/3,1):1071 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:1129 1:7
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 4:4 5:9 6:10 7:27 8:45 9:69 10:101 11:116 12:170 13:154 14:129 15:99 16:69 17:34 18:22 19:6 21:1 22:1 23:5 24:6 25:3 26:11 27:31 28:14

-- kind=entry23 --
  count=8036 sameArc=6839 earlierArc=1197 firstVisitBeforeEvent=8036 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0     6840     1100        0       96        0        0     8036
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0     6839        0        0        0        0        0     6839
    earlierArc          0        1     1100        0       96        0        0     1197
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0     4219      557        0        5        0        0     4781
    A                   0     2621      543        0       91        0        0     3255
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0        0        0        0        0        0        0
    upperOnly           0     2625      541        0       91        0        0     3257
    lowerOnly           0     4209      559        0        5        0        0     4773
    both                0        6        0        0        0        0        0        6
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0     6839        0        0        0        0        0     6839
    prev                0        1     1100        0        0        0        0     1101
    prev2               0        0        0        0       96        0        0       96
    older               0        0        0        0        0        0        0        0
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:1 q=L+1:1100 q=L+2:0 q>=L+3:96
    sameArc    q<L:0 q=L:6839 q=L+1:0 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):2 [1/4,1/3):17 [1/3,1/2):159 [1/2,2/3):206 [2/3,1):7652 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:7857 1:177 2:2
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 1:1 2:732 3:24 4:16 5:39 6:55 7:96 8:161 9:206 10:314 11:393 12:454 13:587 14:550 15:569 16:645 17:623 18:485 19:412 20:333 21:325 22:195 23:189 24:185 25:147 26:147 27:65 28:71 29:17

-- kind=bandexit --
  count=5731 sameArc=4630 earlierArc=1101 firstVisitBeforeEvent=5731 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0     4630      802      188       98        3       10     5731
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0     4630        0        0        0        0        0     4630
    earlierArc          0        0      802      188       98        3       10     1101
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0     3615      218       15        5        0        0     3853
    A                   0     1015      584      173       93        3       10     1878
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0       19       30        0        0        1       50
    upperOnly           0     1032      319       51       83        3        9     1497
    lowerOnly           0     2480      462      107       15        0        0     3064
    both                0     1118        2        0        0        0        0     1120
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0     4630        0        0        0        0        0     4630
    prev                0        0      802        0        0        0        0      802
    prev2               0        0        0      188       98        3        0      289
    older               0        0        0        0        0        0       10       10
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:802 q=L+2:188 q>=L+3:111
    sameArc    q<L:0 q=L:4630 q=L+1:0 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):33 [1/4,1/3):177 [1/3,1/2):390 [1/2,2/3):286 [2/3,1):4845 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:5131 1:567 2:33
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 1:1776 2:359 3:12 4:35 5:53 6:88 7:128 8:202 9:227 10:325 11:314 12:328 13:295 14:213 15:184 16:130 17:100 18:104 19:107 20:74 21:151 22:75 23:146 24:57 25:24 26:54 27:46 28:58 29:66

-- all kinds --
  count=21816 sameArc=19214 earlierArc=2602 firstVisitBeforeEvent=21816 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0    11470     8566     1248      460       52       20    21816
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0    11469     6664     1058       23        0        0    19214
    earlierArc          0        1     1902      190      437       52       20     2602
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0     7834     5038      928       38        3        1    13842
    A                   0     3636     3528      320      422       49       19     7974
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0       41       31        0        5        2       79
    upperOnly           0     3657     3257       69      410       42       17     7452
    lowerOnly           0     6689     5260     1148       50        5        1    13153
    both                0     1124        8        0        0        0        0     1132
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0    11469     6664     1058       23        0        0    19214
    prev                0        1     1902        2      243       49        7     2204
    prev2               0        0        0      188      194        3        3      388
    older               0        0        0        0        0        0       10       10
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:1 q=L+1:1904 q=L+2:479 q>=L+3:218
    sameArc    q<L:0 q=L:19191 q=L+1:23 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):35 [1/4,1/3):194 [1/3,1/2):750 [1/2,2/3):603 [2/3,1):20234 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:20836 1:945 2:35
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 1:1777 2:1091 3:41 4:62 5:118 6:182 7:289 8:474 9:606 10:898 11:1026 12:1223 13:1408 14:1350 15:1442 16:1560 17:1551 18:1349 19:1218 20:900 21:795 22:563 23:555 24:390 25:184 26:223 27:167 28:289 29:85

-- hypotheses --
(A) every blocking value first visited at level q >= 2: FAIL (violations=11470 of 21816)
(B) every blocking value in a ping-pong run at its first visit (upperRun or lowerRun): FAIL (violations=79 of 21816)
(C) sameArc => q = 2 and earlierArc => q >= 3: FAIL (sameArc & q != 2: 12550; earlierArc & q <= 2: 1903; of 21816)
(C') generalized: sameArc => q = L_kind and earlierArc => q > L_kind (L = 2 test/lockcand, 3 l3, 1 entry23/bandexit): FAIL (violations=24 of 21816)
    per kind violations (A / B / sameArc&q!=2 / earlierArc&q<=2 / C'): test=0/2/0/0/0 lockcand=0/20/0/0/0 l3=0/7/1081/0/23 entry23=6840/0/6839/1101/1 bandexit=4630/50/4630/802/0

```

### 3.2 Holdout (10^9 <= c < 10^10)

```
==== holdout (10^9 <= c < H) ====
queries=30412 test=13062 lockcand=372 l3=2342 entry23=14227 bandexit=409

-- kind=test --
  count=13062 sameArc=12521 earlierArc=541 firstVisitBeforeEvent=13062 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0        0    12521        0      534        3        4    13062
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0        0    12521        0        0        0        0    12521
    earlierArc          0        0        0        0      534        3        4      541
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0        0     7885        0       63        0        1     7949
    A                   0        0     4636        0      471        3        3     5113
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0        2        0        0        0        0        2
    upperOnly           0        0     4639        0      471        3        3     5116
    lowerOnly           0        0     7878        0       63        0        1     7942
    both                0        0        2        0        0        0        0        2
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0        0    12521        0        0        0        0    12521
    prev                0        0        0        0      534        3        0      537
    prev2               0        0        0        0        0        0        4        4
    older               0        0        0        0        0        0        0        0
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:0 q=L+2:534 q>=L+3:7
    sameArc    q<L:0 q=L:12521 q=L+1:0 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):0 [1/4,1/3):0 [1/3,1/2):440 [1/2,2/3):101 [2/3,1):12521 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:12622 1:440
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 3:5 4:1 5:2 6:6 7:20 8:19 9:60 10:78 11:113 12:211 13:290 14:427 15:598 16:740 17:946 18:1218 19:1473 20:1609 21:1266 22:1003 23:714 24:498 25:496 26:378 27:266 28:86 29:50 30:122 31:351 32:16
  T x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    T=1                 0        0     2143        0       44        1        0     2188
    T=2                 0        0      831        0       14        0        0      845
    T>=3                0        0     9547        0      476        2        4    10029
  T x arc: T=1: sameArc=2143 earlierArc=45; T=2: sameArc=831 earlierArc=14; T>=3: sameArc=9547 earlierArc=482; 
  lock outcome x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    break               0        0    10243        0      470        1        4    10718
    wrap                0        0        2        0        0        0        0        2
    l3blocked           0        0     2276        0       64        2        0     2342
    none/other          0        0        0        0        0        0        0        0
  lock outcome x arc: break: sameArc=10243 earlierArc=475; wrap: sameArc=2 earlierArc=0; l3blocked: sameArc=2276 earlierArc=66; none/other: sameArc=0 earlierArc=0; 
    gap c-n log2 histogram (sameArc & q=2) (floor(log2(c-n)):count): 3:5 4:1 5:2 6:6 7:20 8:19 9:60 10:78 11:113 12:211 13:290 14:427 15:598 16:740 17:946 18:1218 19:1473 20:1609 21:1266 22:1003 23:714 24:498 25:496 26:378 27:266 28:84

-- kind=lockcand --
  count=372 sameArc=371 earlierArc=1 firstVisitBeforeEvent=372 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0        0      371        0        1        0        0      372
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0        0      371        0        0        0        0      371
    earlierArc          0        0        0        0        1        0        0        1
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0        0      200        0        1        0        0      201
    A                   0        0      171        0        0        0        0      171
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0       29        0        1        0        0       30
    upperOnly           0        0      171        0        0        0        0      171
    lowerOnly           0        0      171        0        0        0        0      171
    both                0        0        0        0        0        0        0        0
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0        0      371        0        0        0        0      371
    prev                0        0        0        0        1        0        0        1
    prev2               0        0        0        0        0        0        0        0
    older               0        0        0        0        0        0        0        0
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:0 q=L+2:1 q>=L+3:0
    sameArc    q<L:0 q=L:371 q=L+1:0 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):0 [1/4,1/3):0 [1/3,1/2):1 [1/2,2/3):0 [2/3,1):371 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:371 1:1
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 11:1 12:8 13:10 14:24 15:36 16:49 17:62 18:59 19:38 20:31 21:25 22:17 23:5 24:3 25:2 28:1 31:1

-- kind=l3 --
  count=2342 sameArc=2290 earlierArc=52 firstVisitBeforeEvent=2342 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0        0        0     2190      100       48        4     2342
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0        0        0     2190      100        0        0     2290
    earlierArc          0        0        0        0        0       48        4       52
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0        0        0     1875        4        0        0     1879
    A                   0        0        0      315       96       48        4      463
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0        0        0        0        1        0        1
    upperOnly           0        0        0       43       93       42        4      182
    lowerOnly           0        0        0     2147        7        5        0     2159
    both                0        0        0        0        0        0        0        0
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0        0        0     2190      100        0        0     2290
    prev                0        0        0        0        0       48        4       52
    prev2               0        0        0        0        0        0        0        0
    older               0        0        0        0        0        0        0        0
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:0 q=L+2:48 q>=L+3:4
    sameArc    q<L:0 q=L:2190 q=L+1:100 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):0 [1/4,1/3):0 [1/3,1/2):4 [1/2,2/3):135 [2/3,1):2203 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:2338 1:4
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 4:1 5:4 6:5 7:9 8:16 9:37 10:67 11:86 12:155 13:237 14:347 15:366 16:308 17:257 18:161 19:92 20:23 21:14 22:5 28:1 29:56 30:42 31:53

-- kind=entry23 --
  count=14227 sameArc=12465 earlierArc=1762 firstVisitBeforeEvent=14227 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0    12465     1501        0      260        0        1    14227
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0    12465        0        0        0        0        0    12465
    earlierArc          0        0     1501        0      260        0        1     1762
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0     6585      967        0       36        0        0     7588
    A                   0     5880      534        0      224        0        1     6639
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0        0        0        0        0        0        0
    upperOnly           0     5883      534        0      224        0        1     6642
    lowerOnly           0     6561      967        0       36        0        0     7564
    both                0       21        0        0        0        0        0       21
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0    12465        0        0        0        0        0    12465
    prev                0        0     1501        0        0        0        0     1501
    prev2               0        0        0        0      260        0        0      260
    older               0        0        0        0        0        0        1        1
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:1501 q=L+2:0 q>=L+3:261
    sameArc    q<L:0 q=L:12465 q=L+1:0 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):3 [1/4,1/3):43 [1/3,1/2):359 [1/2,2/3):370 [2/3,1):13452 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:13822 1:402 2:3
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 2:1491 3:21 4:4 5:7 6:8 7:18 8:32 9:60 10:106 11:169 12:283 13:425 14:627 15:763 16:968 17:1282 18:1400 19:1243 20:1084 21:934 22:666 23:453 24:262 25:123 26:71 27:100 28:426 29:446 30:429 31:245 32:81

-- kind=bandexit --
  count=409 sameArc=391 earlierArc=18 firstVisitBeforeEvent=409 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0      391       14        0        4        0        0      409
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0      391        0        0        0        0        0      391
    earlierArc          0        0       14        0        4        0        0       18
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0      368        4        0        0        0        0      372
    A                   0       23       10        0        4        0        0       37
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0        3        0        0        0        0        3
    upperOnly           0       23        1        0        3        0        0       27
    lowerOnly           0      135       10        0        1        0        0      146
    both                0      233        0        0        0        0        0      233
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0      391        0        0        0        0        0      391
    prev                0        0       14        0        0        0        0       14
    prev2               0        0        0        0        4        0        0        4
    older               0        0        0        0        0        0        0        0
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:14 q=L+2:0 q>=L+3:4
    sameArc    q<L:0 q=L:391 q=L+1:0 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):4 [1/4,1/3):0 [1/3,1/2):14 [1/2,2/3):0 [2/3,1):391 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:391 1:14 2:4
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 1:256 2:46 3:1 5:1 6:4 7:13 8:19 9:6 10:17 11:17 12:7 13:3 14:1 29:2 31:10 32:6

-- all kinds --
  count=30412 sameArc=28038 earlierArc=2374 firstVisitBeforeEvent=30412 (must equal count)
  level q at the first visit:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    all                 0    12856    14407     2190      899       51        9    30412
  sameArc x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    sameArc             0    12856    12892     2190      100        0        0    28038
    earlierArc          0        0     1515        0      799       51        9     2374
  step type x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    S                   0     6953     9056     1875      104        0        1    17989
    A                   0     5903     5351      315      795       51        8    12423
  run class x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    neither             0        0       34        0        1        1        0       36
    upperOnly           0     5906     5345       43      791       45        8    12138
    lowerOnly           0     6696     9026     2147      107        5        1    17982
    both                0      254        2        0        0        0        0      256
  arc distance (arcAtC - arcN) x q:
                      q=0      q=1      q=2      q=3      q=4      q=5     q>=6    total
    same                0    12856    12892     2190      100        0        0    28038
    prev                0        0     1515        0      535       51        4     2105
    prev2               0        0        0        0      264        0        4      268
    older               0        0        0        0        0        0        1        1
  q relative to the event level L (L=2 test/lockcand, 3 l3, 1 entry23/bandexit):
    earlierArc q<L:0 q=L:0 q=L+1:1515 q=L+2:583 q>=L+3:276
    sameArc    q<L:0 q=L:27938 q=L+1:100 q=L+2:0 q>=L+3:0
  n/c histogram: [0,1/8):0 [1/8,1/4):7 [1/4,1/3):43 [1/3,1/2):818 [1/2,2/3):606 [2/3,1):28938 [1,inf):0
    c/n log2 histogram (floor(log2(c/n)):count): 0:29544 1:861 2:7
    gap c-n log2 histogram (all) (floor(log2(c-n)):count): 1:256 2:1537 3:27 4:6 5:14 6:23 7:60 8:86 9:163 10:268 11:386 12:664 13:965 14:1426 15:1763 16:2065 17:2547 18:2838 19:2846 20:2747 21:2239 22:1691 23:1172 24:763 25:621 26:449 27:366 28:514 29:554 30:593 31:660 32:103

-- hypotheses --
(A) every blocking value first visited at level q >= 2: FAIL (violations=12856 of 30412)
(B) every blocking value in a ping-pong run at its first visit (upperRun or lowerRun): FAIL (violations=36 of 30412)
(C) sameArc => q = 2 and earlierArc => q >= 3: FAIL (sameArc & q != 2: 15146; earlierArc & q <= 2: 1515; of 30412)
(C') generalized: sameArc => q = L_kind and earlierArc => q > L_kind (L = 2 test/lockcand, 3 l3, 1 entry23/bandexit): FAIL (violations=100 of 30412)
    per kind violations (A / B / sameArc&q!=2 / earlierArc&q<=2 / C'): test=0/2/0/0/0 lockcand=0/30/0/0/0 l3=0/1/2290/0/100 entry23=12465/0/12465/1501/0 bandexit=391/3/391/14/0

```

## 4. Exception listings (from h10/summary.txt; columns as in records.txt)

The (B) and (C') lists are shown in full up to the 50-per-list cap of summary.txt (the holdout (C') list has 100 entries, the first 50 are shown); for the three large lists ((A) q <= 1, sameArc & q != 2, earlierArc & q <= 2) only the first 5 lines are shown here, the first 50 are in summary.txt.

```
==== discovery (c < 10^9) ====
  [q <= 1 (first visit at level 0 or 1)] total=11470
    entry23 3 4 2 1 3 0 1 none 9 | 2 A 1 1 2 2 0 1 6 2 0 1 0 2 0.500000
    entry23 87 64 26 13 7 0 1 none 69 | 57 A 1 30 7 40 86 30 29 88 1 0 1 7 0.890625
    entry23 160 99 64 12 8 0 26 none 104 | 92 A 1 68 8 77 159 68 67 161 1 0 1 7 0.929293
    entry23 282 170 115 18 9 0 133 none 175 | 163 A 1 119 9 135 281 119 118 283 1 0 1 7 0.958824
    entry23 266 222 47 14 9 1 64 none 227 | 187 S 1 79 9 135 267 453 454 643 0 1 1 35 0.842342
  [run class = neither] total=79
    l3 755074 196464 165764 232 21 87 232 none 196643 | 139568 A 5 57234 20 99742 475939 615506 615505 475935 0 0 0 56896 0.710400
    l3 1586743 474903 162192 630 22 163 634 none 475234 | 310877 A 5 32358 21 181694 964990 1275866 1275865 964986 0 0 0 164026 0.654612
    l3 4959606 1510767 427394 2095 24 94 2095 none 1510960 | 969579 A 5 111711 23 589933 3020449 3990027 3990026 3020445 0 0 0 541188 0.641779
    l3 86011640 24884528 11360620 6118 29 2569 6118 none 24889671 | 16617136 A 5 2925960 28 10212211 52777369 69394504 69394503 52777365 0 0 0 8267392 0.667770
    lockcand 115253662 56097953 3059701 551 30 649 648 none 56099255 | 56087771 S 2 3078120 30 32148795 227429203 171341433 59165890 3078117 0 0 1 10182 0.999818
    test 197451461 88958070 19535319 5 31 152 152 break 88958074 | 88953754 S 2 19543953 31 58056876 375358968 286405215 108497706 19543950 0 0 1 4316 0.999951
    lockcand 337511043 141199809 55178431 20646 32 22337 22335 none 141244485 | 140416317 S 2 56678409 32 101769230 618343676 477927360 197094725 56678406 0 0 1 783492 0.994451
    lockcand 337495458 143363715 50826598 17799 32 19552 19523 none 143402767 | 142902027 S 2 51691404 32 101769230 623299511 480397485 194593430 51691401 0 0 1 461688 0.996780
    lockcand 340979001 154260897 32505187 14086 32 19828 15993 none 154292889 | 153778497 S 2 33422007 32 101769230 648535994 494757498 187200503 33422004 0 0 1 482400 0.996873
    lockcand 346927812 171962727 3005704 1 32 1116 1115 none 171964963 | 171952679 S 2 3022454 32 101769230 690833169 518880491 174975132 3022451 0 0 1 10048 0.999942
    test 587411886 262814448 61782988 1 33 0 197 l3blocked 262814452 | 262700760 S 2 62010366 33 173395920 1112813405 850112646 324711125 62010363 0 0 1 113688 0.999567
    lockcand 604903257 287302248 30331414 9165 33 11423 10884 none 287324022 | 287153262 S 2 30596733 33 173395920 1179209780 892056519 317749994 30596730 0 0 1 148986 0.999481
    lockcand 606095009 297645184 10805620 250 33 327 326 none 297645842 | 297633606 S 2 10827797 33 173395920 1201362220 903728615 308461402 10827794 0 0 1 11578 0.999961
    lockcand 998078210 407843549 182423459 5994 34 10831 10782 none 407865119 | 407388943 S 2 183300324 34 302890749 1812856095 1405467153 590689266 183300321 0 0 1 454606 0.998885
    lockcand 997862605 420395283 157182386 34921 34 48725 36782 none 420468853 | 419009121 S 2 159844363 34 302890749 1835880846 1416871726 578853483 159844360 0 0 1 1386162 0.996703
    lockcand 1017511891 454519223 108475132 392 34 563 562 none 454520353 | 454509457 S 2 108492977 34 302890749 1926530804 1472021348 563002433 108492974 0 0 1 9766 0.999979
    lockcand 1017384007 462833003 91760662 1 34 14221 14220 none 462861449 | 462702885 S 2 91978237 34 302890749 1942789776 1480086892 554681121 91978234 0 0 1 130118 0.999719
    lockcand 1017341094 465302291 86775660 1 34 16017 13049 none 465328395 | 464929007 S 2 87483080 34 302890749 1947199107 1482270101 552412086 87483077 0 0 1 373284 0.999198
    lockcand 1025003598 481851785 61347819 15692 34 15931 15930 none 481883651 | 481766575 S 2 61470448 34 302890749 1988536747 1506770173 543237022 61470445 0 0 1 85210 0.999823
    lockcand 1024827282 484278821 56291415 6239 34 7259 7258 none 484293343 | 484172195 S 2 56482892 34 302890749 1993171671 1508999477 540655086 56482889 0 0 1 106626 0.999780
    lockcand 1024545003 492902079 38752252 3760 34 7427 3802 none 492909689 | 492852893 S 2 38839217 34 302890749 2010250788 1517397896 531692109 38839214 0 0 1 49186 0.999900
    lockcand 1023891943 497257509 29385983 2248 34 3020 3019 none 497263553 | 497137241 S 2 29617461 34 302890749 2018166424 1521029184 1521029185 2018166428 0 0 1 120268 0.999758
    l3 2374550308 685041102 319433477 18302 35 6480 20211 none 685054067 | 684890827 S 3 319877827 35 511561221 3744331961 3059441135 1689659480 1004768651 0 0 1 150275 0.999781
    l3 2384430473 695012586 299414003 47412 35 21293 49248 none 695055177 | 455653890 A 5 106161023 34 302890749 1473122694 1928776583 1928776582 1473122690 0 0 0 239358696 0.655605
    lockcand 1688996420 701419512 286161132 2 35 1246 1245 none 701422008 | 700732356 S 2 287531708 35 511561221 3090461131 2389728776 988264063 287531705 0 0 1 687156 0.999020
    lockcand 1743676828 763433888 216838906 8420 35 9953 9951 none 763453796 | 763177056 S 2 217322716 35 511561221 3270030939 2506853884 980499771 217322713 0 0 1 256832 0.999664
    lockcand 1794971775 834619308 125741944 2657 35 2929 2928 none 834625170 | 834599654 S 2 125772467 35 511561221 3464171082 2629571429 960372120 125772464 0 0 1 19654 0.999976
    lockcand 1810144491 874139560 61886864 7132 35 7165 7164 none 874153894 | 874091306 S 2 61961879 35 511561221 3558327102 2684235797 936053184 61961876 0 0 1 48254 0.999945
    l3 2690434471 880765788 48147280 10507 35 10178 12553 none 880786149 | 423159169 A 6 151479457 34 302890749 1844116134 2267275302 2267275301 1844116130 0 0 0 457606619 0.480445
    bandexit 2929 2087 843 0 13 1 2 none 2089 | 1361 S 2 207 12 845 5650 4290 1567 204 0 0 0 726 0.652132
    bandexit 188239 169540 18700 0 20 1 2 none 169542 | 81238 S 2 25763 19 57072 350714 269477 107000 25760 0 0 0 88302 0.479167
    bandexit 615289 551820 63470 0 22 0 0 none 551822 | 261934 S 2 91421 21 181694 1139156 877223 353354 91418 0 0 0 289886 0.474673
    bandexit 2023226 1422342 600885 0 24 0 0 none 1422344 | 923576 S 2 176074 23 589933 3870377 2946802 1099649 176071 0 0 0 498766 0.649335
    bandexit 1812337 1763800 48538 0 24 0 0 none 1763802 | 638386 S 2 535565 23 589933 3089108 2450723 2450724 3089112 0 0 0 1125414 0.361938
    bandexit 3405234 2905889 499346 0 25 148 296 none 2905891 | 559263 A 6 49656 22 328256 2286709 2845971 2845970 2286705 0 0 0 2346626 0.192458
    bandexit 6073165 5265604 807562 0 26 0 0 none 5265606 | 2603018 S 2 867129 25 1788538 11279200 8676183 3470146 867126 0 0 0 2662586 0.494344
    bandexit 5822770 5746838 75933 0 26 0 0 none 5746840 | 2268352 S 2 1286066 25 1788538 10359473 8091122 3554417 1286063 0 0 0 3478486 0.394713
    bandexit 10749943 9698107 1051837 0 27 1 2 none 9698109 | 4492025 S 2 1765893 26 3225919 19733992 15241968 6257917 1765890 0 0 0 5206082 0.463186
    bandexit 10228282 10192709 35574 0 27 1337 2674 none 10192711 | 3854363 S 2 2519556 26 3225919 17937007 14082645 6373918 2519553 0 0 0 6338346 0.378149
    bandexit 19411834 16973746 2438089 0 28 1 2 none 16973748 | 8143444 S 2 3124946 27 5784586 35698721 27555278 11268389 3124943 0 0 0 8830302 0.479767
    bandexit 18966588 17693130 1273459 0 28 0 0 none 17693132 | 7485632 S 2 3995324 27 5784586 33937851 26452220 11480955 3995321 0 0 0 10207498 0.423081
    bandexit 34477920 29277517 5200404 0 29 3 6 none 29277519 | 14308695 S 2 5860530 28 10212211 63095309 48786615 20169224 5860527 0 0 0 14968822 0.488726
    bandexit 32280813 32019371 261443 0 29 0 0 none 32019373 | 11903165 S 2 8474483 28 10212211 56087142 44183978 20377647 8474480 0 0 0 20116206 0.371749
    bandexit 61068175 52090084 8978092 0 30 9783 19566 none 52090086 | 25635774 S 2 9796627 29 18399785 112339722 86703949 35432400 9796624 0 0 0 26454310 0.492143
    bandexit 59540280 55358514 4181767 0 30 900 1800 none 55358516 | 23102640 S 2 13335000 29 18399785 105745559 82642920 36437639 13334997 0 0 0 32255874 0.417328
    bandexit 105481450 96359537 9121914 0 31 1 2 none 96359539 | 41792967 S 2 21895516 30 32148795 189067383 147274417 63688482 21895513 0 0 0 54566570 0.433719
    bandexit 178125598 169074114 9051485 0 32 1 2 none 169074116 | 62667964 S 2 52789670 31 58056876 303461525 240793562 115457633 52789667 0 0 0 106406150 0.370654
    bandexit 176891177 170270252 6620926 0 32 1798 3596 none 170270254 | 61163666 S 2 54563845 31 58056876 299218508 238054843 115727510 54563842 0 0 0 109106586 0.359215
    bandexit 174138515 172687300 1451216 0 32 0 0 none 172687302 | 58027442 S 3 56189 30 32148795 290193398 232165957 116111072 58083628 0 0 0 114659858 0.336026
    bandexit 173978358 172844326 1134033 0 32 1018 2036 none 172844328 | 57849380 A 3 430218 30 32148795 58279599 116128978 116128977 58279595 0 0 0 114994946 0.334691
  [sameArc with q != 2] total=12550
    entry23 87 64 26 13 7 0 1 none 69 | 57 A 1 30 7 40 86 30 29 88 1 0 1 7 0.890625
    entry23 160 99 64 12 8 0 26 none 104 | 92 A 1 68 8 77 159 68 67 161 1 0 1 7 0.929293
    entry23 282 170 115 18 9 0 133 none 175 | 163 A 1 119 9 135 281 119 118 283 1 0 1 7 0.958824
    entry23 266 222 47 14 9 1 64 none 227 | 187 S 1 79 9 135 267 453 454 643 0 1 1 35 0.842342
    entry23 511 285 229 19 10 6 19 none 290 | 278 A 1 233 10 249 510 233 232 512 1 0 1 7 0.975439
  [earlierArc with q <= 2] total=1903
    entry23 3 4 2 1 3 0 1 none 9 | 2 A 1 1 2 2 0 1 6 2 0 1 0 2 0.500000
    entry23 21 16 8 3 5 1 4 none 21 | 9 A 2 3 4 7 20 12 11 22 1 0 0 7 0.562500
    entry23 42 31 14 5 6 0 19 none 36 | 20 S 2 2 5 12 43 62 63 41 0 1 0 11 0.645161
    entry23 492 403 92 19 10 7 132 none 408 | 228 S 2 36 9 135 493 720 721 491 0 1 0 175 0.565757
    entry23 909 508 404 22 11 0 426 none 513 | 449 A 2 11 10 249 908 460 459 910 1 0 0 59 0.883858
  [generalized (C'): sameArc with q != L_kind or earlierArc with q <= L_kind] total=24
    entry23 3 4 2 1 3 0 1 none 9 | 2 A 1 1 2 2 0 1 6 2 0 1 0 2 0.500000
    l3 2950311 925982 172451 399 23 91 399 none 926169 | 590322 A 4 589023 23 589933 2950310 2359989 2359988 1769664 1 0 1 335660 0.637509
    l3 3088467 1020800 26062 71 23 0 111 none 1020805 | 637102 A 4 540059 23 589933 3088466 2451365 2451364 3088468 1 0 1 383698 0.624120
    l3 3088162 1021266 24359 1 23 0 15 none 1021271 | 636492 A 4 542194 23 589933 3088161 2451670 2451669 3088163 1 0 1 384774 0.623238
    l3 30233632 9782006 889651 2236 27 2042 2236 none 9786095 | 6235652 A 4 5291024 27 5784586 30233631 23997980 23997979 17762325 1 0 1 3546354 0.637461
    l3 95191377 30788980 2824658 1 29 226 781 none 30789437 | 19506434 A 4 17165641 29 18399785 95191376 75684943 75684942 56178506 1 0 1 11282546 0.633552
    l3 95370742 30930994 2596951 15844 29 19196 20354 none 30969391 | 19569292 A 4 17093574 29 18399785 95370741 75801450 75801449 56232155 1 0 1 11361702 0.632676
    l3 165131577 51941165 9309581 1543 30 1504 1543 none 51944178 | 33659693 A 4 30492805 30 32148795 97812192 131471884 198791271 165131576 0 1 1 18281472 0.648035
    l3 168257529 54082121 6011161 1 30 0 16 none 54082126 | 34708521 A 4 29423445 30 32148795 168257528 133549008 133549007 168257530 1 0 1 19373600 0.641774
    l3 172375272 56782147 2028826 43 30 0 43 none 56782152 | 36130267 S 4 27854204 30 32148795 172375273 208505539 208505540 172375271 0 1 1 20651880 0.636296
    l3 299468337 97169456 7959964 232 31 0 6140 none 97169461 | 61271362 A 4 54382889 31 58056876 299468336 238196975 238196974 299468338 1 0 1 35898094 0.630562
    l3 899150347 292543292 21525248 29325 33 4782 29325 none 292552861 | 184353794 A 4 161735171 33 173395920 530442760 714796553 1083504142 899150346 0 1 1 108189498 0.630176
    l3 1519264297 495125809 33886865 4655 34 0 5868 none 495125814 | 304521641 S 4 301177733 34 302890749 1519264298 1823785938 1823785939 1519264296 0 1 1 190604168 0.615039
    l3 1519266647 495139493 33848163 2 34 0 826 none 495139498 | 304516941 S 4 301198883 34 302890749 1519266648 1823783588 1823783589 1519266646 0 1 1 190622552 0.615012
    l3 1519286688 495155951 33818830 5117 34 0 5327 none 495155956 | 304476859 S 4 301379252 34 302890749 1519286689 1823763547 1823763548 1519286687 0 1 1 190679092 0.614911
    l3 1519263557 495213761 33622269 97 34 0 97 none 495213766 | 304523121 S 4 301171073 34 302890749 1519263558 1823786678 1823786679 1519263556 0 1 1 190690640 0.614933
    l3 1519280643 495228441 33595315 1312 34 0 1758 none 495228446 | 304488949 S 4 301324847 34 302890749 1519280644 1823769592 1823769593 1519280642 0 1 1 190739492 0.614845
    l3 1520272506 496335427 31266220 391 34 0 4720 none 496335432 | 304847399 S 4 300882910 34 302890749 1520272507 1825119905 1825119906 1520272505 0 1 1 191488028 0.614196
    l3 1530000725 506458397 10628245 1 34 2716 2511 none 506463834 | 308175561 A 4 297298481 34 302890749 1530000724 1221825164 1221825163 913649600 1 0 1 198282836 0.608491
    l3 1532937263 509768977 3630327 1328 34 0 3545 none 509768982 | 309167217 A 4 296268395 34 302890749 1532937262 1223770046 1223770045 1532937264 1 0 1 200601760 0.606485
    l3 2563313030 796465380 173917020 1186 35 135 1186 none 796465655 | 513433488 A 4 509579078 35 511561221 2563313029 2049879542 2049879541 1536446051 1 0 1 283031892 0.644640
    l3 2564157028 796939734 173338683 569 35 862 2870 none 796941463 | 513720852 A 4 509273620 35 511561221 2564157027 2050436176 2050436175 1536715321 1 0 1 283218882 0.644617
    l3 2626339971 832500932 128837170 4144 35 0 46513 none 832500937 | 534692654 A 4 487569355 35 511561221 2626339970 2091647317 2091647316 2626339972 1 0 1 297808278 0.642273
    l3 2626648728 832891130 127975333 16968 35 0 21284 none 832891135 | 534836972 A 4 487300840 35 511561221 2626648727 2091811756 2091811755 2626648729 1 0 1 298054158 0.642145
==== holdout (10^9 <= c < H) ====
  [q <= 1 (first visit at level 0 or 1)] total=12856
    entry23 1802530080 1001775975 800754108 16949 36 0 800771057 none 1001775980 | 1000373092 A 1 802156988 36 904036925 1802530079 802156988 802156987 1802530081 1 0 1 1402883 0.998600
    entry23 1802516026 1001794975 800721054 3373 36 476 800725855 none 1001794980 | 1001274136 A 1 801241890 36 904036925 1802516025 801241890 801241889 1802516027 1 0 1 520839 0.999480
    entry23 1802533856 1001839639 800694220 21206 36 0 800715426 none 1001839644 | 1000380644 A 1 802153212 36 904036925 1802533855 802153212 802153211 1802533857 1 0 1 1458995 0.998544
    entry23 1802530091 1001888853 800641241 17490 36 47 800658872 none 1001888858 | 1000373114 A 1 802156977 36 904036925 1802530090 802156977 802156976 1802530092 1 0 1 1515739 0.998487
    entry23 1802516017 1001907349 800608671 3417 36 0 800612088 none 1001907354 | 1001274118 A 1 801241899 36 904036925 1802516016 801241899 801241898 1802516018 1 0 1 633231 0.999368
  [run class = neither] total=36
    lockcand 3153946696 1415142025 323671749 2879 36 7467 3034 none 1415148099 | 1415087023 S 2 323772650 36 904036925 5984120741 4569033719 4569033720 5984120745 0 0 1 55002 0.999961
    lockcand 3224115842 1531077693 161986449 2 36 8665 8664 none 1531095027 | 1530747495 S 2 162620852 36 904036925 6285610831 4754863337 1693368346 162620849 0 0 1 330198 0.999784
    lockcand 3224115836 1531866989 160443905 17846 36 20683 20682 none 1531908359 | 1531726475 S 2 160662886 36 904036925 6287568785 4755842311 1692389360 160662883 0 0 1 140514 0.999908
    lockcand 3228099589 1559113557 109898693 7002 36 8740 8739 none 1559131041 | 1559056701 S 2 109986187 36 904036925 6346212990 4787156290 1669042887 109986184 0 0 1 56856 0.999964
    lockcand 3227090463 1566976901 93151959 4014 36 5100 5099 none 1566987105 | 1566907029 S 2 93276405 36 904036925 6360904520 4793997492 1660183433 93276402 0 0 1 69872 0.999955
    lockcand 3226942107 1569880335 87326224 41863 36 48265 48262 none 1569976865 | 1569508473 S 2 87925161 36 904036925 6365959052 4796450580 1657433633 87925158 0 0 1 371862 0.999763
    lockcand 5342865031 2166548942 1009813465 6052 37 15440 15439 none 2166579826 | 2166311838 S 2 1010241355 37 1610187039 9675488706 7509176869 3176553192 1010241352 0 0 1 237104 0.999891
    lockcand 5342798476 2171302116 1000542374 113802 37 117517 116043 none 2171534208 | 2170797376 S 2 1001203724 37 1610187039 9684393227 7513595852 3172001099 1001203721 0 0 1 504740 0.999768
    lockcand 5455669320 2414392124 627245340 74162 37 122642 120089 none 2414632308 | 2410727904 S 2 634213512 37 1610187039 10277125127 7866397224 3044941415 634213509 0 0 1 3664220 0.998482
    lockcand 5474713048 2443521274 587675529 1 37 1677 1676 none 2443524632 | 2443489208 S 2 587734632 37 1610187039 10361691463 7918202256 3031223839 587734629 0 0 1 32066 0.999987
    test 5586872546 2649815396 287241752 1 37 0 1 l3blocked 2649815400 | 2649801916 S 2 287268714 37 1610187039 10886476377 8236674462 2937070629 287268711 0 0 1 13480 0.999995
    lockcand 5581209644 2745044622 91201407 5050 37 27003 27002 none 2745098632 | 2744888644 S 2 91432356 37 1610187039 11070986931 8326098288 2836320999 91432353 0 0 1 155978 0.999943
    l3 11911159998 3178449881 2375812951 22520 38 2601 22520 none 3178455088 | 2189737367 A 5 962473163 37 1610187039 7531685265 9721422631 9721422630 7531685261 0 0 0 988712514 0.688932
    lockcand 9254928418 3860969487 1533119738 39266 38 43432 43431 none 3861056355 | 3860724211 S 2 1533479996 38 2789150424 16976376839 13115652629 5394204206 1533479993 0 0 1 245276 0.999936
    lockcand 9493949654 4142469605 1209137543 38515 38 42367 42366 none 4142554343 | 4141983251 S 2 1209983152 38 2789150424 17777916155 13635932905 13635932906 17777916159 0 0 1 486354 0.999883
    lockcand 9689838734 4401582643 886691350 702 38 5969 5967 none 4401594583 | 4401363247 S 2 887112240 38 2789150424 18492565227 14091201981 5288475486 887112237 0 0 1 219396 0.999950
    lockcand 9708394958 4428454341 851709669 67275 38 74466 74464 none 4428603275 | 4427796531 S 2 852801896 38 2789150424 18563988019 14136191489 5280598426 852801893 0 0 1 657810 0.999851
    lockcand 9824245731 4887128329 50022575 738 38 11168 11167 none 4887150669 | 2243840842 S 4 848882363 37 1610187039 14311927414 12068086573 7580404888 5336564044 0 0 0 2643287487 0.459133
    lockcand 16209122027 6516682302 3175812477 16676 39 28523 18351 none 6516719010 | 6515865006 S 2 3177392015 39 4910758398 29240852038 22724987033 9693257020 3177392012 0 0 1 817296 0.999875
    lockcand 16205315623 6583759314 3039564155 581745 39 589054 589053 none 6584937426 | 6568360214 S 2 3068595195 39 4910758398 29342036050 22773675837 9636955408 3068595192 0 0 1 15399100 0.997661
    lockcand 16201573355 6666962588 2867993684 108859 39 115170 115168 none 6667192930 | 6660990234 S 2 2879592887 39 4910758398 29523553822 22862563589 9540583120 2879592884 0 0 1 5972354 0.999104
    lockcand 16199180320 6815525500 2568156078 7439 39 8921 8919 none 6815543344 | 6815278592 S 2 2568623136 39 4910758398 29829737503 23014458912 9383901727 2568623133 0 0 1 246908 0.999964
    test 16199180341 6827775922 2543628495 81818 39 26652 127048 break 6827775926 | 6777798882 S 2 2643582577 39 4910758398 29754778104 22976979223 9421381458 2643582574 0 0 1 49977040 0.992680
    lockcand 16198547949 6845364496 2507947772 11667 39 42939 42938 none 6845450378 | 6843955194 S 2 2510637561 39 4910758398 29886458336 23042503143 9354592754 2510637558 0 0 1 1409302 0.999794
    lockcand 16198258185 6871914088 2455161134 243708 39 243709 243708 none 6872401510 | 6865229450 S 2 2467799285 39 4910758398 29928717084 23063487635 23063487636 29928717088 0 0 1 6684638 0.999027
    lockcand 16198114896 6899810874 2398885339 129847 39 130731 130730 none 6900072340 | 6898326840 S 2 2401461216 39 4910758398 29994768575 23096441736 9299788055 2401461213 0 0 1 1484034 0.999785
    lockcand 16372785314 7160041306 2053209403 168766 39 168901 168900 none 7160379112 | 7159047936 S 2 2054689442 39 4910758398 30690881185 23531833250 9213737377 2054689439 0 0 1 993370 0.999861
    lockcand 16372653526 7167034320 2038617398 8998 39 30667 10837 none 7167056000 | 7164868796 S 2 2042915934 39 4910758398 30702391117 23537522322 9207784729 2042915931 0 0 1 2165524 0.999698
    lockcand 16864529308 7989974088 884635142 17801 39 47476 18003 none 7990010100 | 7988606968 S 2 887315372 39 4910758398 32841743243 24853136276 8875922339 887315369 0 0 1 1367120 0.999829
    lockcand 16850763863 8161300430 528188795 3302 39 12761 8597 none 8161317630 | 8161109094 S 2 528545675 39 4910758398 33172982050 25011872957 8689654768 528545672 0 0 1 191336 0.999977
    lockcand 16843863754 8299018656 245866754 1 39 16773 13437 none 8299045536 | 8298651940 S 2 246559874 39 4910758398 33441167633 25142515694 8545211813 246559871 0 0 1 366716 0.999956
    lockcand 16834812136 8397533142 39748367 514 39 839 838 none 8397534824 | 8397510308 S 2 39791520 39 4910758398 33629832751 25232322444 8437301827 39791517 0 0 1 22834 0.999997
    lockcand 25296875719 8473464555 8350253786 101938 40 102393 102392 none 8473669345 | 8473029917 S 2 8350815885 40 8416580355 42242935552 33769905636 16823845801 8350815882 0 0 1 434638 0.999949
    bandexit 4912933713 4909293676 3640038 0 38 1 2 none 4909293678 | 1697636630 S 2 1517660453 37 1610187039 8308206972 6610570343 3215297082 1517660450 0 0 0 3211657046 0.345801
    bandexit 4911453830 4910082110 1371721 0 38 0 0 none 4910082112 | 1695991604 S 2 1519470622 37 1610187039 8303437037 6607445434 3215462225 1519470619 0 0 0 3214090506 0.345410
    bandexit 8421109093 8412250627 8858467 0 39 0 0 none 8412250629 | 2846695013 S 2 2727719067 38 2789150424 14114499118 11267804106 5574414079 2727719064 0 0 0 5565555614 0.338399
  [sameArc with q != 2] total=15146
    entry23 1802530080 1001775975 800754108 16949 36 0 800771057 none 1001775980 | 1000373092 A 1 802156988 36 904036925 1802530079 802156988 802156987 1802530081 1 0 1 1402883 0.998600
    entry23 1802516026 1001794975 800721054 3373 36 476 800725855 none 1001794980 | 1001274136 A 1 801241890 36 904036925 1802516025 801241890 801241889 1802516027 1 0 1 520839 0.999480
    entry23 1802533856 1001839639 800694220 21206 36 0 800715426 none 1001839644 | 1000380644 A 1 802153212 36 904036925 1802533855 802153212 802153211 1802533857 1 0 1 1458995 0.998544
    entry23 1802530091 1001888853 800641241 17490 36 47 800658872 none 1001888858 | 1000373114 A 1 802156977 36 904036925 1802530090 802156977 802156976 1802530092 1 0 1 1515739 0.998487
    entry23 1802516017 1001907349 800608671 3417 36 0 800612088 none 1001907354 | 1001274118 A 1 801241899 36 904036925 1802516016 801241899 801241898 1802516018 1 0 1 633231 0.999368
  [earlierArc with q <= 2] total=1515
    entry23 1802612987 1000538913 802074077 90561 36 1055 802167803 none 1000538918 | 854957150 S 2 92698687 35 511561221 1802612988 2657570137 2657570138 1802612986 0 1 0 145581763 0.854497
    entry23 1802644777 1001178401 801466379 125038 36 0 801591417 none 1001178406 | 854539734 A 2 93565309 35 511561221 1802644776 948105043 948105042 1802644778 1 0 0 146638667 0.853534
    entry23 1802537279 1001316649 801220633 24144 36 0 801244777 none 1001316654 | 855035858 S 2 92465563 35 511561221 1802537280 2657573137 2657573138 1802537278 0 1 0 146280791 0.853912
    entry23 1802584425 1001475329 801109099 71291 36 0 801180390 none 1001475334 | 855141294 A 2 92301837 35 511561221 1802584424 947443131 947443130 1802584426 1 0 0 146334035 0.853882
    entry23 1802595338 1001687271 800908070 82206 36 0 800990276 none 1001687276 | 854974796 S 2 92645746 35 511561221 1802595339 2657570134 2657570135 1802595337 0 1 0 146712475 0.853535
  [generalized (C'): sameArc with q != L_kind or earlierArc with q <= L_kind] total=100
    l3 4753495524 1529294957 165624405 2 36 13757 24761 none 1529322476 | 983193899 A 4 820719928 36 904036925 2787107727 3770301625 5736689424 4753495523 0 1 1 546101058 0.642907
    l3 4753490086 1529339255 165472316 3597 36 0 3597 none 1529339260 | 983204775 S 4 820670986 36 904036925 4753490087 5736694861 5736694862 4753490085 0 1 1 546134480 0.642895
    l3 4764128679 1539732009 144932647 183418 36 0 216280 none 1539732014 | 986705105 S 4 817308259 36 904036925 4764128680 5750833784 5750833785 4764128678 0 1 1 553026904 0.640829
    l3 4798645384 1571710313 83517567 3701 36 3127 4610 none 1571716572 | 998583755 A 4 804310364 36 904036925 4798645383 3800061629 3800061628 2801477871 1 0 1 573126558 0.635348
    l3 4803128982 1576447415 73786732 1 36 0 21942 none 1576447420 | 1000108963 A 4 802693130 36 904036925 4803128981 3803020019 3803020018 4803128983 1 0 1 576338452 0.634407
    l3 4803320621 1576585985 73562661 33891 36 0 39632 none 1576585990 | 1000182749 A 4 802589625 36 904036925 4803320620 3803137872 3803137871 4803320622 1 0 1 576403236 0.634398
    l3 4804325659 1577983313 70391057 1 36 15342 56513 none 1578014002 | 1000601969 A 4 801917783 36 904036925 4804325658 3803723690 3803723689 2803121718 1 0 1 577381344 0.634102
    l3 4806318222 1580927859 63635298 877 36 100658 138881 none 1581129180 | 1001268359 A 4 801244786 36 904036925 4806318221 3805049863 3805049862 2803781501 1 0 1 579659500 0.633342
    l3 4820971236 1598497703 25478122 2 36 0 16009 none 1598497708 | 1006198179 A 4 796178520 36 904036925 4820971235 3814773057 3814773056 4820971237 1 0 1 592299524 0.629465
    l3 8173750015 2598690204 377679398 23130 37 0 23130 none 2598690209 | 1651586886 A 4 1567402471 37 1610187039 8173750014 6522163129 6522163128 8173750016 1 0 1 947103318 0.635546
    l3 8248835714 2662222754 262326749 61429 37 159302 111257 none 2662541363 | 1677432028 A 4 1539107602 37 1610187039 8248835713 6571403686 6571403685 4893971655 1 0 1 984790726 0.630087
    l3 8256660453 2670626084 244821000 44380 37 38804 50182 none 2670703697 | 1680082570 A 4 1536330173 37 1610187039 8256660452 6576577883 6576577882 4896495310 1 0 1 990543514 0.629097
    l3 8266319011 2680800630 223943099 29006 37 25983 29006 none 2680852601 | 1683369770 A 4 1532839931 37 1610187039 8266319010 6582949241 9949688782 11633058554 1 0 1 997430860 0.627935
    l3 8290958045 2707363520 168867480 1 37 0 9257 none 2707363525 | 1691703398 A 4 1524144453 37 1610187039 8290958044 6599254647 6599254646 8290958046 1 0 1 1015660122 0.624853
    l3 8303437037 2720354420 142398458 47994 37 24686 50523 none 2720403797 | 1695991602 A 4 1519470629 37 1610187039 8303437036 6607445435 6607445434 4911453830 1 0 1 1024362818 0.623445
    l3 8308206972 2725157032 132792804 62816 37 56933 80500 none 2725270903 | 1697636628 A 4 1517660460 37 1610187039 8308206971 6610570344 6610570343 4912933713 1 0 1 1027520404 0.622950
    l3 8308206536 2725388322 132041565 8915 37 0 8915 none 2725388327 | 1697635756 A 4 1517663512 37 1610187039 8308206535 6610570780 6610570779 8308206537 1 0 1 1027752566 0.622897
    l3 8317854174 2735752258 110597395 2 37 0 19123 none 2735752263 | 1700885996 A 4 1514310190 37 1610187039 8317854173 6616968178 6616968177 8317854175 1 0 1 1034866262 0.621725
    l3 8319292586 2737271222 107478915 1787 37 0 2198 none 2737271227 | 1701578292 A 4 1512979418 37 1610187039 8319292585 6617714294 6617714293 8319292587 1 0 1 1035692930 0.621633
    l3 8319307025 2737294188 107424456 1527 37 0 1527 none 2737294193 | 1701607170 A 4 1512878345 37 1610187039 8319307024 6617699855 6617699854 8319307026 1 0 1 1035687018 0.621638
    l3 8319960390 2737927302 106178479 2991 37 0 5076 none 2737927307 | 1701957420 A 4 1512130710 37 1610187039 8319960389 6618002970 6618002969 8319960391 1 0 1 1035969882 0.621623
    l3 8320075680 2738057446 105903337 1 37 0 715 none 2738057451 | 1702072876 S 4 1511784176 37 1610187039 8320075681 10022148556 10022148557 8320075679 0 1 1 1035984570 0.621635
    l3 8320557285 2738537690 104950961 1 37 6751 9650 none 2738551197 | 1702311210 A 4 1511312445 37 1610187039 8320557284 6618246075 6618246074 4915934862 1 0 1 1036226480 0.621613
    l3 8320712809 2738796082 104326655 1 37 2097 7654 none 2738800281 | 1702403270 A 4 1511099729 37 1610187039 8320712808 6618309539 6618309538 4915906266 1 0 1 1036392812 0.621588
    l3 8320825478 2738899568 104128112 5319 37 1343 10558 none 2738902259 | 1702478384 A 4 1510911942 37 1610187039 4915868711 6618347094 10023303863 8320825477 0 1 1 1036421184 0.621592
    l3 8321856220 2739988442 101890889 12991 37 0 16694 none 2739988447 | 1702843480 A 4 1510482300 37 1610187039 8321856219 6619012740 6619012739 8321856221 1 0 1 1037144962 0.621478
    l3 8321913943 2740033996 101811950 13800 37 0 13800 none 2740034001 | 1702958926 A 4 1510078239 37 1610187039 8321913942 6618955017 6618955016 8321913944 1 0 1 1037075070 0.621510
    l3 8323359726 2741757222 98088055 13088 37 0 15064 none 2741757227 | 1703641920 A 4 1508792046 37 1610187039 8323359725 6619717806 6619717805 8323359727 1 0 1 1038115302 0.621369
    l3 8323428785 2741832536 97939676 10450 37 8504 15815 none 2741849549 | 1703780038 A 4 1508308633 37 1610187039 8323428784 6619648747 6619648746 4915868706 1 0 1 1038052498 0.621402
    l3 8323373868 2741924970 97598953 2 37 0 3550 none 2741924975 | 1703670204 A 4 1508693052 37 1610187039 8323373867 6619703664 6619703663 8323373869 1 0 1 1038254766 0.621341
    l3 8323635783 2742208714 97043921 1 37 34285 38568 none 2742277289 | 1703855078 A 4 1508215471 37 1610187039 8323635782 6619780705 10027490862 11731345942 1 0 1 1038353636 0.621344
    l3 8324223301 2742944452 95389940 7049 37 0 7967 none 2742944457 | 1704125682 A 4 1507720573 37 1610187039 8324223300 6620097619 6620097618 8324223302 1 0 1 1038818770 0.621276
    l3 8324228418 2742965614 95331571 2620 37 0 2620 none 2742965619 | 1704135916 A 4 1507684754 37 1610187039 8324228417 6620092502 6620092501 8324228419 1 0 1 1038829698 0.621275
    l3 8325285674 2744052958 93126795 3291 37 0 3291 none 2744052963 | 1704583172 A 4 1506952986 37 1610187039 8325285673 6620702502 6620702501 8325285675 1 0 1 1039469786 0.621192
    l3 8343753769 2764147760 51310484 16511 37 0 25085 none 2764147765 | 1710959450 A 4 1499915969 37 1610187039 8343753768 6632794319 6632794318 8343753770 1 0 1 1053188310 0.618983
    l3 8344126556 2764579086 50389293 3773 37 0 5576 none 2764579091 | 1711103824 A 4 1499711260 37 1610187039 8344126555 6633022732 6633022731 8344126557 1 0 1 1053475262 0.618938
    l3 8344126643 2764592224 50349966 1335 37 0 1466 none 2764592229 | 1711103998 A 4 1499710651 37 1610187039 8344126642 6633022645 6633022644 8344126644 1 0 1 1053488226 0.618935
    l3 8344161480 2764618610 50308567 6958 37 2922 7289 none 2764624459 | 1711173672 A 4 1499466792 37 1610187039 8344161479 6632987808 6632987807 4921814133 1 0 1 1053444938 0.618955
    l3 8364286073 2785659584 7307316 965 37 0 48022 none 2785659589 | 1718170006 A 4 1491606049 37 1610187039 8364286072 6646116067 6646116066 8364286074 1 0 1 1067489578 0.616791
    l3 8365526580 2786994300 4551548 1 37 7873 31739 none 2787010051 | 1718816972 A 4 1490258692 37 1610187039 8365526579 6646709608 6646709607 4927892633 1 0 1 1068177328 0.616728
    l3 8366152192 2787761878 2866553 164 37 0 7119 none 2787761883 | 1719084200 A 4 1489815392 37 1610187039 8366152191 6647067992 6647067991 8366152193 1 0 1 1068677678 0.616654
    l3 8366349031 2788019876 2289398 1 37 0 2664 none 2788019881 | 1719202802 A 4 1489537823 37 1610187039 8366349030 6647146229 6647146228 8366349032 1 0 1 1068817074 0.616639
    l3 14038155939 4369974827 928259864 59096 38 28411 85002 none 4370031654 | 2820284909 A 4 2757016303 38 2789150424 14038155938 11217871030 16858440849 19678725760 1 0 1 1549689918 0.645378
    l3 14038700027 4370620461 926838639 41686 38 0 41686 none 4370620466 | 2820557057 A 4 2756471799 38 2789150424 14038700026 11218142970 11218142969 14038700028 1 0 1 1550063404 0.645345
    l3 14038676692 4370702475 926569262 6569 38 0 6569 none 4370702480 | 2820510387 A 4 2756635144 38 2789150424 14038676691 11218166305 11218166304 14038676693 1 0 1 1550192088 0.645322
    l3 14038698861 4370755845 926431321 3912 38 0 7851 none 4370755850 | 2820554725 A 4 2756479961 38 2789150424 14038698860 11218144136 11218144135 14038698862 1 0 1 1550201120 0.645324
    l3 14064493237 4385753481 907232789 4734 38 0 4734 none 4385753486 | 2829532153 A 4 2746364625 38 2789150424 14064493236 11234961084 11234961083 14064493238 1 0 1 1556221328 0.645164
    l3 14064577993 4385818423 907125518 13840 38 2799 13990 none 4385824026 | 2829701665 A 4 2745771333 38 2789150424 14064577992 11234876328 11234876327 8405174660 1 0 1 1556116758 0.645194
    l3 14496751865 4658079819 522514672 197 38 2269 3821 none 4658084362 | 2975859797 A 4 2593312677 38 2789150424 14496751864 11520892068 11520892067 8545032268 1 0 1 1682220022 0.638860
    l3 14499275598 4660862515 516688048 2 38 0 1778 none 4660862520 | 2976724871 A 4 2592376114 38 2789150424 14499275597 11522550727 11522550726 14499275599 1 0 1 1684137644 0.638664
```

## 5. Census of the records (output of post.sh h10/records.txt)

```
== (B) exceptions (upperRun=0 lowerRun=0): ladder classification ==
   ladderSSS = subtraction at n, at n+1 (a(n+1) = w-(n+1)) and at n+2
1 discovery bandexit q=2 ladderSSS=0
18 discovery bandexit q=2 ladderSSS=1
23 discovery bandexit q=3 ladderSSS=0
7 discovery bandexit q=3 ladderSSS=1
1 discovery bandexit q=6 ladderSSS=0
1 discovery l3 q=3 ladderSSS=1
5 discovery l3 q=5 ladderSSS=0
1 discovery l3 q=6 ladderSSS=0
1 discovery lockcand q=2 ladderSSS=0
19 discovery lockcand q=2 ladderSSS=1
2 discovery test q=2 ladderSSS=1
3 holdout bandexit q=2 ladderSSS=1
1 holdout l3 q=5 ladderSSS=0
26 holdout lockcand q=2 ladderSSS=1
3 holdout lockcand q=2 ladderSSS=0
1 holdout lockcand q=4 ladderSSS=1
2 holdout test q=2 ladderSSS=1

== (B) exceptions: step pattern at clocks n-1, n, n+1, n+2 (A/S from the values), per kind and split ==
   SSSS/ASSS = ladder through w; AASS = spike (w is the peak); SSAA = valley (w is the bottom)
1 discovery bandexit q=2 pattern=SSAA sameArc=0
18 discovery bandexit q=2 pattern=SSSS sameArc=0
23 discovery bandexit q=3 pattern=AASS sameArc=0
7 discovery bandexit q=3 pattern=SSSS sameArc=0
1 discovery bandexit q=6 pattern=AASS sameArc=0
1 discovery l3 q=3 pattern=SSSS sameArc=1
5 discovery l3 q=5 pattern=AASS sameArc=0
1 discovery l3 q=6 pattern=AASS sameArc=0
1 discovery lockcand q=2 pattern=SSAA sameArc=1
19 discovery lockcand q=2 pattern=SSSS sameArc=1
2 discovery test q=2 pattern=SSSS sameArc=1
3 holdout bandexit q=2 pattern=SSSS sameArc=0
1 holdout l3 q=5 pattern=AASS sameArc=0
3 holdout lockcand q=2 pattern=SSAA sameArc=1
26 holdout lockcand q=2 pattern=SSSS sameArc=1
1 holdout lockcand q=4 pattern=SSSS sameArc=0
2 holdout test q=2 pattern=SSSS sameArc=1

== (B) exceptions: ladders (S at n, n+1, n+2) that end in a late landing at n+2 (a(n+2) < n+2) ==
25 bandexit ladderSSS=0 lateAtN+2=0
7 bandexit ladderSSS=1 lateAtN+2=0
21 bandexit ladderSSS=1 lateAtN+2=1
7 l3 ladderSSS=0 lateAtN+2=0
1 l3 ladderSSS=1 lateAtN+2=0
4 lockcand ladderSSS=0 lateAtN+2=0
1 lockcand ladderSSS=1 lateAtN+2=0
45 lockcand ladderSSS=1 lateAtN+2=1
4 test ladderSSS=1 lateAtN+2=1

== per kind: sameArc & q=L: run class (L=2 test/lockcand, 3 l3, 1 entry23/bandexit) ==
1351 bandexit both
2615 bandexit lower
1055 bandexit upper
27 entry23 both
10769 entry23 lower
8508 entry23 upper
3186 l3 lower
1 l3 neither
61 l3 upper
1 lockcand both
278 lockcand lower
49 lockcand neither
280 lockcand upper
7 test both
12010 test lower
4 test neither
6927 test upper

== per kind: earlierArc: (arcAtC-arcN, q) ==
816 bandexit dist=1 q=2
188 bandexit dist=2 q=3
102 bandexit dist=2 q=4
3 bandexit dist=2 q=5
10 bandexit dist=3 q=6
1 entry23 dist=1 q=1
2601 entry23 dist=1 q=2
356 entry23 dist=2 q=4
1 entry23 dist=3 q=7
96 l3 dist=1 q=5
11 l3 dist=1 q=6
1 lockcand dist=1 q=4
2 test dist=1 q=3
777 test dist=1 q=4
4 test dist=1 q=5
7 test dist=2 q=6

== test values, earlierArc: n/c min/max per q ==
q=3 count=2 n/c in [0.9999, 1.0000]
q=4 count=777 n/c in [0.4441, 0.6181]
q=5 count=4 n/c in [0.3432, 0.3734]
q=6 count=7 n/c in [0.3419, 0.4241]

== l3 values sameArc q=4 (C-prime exceptions): residue/n and run flags ==
c=925982 n=590322 n/c=0.637509 r/n=0.9978 upper=1 lower=0 split=discovery
c=1020800 n=637102 n/c=0.624120 r/n=0.8477 upper=1 lower=0 split=discovery
c=1021266 n=636492 n/c=0.623238 r/n=0.8518 upper=1 lower=0 split=discovery
c=9782006 n=6235652 n/c=0.637461 r/n=0.8485 upper=1 lower=0 split=discovery
c=30788980 n=19506434 n/c=0.633552 r/n=0.8800 upper=1 lower=0 split=discovery
c=30930994 n=19569292 n/c=0.632676 r/n=0.8735 upper=1 lower=0 split=discovery
c=51941165 n=33659693 n/c=0.648035 r/n=0.9059 upper=0 lower=1 split=discovery
c=54082121 n=34708521 n/c=0.641774 r/n=0.8477 upper=1 lower=0 split=discovery
c=56782147 n=36130267 n/c=0.636296 r/n=0.7709 upper=0 lower=1 split=discovery
c=97169456 n=61271362 n/c=0.630562 r/n=0.8876 upper=1 lower=0 split=discovery
c=292543292 n=184353794 n/c=0.630176 r/n=0.8773 upper=0 lower=1 split=discovery
c=495125809 n=304521641 n/c=0.615039 r/n=0.9890 upper=0 lower=1 split=discovery
c=495139493 n=304516941 n/c=0.615012 r/n=0.9891 upper=0 lower=1 split=discovery
c=495155951 n=304476859 n/c=0.614911 r/n=0.9898 upper=0 lower=1 split=discovery
c=495213761 n=304523121 n/c=0.614933 r/n=0.9890 upper=0 lower=1 split=discovery
c=495228441 n=304488949 n/c=0.614845 r/n=0.9896 upper=0 lower=1 split=discovery
c=496335427 n=304847399 n/c=0.614196 r/n=0.9870 upper=0 lower=1 split=discovery
c=506458397 n=308175561 n/c=0.608491 r/n=0.9647 upper=1 lower=0 split=discovery
c=509768977 n=309167217 n/c=0.606485 r/n=0.9583 upper=1 lower=0 split=discovery
c=796465380 n=513433488 n/c=0.644640 r/n=0.9925 upper=1 lower=0 split=discovery
c=796939734 n=513720852 n/c=0.644617 r/n=0.9913 upper=1 lower=0 split=discovery
c=832500932 n=534692654 n/c=0.642273 r/n=0.9119 upper=1 lower=0 split=discovery
c=832891130 n=534836972 n/c=0.642145 r/n=0.9111 upper=1 lower=0 split=discovery
c=1529294957 n=983193899 n/c=0.642907 r/n=0.8347 upper=0 lower=1 split=holdout
c=1529339255 n=983204775 n/c=0.642895 r/n=0.8347 upper=0 lower=1 split=holdout
c=1539732009 n=986705105 n/c=0.640829 r/n=0.8283 upper=0 lower=1 split=holdout
c=1571710313 n=998583755 n/c=0.635348 r/n=0.8055 upper=1 lower=0 split=holdout
c=1576447415 n=1000108963 n/c=0.634407 r/n=0.8026 upper=1 lower=0 split=holdout
c=1576585985 n=1000182749 n/c=0.634398 r/n=0.8024 upper=1 lower=0 split=holdout
c=1577983313 n=1000601969 n/c=0.634102 r/n=0.8014 upper=1 lower=0 split=holdout
c=1580927859 n=1001268359 n/c=0.633342 r/n=0.8002 upper=1 lower=0 split=holdout
c=1598497703 n=1006198179 n/c=0.629465 r/n=0.7913 upper=1 lower=0 split=holdout
c=2598690204 n=1651586886 n/c=0.635546 r/n=0.9490 upper=1 lower=0 split=holdout
c=2662222754 n=1677432028 n/c=0.630087 r/n=0.9175 upper=1 lower=0 split=holdout
c=2670626084 n=1680082570 n/c=0.629097 r/n=0.9144 upper=1 lower=0 split=holdout
c=2680800630 n=1683369770 n/c=0.627935 r/n=0.9106 upper=1 lower=0 split=holdout
c=2707363520 n=1691703398 n/c=0.624853 r/n=0.9010 upper=1 lower=0 split=holdout
c=2720354420 n=1695991602 n/c=0.623445 r/n=0.8959 upper=1 lower=0 split=holdout
c=2725157032 n=1697636628 n/c=0.622950 r/n=0.8940 upper=1 lower=0 split=holdout
c=2725388322 n=1697635756 n/c=0.622897 r/n=0.8940 upper=1 lower=0 split=holdout
c=2735752258 n=1700885996 n/c=0.621725 r/n=0.8903 upper=1 lower=0 split=holdout
c=2737271222 n=1701578292 n/c=0.621633 r/n=0.8892 upper=1 lower=0 split=holdout
c=2737294188 n=1701607170 n/c=0.621638 r/n=0.8891 upper=1 lower=0 split=holdout
c=2737927302 n=1701957420 n/c=0.621623 r/n=0.8885 upper=1 lower=0 split=holdout
c=2738057446 n=1702072876 n/c=0.621635 r/n=0.8882 upper=0 lower=1 split=holdout
c=2738537690 n=1702311210 n/c=0.621613 r/n=0.8878 upper=1 lower=0 split=holdout
c=2738796082 n=1702403270 n/c=0.621588 r/n=0.8876 upper=1 lower=0 split=holdout
c=2738899568 n=1702478384 n/c=0.621592 r/n=0.8875 upper=0 lower=1 split=holdout
c=2739988442 n=1702843480 n/c=0.621478 r/n=0.8870 upper=1 lower=0 split=holdout
c=2740033996 n=1702958926 n/c=0.621510 r/n=0.8867 upper=1 lower=0 split=holdout
c=2741757222 n=1703641920 n/c=0.621369 r/n=0.8856 upper=1 lower=0 split=holdout
c=2741832536 n=1703780038 n/c=0.621402 r/n=0.8853 upper=1 lower=0 split=holdout
c=2741924970 n=1703670204 n/c=0.621341 r/n=0.8856 upper=1 lower=0 split=holdout
c=2742208714 n=1703855078 n/c=0.621344 r/n=0.8852 upper=1 lower=0 split=holdout
c=2742944452 n=1704125682 n/c=0.621276 r/n=0.8847 upper=1 lower=0 split=holdout
c=2742965614 n=1704135916 n/c=0.621275 r/n=0.8847 upper=1 lower=0 split=holdout
c=2744052958 n=1704583172 n/c=0.621192 r/n=0.8841 upper=1 lower=0 split=holdout
c=2764147760 n=1710959450 n/c=0.618983 r/n=0.8767 upper=1 lower=0 split=holdout
c=2764579086 n=1711103824 n/c=0.618938 r/n=0.8765 upper=1 lower=0 split=holdout
c=2764592224 n=1711103998 n/c=0.618935 r/n=0.8765 upper=1 lower=0 split=holdout
c=2764618610 n=1711173672 n/c=0.618955 r/n=0.8763 upper=1 lower=0 split=holdout
c=2785659584 n=1718170006 n/c=0.616791 r/n=0.8681 upper=1 lower=0 split=holdout
c=2786994300 n=1718816972 n/c=0.616728 r/n=0.8670 upper=1 lower=0 split=holdout
c=2787761878 n=1719084200 n/c=0.616654 r/n=0.8666 upper=1 lower=0 split=holdout
c=2788019876 n=1719202802 n/c=0.616639 r/n=0.8664 upper=1 lower=0 split=holdout
c=4369974827 n=2820284909 n/c=0.645378 r/n=0.9776 upper=1 lower=0 split=holdout
c=4370620461 n=2820557057 n/c=0.645345 r/n=0.9773 upper=1 lower=0 split=holdout
c=4370702475 n=2820510387 n/c=0.645322 r/n=0.9774 upper=1 lower=0 split=holdout
c=4370755845 n=2820554725 n/c=0.645324 r/n=0.9773 upper=1 lower=0 split=holdout
c=4385753481 n=2829532153 n/c=0.645164 r/n=0.9706 upper=1 lower=0 split=holdout
c=4385818423 n=2829701665 n/c=0.645194 r/n=0.9703 upper=1 lower=0 split=holdout
c=4658079819 n=2975859797 n/c=0.638860 r/n=0.8714 upper=1 lower=0 split=holdout
c=4660862515 n=2976724871 n/c=0.638664 r/n=0.8709 upper=1 lower=0 split=holdout
c=4661181187 n=2976868895 n/c=0.638651 r/n=0.8707 upper=1 lower=0 split=holdout
c=4661196985 n=2976901185 n/c=0.638656 r/n=0.8707 upper=1 lower=0 split=holdout
c=4684904473 n=2984540939 n/c=0.637055 r/n=0.8659 upper=1 lower=0 split=holdout
c=4701540117 n=2989911117 n/c=0.635943 r/n=0.8625 upper=1 lower=0 split=holdout
c=4723688587 n=2997359985 n/c=0.634538 r/n=0.8577 upper=1 lower=0 split=holdout
c=4746056935 n=3003967555 n/c=0.632940 r/n=0.8535 upper=1 lower=0 split=holdout
c=4766943591 n=3010624383 n/c=0.631563 r/n=0.8494 upper=1 lower=0 split=holdout
c=4766966237 n=3010624637 n/c=0.631560 r/n=0.8494 upper=1 lower=0 split=holdout
c=4806963953 n=3023087939 n/c=0.628898 r/n=0.8417 upper=1 lower=0 split=holdout
c=4812119141 n=3024812133 n/c=0.628582 r/n=0.8406 upper=1 lower=0 split=holdout
c=4827849767 n=3029529679 n/c=0.627511 r/n=0.8377 upper=1 lower=0 split=holdout
c=4828026085 n=3029625769 n/c=0.627508 r/n=0.8377 upper=1 lower=0 split=holdout
c=4832562083 n=3031165647 n/c=0.627238 r/n=0.8366 upper=1 lower=0 split=holdout
c=4883413871 n=3047167123 n/c=0.623983 r/n=0.8268 upper=1 lower=0 split=holdout
c=4883499367 n=3047056847 n/c=0.623949 r/n=0.8270 upper=1 lower=0 split=holdout
c=4884601697 n=3047674441 n/c=0.623935 r/n=0.8264 upper=0 lower=1 split=holdout
c=4884930633 n=3047848565 n/c=0.623929 r/n=0.8262 upper=1 lower=0 split=holdout
c=4885223057 n=3047991865 n/c=0.623921 r/n=0.8260 upper=1 lower=0 split=holdout
c=4885281629 n=3047982213 n/c=0.623911 r/n=0.8261 upper=1 lower=0 split=holdout
c=4901491895 n=3053019575 n/c=0.622876 r/n=0.8230 upper=1 lower=0 split=holdout
c=4901596709 n=3053143797 n/c=0.622888 r/n=0.8228 upper=1 lower=0 split=holdout
c=4901908435 n=3052996559 n/c=0.622818 r/n=0.8230 upper=1 lower=0 split=holdout
c=4901961189 n=3053053329 n/c=0.622823 r/n=0.8229 upper=1 lower=0 split=holdout
c=4903117625 n=3053482857 n/c=0.622764 r/n=0.8226 upper=1 lower=0 split=holdout
c=4903148785 n=3053479265 n/c=0.622759 r/n=0.8226 upper=1 lower=0 split=holdout
c=4903704003 n=3053848607 n/c=0.622764 r/n=0.8222 upper=1 lower=0 split=holdout
c=7930776808 n=4995165446 n/c=0.629846 r/n=0.9647 upper=1 lower=0 split=holdout
c=7932836876 n=4996090554 n/c=0.629799 r/n=0.9642 upper=1 lower=0 split=holdout
c=7971739894 n=5008694726 n/c=0.628306 r/n=0.9590 upper=0 lower=1 split=holdout
c=7980834282 n=5011154820 n/c=0.627899 r/n=0.9580 upper=1 lower=0 split=holdout
c=7980861108 n=5011164394 n/c=0.627898 r/n=0.9580 upper=1 lower=0 split=holdout
c=7989233076 n=5014060798 n/c=0.627602 r/n=0.9568 upper=1 lower=0 split=holdout
c=8008749244 n=5020807442 n/c=0.626915 r/n=0.9539 upper=1 lower=0 split=holdout
c=8009806962 n=5021440048 n/c=0.626911 r/n=0.9536 upper=1 lower=0 split=holdout
c=8061626692 n=5038648368 n/c=0.625016 r/n=0.9468 upper=1 lower=0 split=holdout
c=8093128546 n=5047862020 n/c=0.623722 r/n=0.9432 upper=1 lower=0 split=holdout
c=8093523564 n=5047960170 n/c=0.623704 r/n=0.9431 upper=1 lower=0 split=holdout
c=8093777104 n=5047849826 n/c=0.623670 r/n=0.9432 upper=1 lower=0 split=holdout
c=8096461292 n=5049719102 n/c=0.623695 r/n=0.9421 upper=1 lower=0 split=holdout
c=8112057222 n=5055620618 n/c=0.623223 r/n=0.9398 upper=1 lower=0 split=holdout
c=8132438414 n=5059658306 n/c=0.622158 r/n=0.9381 upper=1 lower=0 split=holdout
c=8132468542 n=5059619656 n/c=0.622151 r/n=0.9381 upper=1 lower=0 split=holdout
c=8132564140 n=5059722424 n/c=0.622156 r/n=0.9380 upper=1 lower=0 split=holdout
c=8155049222 n=5066909690 n/c=0.621322 r/n=0.9352 upper=1 lower=0 split=holdout
c=8208388238 n=5083807856 n/c=0.619343 r/n=0.9287 upper=1 lower=0 split=holdout
c=8208673254 n=5083715172 n/c=0.619310 r/n=0.9288 upper=1 lower=0 split=holdout
c=8208922404 n=5084190334 n/c=0.619349 r/n=0.9284 upper=1 lower=0 split=holdout
c=8293118724 n=5111390214 n/c=0.616341 r/n=0.9179 upper=1 lower=0 split=holdout
c=8302577914 n=5114579198 n/c=0.616023 r/n=0.9166 upper=1 lower=0 split=holdout
c=8354488176 n=5131704730 n/c=0.614245 r/n=0.9101 upper=1 lower=0 split=holdout
```

## 6. Hypotheses (H = 10^10; counts from `h10/summary.txt` and section 5)

**(A) every blocking value first visited at level q >= 2 — FAIL in both splits.**
Violations 11,470 of 21,816 (discovery) and 12,856 of 30,412 (holdout). All of them are entry23
(6,840 + 12,465) and bandexit (4,630 + 391) values first visited at q = 1; q = 0 never occurs.
For test (19,738), lockcand (609) and l3 (3,478) there are 0 violations in either split. For test
and l3 this is forced (w = 2c+v+2 > 2n resp. w > 3n because n < c); the non-trivial part is
lockcand, where all 609 values have q = 2 (608) or q = 4 (1). As stated, (A) is refuted by the
level-1 blockers: the values that block the level-2/3 entry (c+v-3) and the band exits (a(n)-1)
are level-1 values first visited at level 1, almost always in the same arc.

**(B) every blocking value belongs to a ping-pong run at its first visit — FAIL in both splits.**
Violations 79 of 21,816 (discovery) and 36 of 30,412 (holdout); 115 of 52,228 = 0.22%. Per kind
(discovery / holdout): test 2 / 2, lockcand 20 / 30, l3 7 / 1, entry23 0 / 0, bandexit 50 / 3.
The step pattern at clocks n-1, n, n+1, n+2 (section 5) classifies all 115 without remainder:
- 79 ladders (SSSS): w is passed on a straight descent of four subtractions (levels 4,3,2,1,0 or
  5,4,3,2,1); test 4, lockcand 46, l3 1, bandexit 28. 70 of the 79 end with a late landing at
  n+2 (all 4 test, 45 of 46 lockcand, 21 of 28 bandexit). These are same-arc blockers (test,
  lockcand, one l3) or previous-arc blockers (bandexit).
- 31 spikes (AASS): w is the peak of a two-up-two-down excursion: levels 1,2,3,2,1 at
  n/c in [0.324, 0.335] for the 23 bandexit values with q = 3 and 4,5,6,5,4 at n/c = 0.19 for
  the one with q = 6; levels 3,4,5,4,3 at n/c in [0.64, 0.71] for the 6 l3 values with q = 5
  and 4,5,6,5,4 at n/c = 0.48 for the one with q = 6; all in an earlier arc.
- 5 valleys (SSAA): w is the bottom of a two-down-two-up excursion (lockcand 4, bandexit 1).
Everything else (52,113 values) is in a run: upperOnly 19,590, lowerOnly 31,135, both 1,388.

**(C) sameArc => q = 2 and earlierArc => q >= 3 — FAIL as stated in both splits**
(sameArc & q != 2: 12,550 / 15,146; earlierArc & q <= 2: 1,903 / 1,515), **but it holds exactly
for the test values** (0 / 0 / 0 / 0): all 18,948 same-arc test values have q = 2 and all 790
earlier-arc test values have q >= 3 (777 at q = 4, 2 at q = 3, 4 at q = 5, 7 at q >= 6). It also
holds for lockcand (608 same-arc at q = 2, 1 earlier-arc at q = 4). The violations are the other
event levels: l3 (same-arc values are at q = 3 or 4, since w > 3n), entry23 and bandexit
(same-arc values at q = 1, previous-arc values at q = 2).

**(C') sameArc => q = L_kind and earlierArc => q > L_kind — FAIL** with 24 of 21,816 (discovery)
and 100 of 30,412 (holdout). 123 of the 124 violations are l3 values first visited in the same
arc at q = 4 (n/c in [0.606, 0.648], r/n in [0.77, 0.998]: level-4 values of the arc's own
level-3/4 ping-pong lying just below 5n; 107 of them are upper-run values reached by addition,
16 lower-run values); the
remaining one is the boundary case c = 4, v = 2, w = 3 (entry23, first visited at n = 2 in arc
2). The observed rule "sameArc => q in {L, L+1}, earlierArc => q >= L+1" has exactly that one
trivial exception among the 52,228 records; it is reported as an observation, nothing was tuned.
The permitted repair of the card ("earlier arc => q >= 2") also holds with that single
exception, but it is vacuous for the level-1 events (their earlier-arc values sit at q = 2).

## 7. Observations

1. **The blocker is almost always the arc's own run at the event's level.** sameArc: 47,252 of
   52,228 (90.5%): test 18,948 / 19,738 (96.0%), lockcand 608 / 609, l3 3,371 / 3,478 (96.9%),
   entry23 19,304 / 22,263 (86.7%), bandexit 5,021 / 6,140 (81.8%). Same-arc first visits are
   late in the arc: n/c >= 0.912 for test, >= 0.992 for l3, >= 0.942 for lockcand, >= 0.704 for
   entry23, >= 0.621 for bandexit (section 5), and the gap c-n is spread over log2 bins 3..29.
2. **Same-arc test values are mostly lower values of the 2/3 ping-pong, not upper values of the
   1/2 ping-pong.** Of the 18,948 same-arc test values, 12,010 are lowerOnly (reached by
   subtraction; the level-2 lower run of a level-2/3 ping-pong), 6,927 upperOnly (reached by
   addition; the level-2 upper run of a level-1/2 ping-pong), 7 both, 4 neither. The hypothesis
   card expected "the arc's own k=2 upper run"; 63% are the k=2 lower run instead. The same
   holds for l3: 3,186 of the 3,248 same-arc q = 3 values are lower-run values (the level-3 side
   of the arc's own 3/4 ping-pong), 61 upper.
3. **Earlier-arc blockers come from the previous arc (or the one before) at a higher level, at a
   fixed fraction of c.** Over all kinds: previous arc 4,309, two arcs back 656, older 11. The
   level rises with the distance: test q = 4 from the previous arc at n/c in [0.444, 0.618]
   (777) and q >= 6 from two arcs back at n/c in [0.342, 0.424] (7); l3 q = 5 at n/c in
   [0.619, 0.715] (96) and q = 6 at [0.480, 0.496] (11); entry23 q = 2 from the previous arc
   (2,601) and q = 4 from two arcs back at [0.236, 0.465] (356); bandexit q = 2 from the previous
   arc (816), q = 3 at [0.323, 0.338] (188), q = 4 at [0.206, 0.465] (102) from two arcs back.
   The blocker of scale c is a run of scale c/2 (level 4) or c/3 (level 6), as the card's
   self-similarity picture wants, but only for the 9.5% earlier-arc cases.
4. **The lock outcome and T do not change the picture for test values.** earlierArc fraction:
   T = 1: 74 of 3,422; T = 2: 26 of 1,317; T >= 3: 690 of 14,999; break 707 of 16,252; wrap 0 of
   8; l3blocked 83 of 3,478. In every cell the same-arc values are all q = 2 and the earlier-arc
   values are all q >= 3.
5. **Self-blocking by the comb and by the chain.** 2,222 of the 19,304 same-arc entry23 values
   have gap c-n = 7: the value c+v-3 is the comb's own addition four teeth earlier
   (a(c-7) = (c-8) + (v+4) + 1), so every fresh comb end with T >= 5 is an entry23 event; the
   first visit is that addition unless the value was visited earlier still (mostly by the
   arc's level-1 lower run: 10,769 lowerOnly vs 8,508 upperOnly among the same-arc entry23
   values). 2,031 of the 5,021 same-arc bandexit values have gap 2 and 405 have gap 6: the band
   value a(n)-1 was the chain's own previous lower value, the chain was interrupted by a late
   landing and the comb addition re-entered the band one above it. All 1,388 "both" records have
   a(n-2) = a(n+2) = w+1 (the value w+1 is visited twice, as a level-1 lower value and again as
   the comb addition); 1,348 of them are such gap-2 band exits.
6. **lockcand is a long-lock phenomenon.** All 609 breaks with i_obs > i_gen have i_gen >= 64;
   their blockers are same-arc level-2 values (608) visited at n/c >= 0.942, 49 of them not in
   a +-1 run (45 are SSSS ladders ending in a late landing at n+2, 4 are valleys).
7. Step type tracks the run side exactly: for every kind, S counts coincide with lowerOnly + a
   few and A with upperOnly (e.g. test discovery S 4,158 vs lowerOnly 4,155, A 2,518 vs
   upperOnly 2,514), as the ping-pong description predicts.
8. Only 6,140 band exits with h <= 10^7 occur up to 10^10 (42,161 with h > 10^7): the sampling
   cap of 400,000 was far from being reached, so the bandexit rows are complete (k = 1).

## 8. Files

- `experiments/blocker_provenance_probe.cpp` — the program (repository).
- `provenance/h10/summary.txt` (109 KB), `records.txt` (52,228 lines), `queries.txt`,
  `pass1_summary.txt`, `stderr.log`; `h9/`, `h8/` likewise; `deathrule_h8/` — the death-rule
  probe's output at 10^8 used for the cross-check; `post.sh` — the census script of section 5;
  binaries `provenance`, `provenance10`, `deathrule`.
