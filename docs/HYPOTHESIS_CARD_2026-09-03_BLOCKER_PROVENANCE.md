# Hypothesis card: blocker provenance（降下を塞ぐ値の出所）

- ID: `H-20260903-01`
- Owner: AI research epoch 2026-09-03（真偽を問わない計画、T4 の帯の履歴部分）
- Created: 2026-09-03
- Status: `CONJECTURED`（probe 実行前）
- Research branch: 非全射方向。landing floor（`H-20260902-05`）の非局所部分

## Exact statement

`E-037` により、弧の降下（hole-hopping）を止めるのは次の 4 種の**塞ぐ値（blocker）**である：

1. `test`：comb 末端 `(c, v)` の test 値 `w = 2c+v+2`（既訪問なら k=3/4 固定）。
2. `lockcand`：固定が run を越えても続く場合の k=2 候補 `w = 2c+v−1−3·i_gen`（既訪問）。
3. `l3`：固定中に既訪問だった k=3 値 `w = 3c+v+5−i`（軌道は k=5 へ上がる）。
4. `entry23`：fresh な comb 末端で既訪問だった k=2→1 候補 `w = c+v−3`（k=2/3 段に入る）。

補助として `bandexit`：k=1/2 chain の帯脱出を起こした既訪問の帯値 `w = a(n)−1`（高さ ≤ 10^7 の脱出）。

各 blocker `w` について、その**初訪問**時刻 `n`（`a(n) = w` となる最初の時刻）、level `q = ⌊w/n⌋`、
弧の同一性（`n` の弧が comb 末端の弧と同じか）、run 所属（`a(n±2) = w±1`）を測る。

```text
(A) 全ての blocker は level q ≥ 2 で初訪問される（level 0/1 の値は blocker にならない）。
(B) 全ての blocker は初訪問時に ping-pong run の一部である：a(n+2) = w±1 または a(n−2) = w∓1。
(C) 同じ弧の blocker は q = 2（弧自身の k=2 上側 run）、前の弧の blocker は q ≥ 3。
```

`PingPongRuns`（`pingpong_run`）により、level `p+2/p+1` の ping-pong の上側値は `a m + k`、
下側値は `a m − (m+k+1)` の連続 run なので、(B) は「blocker は必ず ping-pong 段が作った連続 run に
属する」という主張である。

## Why it would matter

- Frontier obligation discharged: landing floor の「帯の履歴」部分に構造を与える。降下を塞ぐのが
  常に**より高い level の ping-pong run**（時刻 ≈ w/q、q ≥ 3 なら前の弧）であれば、スケール `c` の
  構造がスケール `c/2, c/3, c/4` の run で決まる自己相似の帰納が立つ。
- Stronger than an existing identity because: `E-036` は blocked かつ落差 < 3 の 20 件で「前の弧の k=4 値」
  を見ただけで、全数ではない。
- Smallest useful consequence: (A) だけでも「late landing と k=1 値は降下を塞がない」が exact に言え、
  帯の既訪問値の候補が level ≥ 2 の run に限られる。

## Provenance and dependencies

- Definitions used: `a`, `valuesThrough`, level `a n / n`、剰余 `a n % n`、Chaffin の弧（剰余非増加区間）。
- Lean theorems used: `PopupLock`（固定）、`LevelTwoThree`（k=2/3 段）、`LockResidue`（剰余則、予算）、
  `PingPongRuns`（run の +1/−1 則）。
- Unverified mathematical assumptions: (A)(B)(C) 自体。
- Literature source or analogy: Chaffin の ping-pong 区間（先読みアルゴリズムの根拠）。

## Falsification plan

- Small and boundary cases: 10^10 までの全 comb 末端（44,422 件、blocked 19,738 件）と全固定結末。
- Adversarial or weakened-history model: なし（canonical のみ。generalized orbit は後続）。
- Discovery range: comb 末端の時刻 `c < 10^9`。
- Frozen holdout range: `10^9 ≤ c < 10^10`。
- Maximum one permitted repair: (C) の「前の弧なら q ≥ 3」を「前の弧なら q ≥ 2」に緩める。
- Stop condition: (A) か (B) に反例が 1 件でもあれば該当項目は `REFUTED`。(C) は修理 1 回まで。

## Acceptance test

1. `experiments/blocker_provenance_probe.cpp`（2 パス：pass 1 でクエリ値を集め、pass 2 で初訪問を記録）が
   死亡則 probe と同じ comb 末端数・blocked 数・固定結末を再現する。
2. (A)(B)(C) を discovery と holdout で別々に判定する。
3. kind × q × 同じ弧／前の弧 × run 種の表と、`n/c` の分布を epoch report に残す。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-03 | `PROVED-LEAN` | `PingPongRuns` | 任意 level の ping-pong 対で剰余は `2p+3` 減り、run の上側値は `a m + k`、下側値は `a m − (m+k+1)`（`pingpong_run`）。 |

## Semantic audit

- Informal statement implies formal statement: blocker の定義は `E-037` の 4 事象そのもので、初訪問は
  一意に定まる。
- Formal statement implies intended consequence: (A)(B) が成り立てば、帯の既訪問値は level ≥ 2 の run の
  値に限られ、run の producer（level、時刻）で帯の履歴を記述できる。
- Counterfactual examples that should make the statement false: late landing の値（level 0）が後で
  test 値になる例。値 `2c+v+2` は時刻 `c` で `2c` 程度なので、level 0 で訪問されるには時刻 > `2c` が
  必要で不可能。level 1 なら時刻 `n ∈ (c, 2c]` — comb 末端の弧の中で可能性はある。
- Could the theorem be proved from weaker or vacuous assumptions?: (A) は上の時刻の議論で
  「level 0 は不可能」までは自明。level 1 の排除は非自明。
- Reachability, freshness, time order omitted?: 初訪問は `n < c`（既訪問の定義）。

## Decision

- Continue / formalize / refute / stop: `CONJECTURED`。probe の結果で更新する。
- Reason: landing floor の非局所部分（帯の履歴）に最初の構造仮説を置く。
- Reopen only if: not applicable（active）。
