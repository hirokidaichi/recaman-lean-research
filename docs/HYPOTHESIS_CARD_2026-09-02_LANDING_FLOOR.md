# Hypothesis card: landing floor（弧の底の下限）

- ID: `H-20260902-05`
- Owner: AI research epoch 2026-09-02（真偽を問わない計画、T4）
- Created: 2026-09-02
- Status: `CONJECTURED`
- Research branch: 非全射方向。chain の生存長と帯の未訪問 run

## Exact statement

弧の底（landing）を Chaffin と同じく「`a n mod n` が増加する時刻の間での `a n` の最小値」と
定義する（A393814/A393815）。`late_landing_iff` により、値 `t` が第 `n+1` 項で着地するのは
時刻 `n` が高さ `t+1` の interior 時刻で `t` が未訪問のときに限るので、
弧の底が `t` を下回らない限り `t` は着地されない。

```text
(landing floor)   ∃ N₀, ∀ n > N₀, 時刻 n が弧の底なら a n > 852655.
(hole permanence) landing floor と「852655 は第 N₀ 項まで未訪問」から、852655 は永久欠損。
```

`N₀ = 10^612` は `COMPUTED`（Chaffin）で満たされている。従って landing floor だけが
証明義務であり、これが証明されれば Recamán 数列は全射でない。

より一般の形（T5 へ）:

```text
(rising floor)   f(n) → ∞ で、時刻 n > N₀ の全ての弧の底 v が v > f(n) を満たす。
```

rising floor が成り立てば、時刻 `n` に `f(n)` 未満で未訪問の値は永久欠損であり、
`2^32` 未満の穴 1,277,400 個（`E-027`）の大半が永久欠損になる。

## Why it would matter

- Frontier obligation discharged: 全射性の否定の証明そのもの。
- Stronger than an existing identity because: 既存の結果はすべて「欠損 target を仮定した構造」で
  あり、この命題は仮定なしに実軌道の弧の底を下から抑える。
- Smallest useful consequence: `f(n) → ∞` の任意の証明で T5（欠損値は無限個）が従う。

## Provenance and dependencies

- Definitions used: `a`, `valuesThrough`, 高さ `a n − n`。
- Lean theorems used: `late_landing_iff`、`chain_descends`（生存長と着地値の関係）、
  `chain_exit_up`／`chain_late_landing`（出口の分類）、`missing_density_dichotomy`（(I) 側の確認）。
- Unverified mathematical assumptions: landing floor 自体。
- Literature source or analogy: Chaffin, *Computing the Recamán Sequence*（ping-pong 区間の先読み）。
  弧の本数は 1 decade あたり 8.45 本で一定、深さ `D = log₁₀ n − log₁₀ v` の分布は
  decade 区間によらず定常（中央値 7.4、90% 点 14.5、裾は `P(D > d) ≈ e^{−3.17−0.037 d}`）。

## Falsification plan

- Small and boundary cases: 10^41 の 2023155（floor 852655 に対する最も近い near miss）、
  10^17.95 の 963744、10^15.17 の 964419。
- Adversarial or weakened-history model: generalized orbit（単一初期値 `v0`）でも弧の底の深さ分布が
  定常かを `generalized_orbit_supply_probe` の母集団で測る。定常でなければ「canonical 固有」の
  性質であり、証明に `initial` からの生成が要る。
- Discovery range: Chaffin 台帳の添字 `[10^20, 10^300]`（深さ分布の推定に使用済み）。
- Frozen holdout range: 添字 `(10^300, 10^612]`（同台帳。深さ分布の定常性の検証）。
  さらに本リポジトリの run-length simulator で `(3×10^9, 10^12]` の弧を独立に再計算して
  Chaffin 台帳と一致させる。
- Maximum one permitted repair: `852655` を `f(n) → ∞` の任意の `f` に置き換える（rising floor）。
- Stop condition: 10^612 以降の Chaffin の追加計算で 852655 未満の弧の底が現れれば `REFUTED`。
  紙上証明が「帯の未訪問 run 長の大域 invariant」に還元されたまま 2 回の修理で閉じなければ `STOPPED`。

## Exact mechanism（2026-09-02 夜、arc trace で確定。`E-036`/`E-037` で訂正）

`a(n) = k·n + r` と書くと両ステップとも `r → r − k` で、弧の底は弧の最後の遅延着地である。
comb の末端 `(c, v)`（`v−1` 既訪問）では +3 の候補 `c+v = a(c−1)` が必ず塞がれ `k=3` へ跳ねる
（`late_landing_popup`）。+4 の候補 `2c+v+2` が既訪問なら `k=3/4` に固定される（`PopupLock`）。
`k=3→2` の候補 `2c+v−1−3i` は先行する歯の test 値と弧自身の `k=2` 上側 run の値で塞がれるが、
run を越えた最初の候補（`i_gen = (T−1)+⌊(J_eff+2)/3⌋`）が未訪問なら固定は破れて降下が再開する
（10^10 で break 15,926 / wrap 8 / `k=5` へ 3,452）。固定のまま剰余が尽きるのは `v < 13+7·i_pred`
のときだけである（予測 7・見逃し 1・誤警報 0・break 15,926）。弧が終わるのは、この wrap か、
再開した降下が掃いた帯に穴を見つけられずに剰余が尽きるときで、`Φ = 2·時刻+高さ` の落差では
特徴づけられない（底 = 最初の落差 ≥ 3 の comb 末端は 0/39、blocked かつ落差 < 3 が 318 件）。
従って landing floor は「剰余の残量 `v` と帯の未訪問 run で費用が決まる hole-hopping の降下が、
852655 の剰余類で高さ 852656 に届かない」という命題である。

## Acceptance test

1. 弧の底の値が、直前の chain の侵入高さ `H` と生存段数 `k` で `v ≈ n + H − 3k`（`chain_descends`）と
   表されることを Lean で固定する（局所部分。T2 の系）。
2. 生存段数 `k` が帯 `[n, n+H]` の未訪問 run 長で上から抑えられることを exact に述べる。
3. 弧の終端則を紙上で証明する：固定が破れる添字 `i_gen`、wrap 条件 `v < 13+7·i`、および再開した
   降下が剰余の尽きる前に次の穴へ届く条件（run 長 `J`・歯数 `T`・次の穴までの距離の算術）。
   これが本丸（`Φ` の落差による旧版の条件 3 は `E-036` で撤回）。
4. 3 から landing floor（または rising floor）を導き、`late_landing_iff` で 852655 の永久欠損へ。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-02 | `COMPUTED` | Chaffin 台帳、`chaffin_landing_analysis.py` | 弧は 8.45 本/decade で一定、深さ `D` は定常、10^41 以降 10^7 未満の着地なし。経験分布の外挿で 852655 の将来の着地期待回数は 10^612 以降 ≈ 10^-9。 |
| 2026-09-02 | `COMPUTED` | `landing_depth_probe v0 300000000`（v0 = 0, 1, 2, 3, 5, …, 10000 の 27 本） | 弧の底の検出は canonical で A393814/A393815 の先頭 19 件と一致。3×10^8 まで、全ての generalized orbit で弧は各 decade 4 本、深さ `D` の中央値 2.3〜3.3、90% 点 3.6〜5.3 で canonical（2.53、3.61）と同程度。深さ分布は `initial` 固有ではない。 |
| 2026-09-02 | `COMPUTED` | `run_length_recaman_simulator 10000000000000 accel`（`E-029`） | 1355 の初出 325,374,625,245 と mex 推移が OEIS と一致。2^20 未満の遅延着地は 1e9: 2309、1e10: 972、1e11: 430、1e12: 30 と減衰。 |
| 2026-09-02 | `COMPUTED` | `arc_death_rule_probe 10000000000`（`E-037`） | k=3/4 固定は通常破れる（break 15,926 / wrap 8 / k=5 へ 3,452）。break 添字 `i_gen=(T−1)+⌊(J_eff+2)/3⌋` が 12,777/15,926、wrap 条件 `v<13+7·i_pred` が 7/1/0/15,926。弧の終わりは wrap 8・break 後の穴なし 11・fresh 後の穴なし 15・k=5 後 2。 |
| 2026-09-02 | `COMPUTED` | `arc_potential_probe 10000000000`（`E-036`） | 「固定 ⟺ Φ の落差 ≥ 3」は偽：blocked かつ落差 < 3 が 318、fresh かつ落差 ≥ 3 が 2,745。底 = 最初の落差 ≥ 3 の comb 末端は 0/39。Φ の減少は k ≥ 3 を経由する区間でのみ起こる。 |
| 2026-09-02 | `PROVED-LEAN` | `LevelTwoThree`（`E-035`） | pop-up 後の k=2 復帰、k=2/3 ping-pong（offset −5/対）、出口の位置エネルギー `2m+s−K`（段の直前より `K−1` 低い）：Φ が下がる唯一の局所機構。 |
| 2026-09-02 | `PROVED-LEAN` | `PopupLock`（`E-034`） | k=3/4 固定の入口・反復・clock 以上・自身の k=2 値との同一視。arc trace の終端機構（`E-033`）の局所部分。 |
| 2026-09-02 | `COMPUTED` | arc trace（`E-033`） | 深い弧 6 本の底はすべて「comb 末端で `2c+v+2` 既訪問 → 固定 → 剰余尽き」。`2c+v+2` は同じ弧の過去の k=2 値。 |
| 2026-09-02 | `PROVED-LEAN` | `HoleHopping` | chainは自クラスの最初の穴に着地（`chain_lands_first_fresh`）、着地後は連続する穴を掃く（`comb_sweep`）、他クラスの穴は提示されない。 |
| 2026-09-02 | `COMPUTED` | `hole_hopping_closure.py`（`E-031`） | 帯の生存を無制限にすると剰余類ゲームの閉包は852655を埋める。保護は組合せではなくarcの深さに依る。 |
| 2026-09-02 | `COMPUTED` | simulator look-ahead census（`E-032`） | 区間終端は遅延着地61%・帯39%、`j_a/n > 10^−2`は1 decadeあたり約100件で、深いarcの本数（8.45/decade）と同程度。 |
| 2026-09-02 | `PROVED-LEAN` | `DescendingChain` | 局所機構（1 の部品 `chain_descends`）と、2 の局所半分 `chain_band_fresh_at_start`：k 段の chain が消費する帯の値はすべて開始時刻 `n+1` に未訪問だった。 |

## Semantic audit

- Informal statement implies formal statement: 弧の底の定義は Chaffin と同一で、`late_landing_iff`
  が「着地 ⟺ 高さ `t+1`」を与えるため、floor は着地の必要条件を正確に捉える。
- Formal statement implies intended consequence: floor + 10^612 項の未訪問で永久欠損。
- Counterfactual examples that should make the statement false: 10^612 以降に深さ `D > 606` の弧。
  定常な指数裾のもとで確率 ≈ 10^-9。
- Could the theorem be proved from weaker or vacuous assumptions?: 「弧の本数が減衰する」型の
  主張は台帳で偽（一定）なので使えない。深さの定常性だけが手掛かりである。
- Reachability, freshness, time order omitted?: 生存段数の上界は履歴の gap 構造に依存するため、
  `initial` からの生成（canonical）を仮定する証明になる可能性が高い。generalized orbit での
  定常性の検証で判定する。

## Decision

- Continue / formalize / refute / stop: `CONJECTURED`。1, 2 の局所部分は Lean 化を進めてよい。
  3 は紙上で、自己相似の帰納を最初の候補とする。
- Reason: 全射性の否定の証明義務がこの一命題に集約され、600 decade の検証データがある。
- Reopen only if: not applicable（active）。
