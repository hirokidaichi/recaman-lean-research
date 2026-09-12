# Hypothesis card: `tight-avoiding-lag-bound`

- ID: `H-20260912-01`
- Owner: 広木さん / parallel session (autonomous loop was concurrently proving E-232 for `p ≤ 11`)
- Created: 2026-09-12
- Status: (T1) `REFUTED`（Lean 証人あり） / (T2) `COMPUTED` / (T3) `COMPUTED`
- Research branch: issue #73, gate T6
- Registry: (T1) は `E-240` として `PROVED-LEAN` 登録済み（証人モジュール `TightAvoidingLagCertificate`）。(T2)(T3) は未登録

## Exact statement

記法は `TenGateT6Resolution` / `TwoSSTightDisjoint` に一致させる。周期 `p`、符号語 `e`、
`σ = signSum e 0 p > 0`、`D = subPhases e 0 p`、`U` は各元に P2 窓 `lag u` を割り当てた加算位相のリスト、
`N(A) = neighborhood e p A lag`、tight とは `|N(A)| = |A|`、avoiding とは `u₀ ∉ A`。
donor `u₀` は `ssCount = 2` かつ `lag u₀ < 15` の窓を持つ加算位相（削除可能性定理の仮定 `hss0`, `hd_lt`）。
`s*(u₀) = oldestSubtractionPhase p u₀ (lag u₀)`。slack は `|U| < |D|`。

三つの命題を分けて凍結する。

**(T1) lag 3 強制**（E-230 `tight_avoiding_all_lag_three_p10` の周期一般化）：
正 slack・donor を持つ任意の周期語の任意の tight avoiding 部分集合 `A` について、`∀ u ∈ A, lag u = 3`。

**(T2) lag ≤ 7 と低SS連動**：同じ設定で `∀ u ∈ A`、`lag u ∈ {3, 7}` かつ
`ssCount (past e u (lag u)) ≤ 1`、さらに lag と ssCount は連動する
（`lag u = 3 ⟹ ssCount = 0`、`lag u = 7 ⟹ ssCount = 1`）。

**(T3) Gate T6 の結論**：tight avoiding 部分集合は `s*(u₀)` を覆わない
（`s*(u₀) ∉ N(A)`）。これは削除可能性と Hall 保存の核心であり、(T1) はその十分条件にすぎない。

## Why it would matter

- Frontier obligation discharged: E-230/E-231 が `p ≤ 10` で無条件に閉じた根拠は
  `tight_avoiding_size_le_two_of_p10` の**純粋な数え上げ**
  （`|A| ≤ |U|-1 ≤ |D|-2` と `p ≤ 10 ∧ σ>0 ⟹ |D| ≤ 4`）である。
  `p = 11` では `|D| ≤ 5` しか出ず `|A| ≤ 3` となり、lag 7 窓（減算 3 個を覆う、E-229）を
  サイズだけでは排除できない。**この数え上げの寿命を測るのが本カードの目的**。
- Stronger than an existing identity because: (T2) は (T1) を含む正しい一般形の候補であり、
  かつ `ssCount ≤ 1` は E-128（低SS 全 lag 共同容量、`PROVED-LEAN`）の既証明クラスそのもの。
  (T2) が真なら gate T6 の残りは既証明クラスの内側へ落ちる。
- Smallest useful consequence: (T1) が偽になる最小周期が分かれば、
  「周期を 1 段ずつ上げる」現行戦略が何段で尽きるかが事前に確定する。

## Provenance and dependencies

- Definitions used: `neighborhood`, `isCoveredByWindow`, `oldestSubtractionPhase`,
  `endpointPhase`, `subPhases`, `ssCount`, `ShortPeriodicSupply.P2`。
- Lean theorems used: E-229 `QuantumP2Arithmetic`（lag `4m+3` は減算 `2m+1` 個を覆う）、
  E-230 `TenGateT6Resolution`、E-231 `GrandPeriodicDeletabilityTheorem`、
  E-181 `PeriodicSupplyBound`（後退走査の停止則）。
- Unverified mathematical assumptions: なし。probe は全 P2 lag 割当にわたる全探索で、
  Lean の `∀ lag` と同じ量化にそろえてある。
- Literature source or analogy: なし。

## Falsification plan

- Small and boundary cases: `p = 4..10`（既に Lean で閉じている領域）で probe が
  `lag 3 強制` を再現することを整合性検査とする。
- Adversarial or weakened-history model: `lag` は最小 lag ではなく**全ての** P2 lag 割当を探索する
  （Lean の定理が `∀ lag` なので、最小 lag だけの測定は仮説を弱める）。
  同様に avoiding 条件（`u₀ ∉ A`）は donor ごとのループとして課す。
- Discovery range: `p ≤ 18`。
- Frozen holdout range: `p = 19..22`（追加 holdout `p = 23, 24` も実施済み、下記 Evidence log）（`CHECK positive-sum words p=19..22 = 3,487,066` で
  E-081 と自動照合し、実装自体を独立検証する）。次の延長 `p = 23, 24` を追加 holdout とする。
- Maximum one permitted repair: (T1) が偽だった場合、lag の上界を一段だけ上げた (T2) への
  差し替えを 1 回だけ許す。それも偽なら lag 側の強制を諦め (T3) を直接扱う。
- Stop condition: (T3) に反例が出たら gate T6 そのものが偽なので分枝を停止する。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-12 | `REFUTED` (T1) | `tight_avoiding_growth 4 24` | `lag 3 強制`は **`p ≤ 17` で真、`p = 18` で偽**。証人 `AAAASSAAAASAAASASS`、`A = {2,8,11,13}`、`lag = [3,3,7,3]`、`N(A) = {4,5,10,17}`、donor `u₀ = 7`（S-ended, `ssCount = 2`, lag 11）、`|U| = 5 < |D| = 6`。tight 割当はこの1通りのみ |
| 2026-09-12 | `PROVED-LEAN` (T1) = **E-240** | `Recaman/TightAvoidingLagCertificate.lean` | 上の証人を `decide` で kernel 認証。公理は `{propext, Classical.choice, Quot.sound}` のみ、`sorry` 0 |
| 2026-09-12 | `COMPUTED` (T2) | `gate_t6_core 4 24` | `p ≤ 24` で例外 0。現れる窓は `(lag 3, ss 0)` と `(lag 7, ss 1)` の**2 種類のみ**、`lag ≥ 11` は 0 件。頻度は `p = 24` で 98,355 : 454 |
| 2026-09-12 | `COMPUTED` (T3) | `gate_t6_core 4 24` | `p ≤ 24` で**例外 0**。tight avoiding 部分集合が `s*(u₀)` を覆う例は donorCases 12,557 件（`p = 24`）を通じて 1 件もない |
| 2026-09-12 | 整合性 | 両 probe | `p = 19..22` 正符号和語数 `3,487,066` が E-081 と一致。走査は `p(p+3)` 安全上界を超えず、実測 `max |A|` は数え上げ上界 `|D|-2` を超えない |
| 2026-09-12 | 訂正 | 同上 | donor の **S-ended 条件を課す前**は (T1) の破れが `p = 15` と出ていた。S-ended を課すと donorCases が約半分に減り、境界は `p = 18` へ動く。`avoiding`（`u₀ ∉ A`）を課す前は `p = 13` と出ていた。**この2つの仕様はいずれも Lean の定理文に含まれており、省くと破れを早く報告する** |

数え上げ上界と実測のギャップ（`countingCap = max(|D|-2)` / 実測 `max |A|`、S-ended donor 版）：

| p | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| cap | 3 | 4 | 4 | 5 | 5 | 6 | 6 | 7 | 7 | 8 | 8 | 9 | 9 |
| 実測 | 2 | 2 | 3 | 3 | 3 | 3 | **4** | 4 | 4 | 4 | 5 | 5 | 6 |
| max lag | 3 | 3 | 3 | 3 | 3 | 3 | **7** | 7 | 7 | 7 | 7 | 7 | 7 |

**実測サイズが 4 に達する周期（`p = 18`）が、lag 7 が現れる周期と一致する。** lag 7 窓は減算を 3 個
覆うので、tight な同居には `|A| ≥ 4` が要る（他に最低 1 個の lag 3 窓が要る）。数え上げ上界 `|D|-2` は
`p = 13` で既に 4 に達しているが、実測が 4 に届くのは 5 周期あとである。

## Semantic audit

- Informal statement implies formal statement: (T1)(T2)(T3) はいずれも Lean の定理文と
  同じ量化（`∀ U, ∀ lag, ∀ A`）で測っている。donor の S-ended 条件と avoiding 条件は
  定理文に含まれるので probe 側にも課している（省いた場合の差は Evidence log の訂正行）。probe は `U` を最小の `A ∪ {u₀}` に取り、
  slack・P2・加算性・削除前 Hall を全て検査した上でのみ反例として数える。
- Formal statement implies intended consequence: (T3) は削除可能性そのものの必要十分形
  （Hall は `|A| = |N(A)|` かつ `s* ∈ N(A)` のときにのみ破れる）なので、
  (T3) が真であることは gate T6 の結論が真であることと同値。
- Counterfactual examples that should make the statement false: (T1) には実際に反例があり
  `p = 18` で記録し Lean 認証した。(T2)(T3) には `p ≤ 24` で反例がない。
- Could the theorem be proved from weaker or vacuous assumptions?: **(T1) の `p ≤ 10` 版は
  実質的に空虚に近い**。`p ≤ 10 ∧ σ > 0` は `|D| ≤ 4` を強制し、`|A| ≤ 2` が自動的に従うので、
  lag 7 の排除は語の構造ではなく周期の小ささだけから出ている。
  周期を 1 段ずつ上げる戦略はこの空虚さを引き継ぐため、`p ≥ 11` では別の論拠が必ず要る。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?:
  本カードは周期語上の組合せ命題であり、実軌道の provenance は E-065 が別に担保している。

## Decision

- Continue / formalize / refute / stop:
  - (T1) は `REFUTED`、証人は `Recaman/TightAvoidingLagCertificate.lean` で kernel 認証済み。
    `lag 3 強制`を一般 `p` の目標として掲げることを**停止**する。
    延長は `p ≤ 17` まで（`p = 17` が現行ルートの寿命の上限、`p = 18` で結論が偽）。
  - (T2) を新しい gate 候補として `COMPUTED` で登録し、Lean 化の対象とする。
  - (T3) は gate T6 の結論そのもので `COMPUTED`、`p ≤ 22` で例外 0。
- Reason: 現行の証明ルートが死ぬ周期（`p = 18`）と、gate T6 の結論が生きている範囲
  （`p ≤ 24` で例外 0）が分離して測れた。**証明の寿命と命題の真偽は別物**である。
  なお自律ループは同日 E-237 で独立に `lags in {3, 7}` と 4 層 `p ≤ 7, 10, 12, 14` に到達しており、
  本カードの (T2) と寿命の測定はそれと整合する。
  lag と ssCount が完全連動し双方とも `ssCount ≤ 1` に収まることは、
  残りが E-128 の既証明クラスの内側にあることを示唆する。
- Reopen only if: (T2) に `p ≥ 25` で反例が出た場合、または `lag ≥ 11` の窓が
  tight avoiding 部分集合に現れた場合。そのときは lag 側の強制を諦め (T3) を直接扱う。
