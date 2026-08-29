# NegativeEpoch

**役割:** 負エポックの主定理を証明する: 目標 `m ≤ n+1` に対し、負ポテンシャル状態は高々 `⌊r/2⌋` 歩で `CoverageStep` を与えるか、undershoot 帯 `0 ≤ G < m` へ脱出する。

## このモジュールの役割

回復層(`Recovery`〜`RecoveryFrontier`)が用意した部品を目標 `m` 込みで組み立て、負エポック(負ポテンシャルから回復を追う有限な軌道区間)を完全に二択へ縮約する。結論の一方は `CoverageStep m (a n) n`、すなわち「目標 `m` が実際に出現する」か「`m ≤ y < a n` を満たすより小さい初出値 `y` を得る」かの一段の大域進捗証明である。もう一方は一段借りによる undershoot 帯(`0 ≤ G < m` の非負ポテンシャル帯)への着地であり、その後の解析は `Undershoot.lean` が引き継ぐ。強化版の主定理は途中の値が出発値を超えないことも保持しており、後で見つかる証明書を元の親値へ輸送できる。これにより証明地図の「負エポック有限化」が完成する。

## 定理と証明

### `coordinates_add_zeroBorrow_negative_gives_coverageStep` (L8)

**主張:** 負ポテンシャルの zero-borrow 状態で強制加算が起こるなら、すべての目標 `m ≤ n + 1` に対し `CoverageStep m (a n) n` が成り立つ。

**証明:** 負の zero-borrow 状態では `q ≥ 2`(`Recovery.lean`)かつ通常領域 `q ≤ r`。減算候補 `y = a n − (n+1)` を考えると、`a n = n·q + r ≥ 2n + r` から

```text
y ≥ n + r − 1 ≥ n + 1    (r ≥ q ≥ 2 を使用)
```

であり、`y < a n` は明らか。強制加算(減算不能)の仮定から `y` はすでに履歴にある(未出なら減算が合法になるため)。履歴の元は初出時刻 `fy` を持つので、`m ≤ n + 1 ≤ y` と合わせて `CoverageStep` の値下降枝(初出値 `y < a n` の発見)が成立する。

### `coordinates_sub_potential_aboveTarget_gives_coverageStep` (L51)

**主張:** 合法減算の着地ポテンシャルが目標以上(`m ≤ G(k, s)`)なら、`CoverageStep m (a n) n` が成り立つ。

**証明:** 着地座標から `a (n+1) = (n+1)·k + s` かつ `s ≥ U(k) + m ≥ m`、よって `m ≤ a (n+1)`。合法減算の着地値は定義上フレッシュ(未出)で `a (n+1) < a n` なので、減算一般の補題 `subtraction_gives_coverageStep` により値下降枝が得られる。

### `coordinates_add_oneBorrow_potential_aboveTarget_gives_coverageStep` (L71)

**主張:** 一段借り強制加算の着地ポテンシャルが目標以上(`m ≤ G(k, s)`)でも、`CoverageStep m (a n) n` が成り立つ。

**証明:** 加算の着地値自体は `a n` より大きいので、減算の場合のように直接は使えない。そこで実際に到達したレベル `M = G(k, s) = s − U(k) ≥ m` を仮の目標とみなす。着地はちょうど目標面 `G = M` の上なので、`PrestateCoverage.lean` の前状態被覆定理(`coordinates_add_target_prestate_gives_coverageStep`)が `CoverageStep M (a n) n` を与える。さらに一段借りの前状態値の等式から `M < a n` が分かるので、目標引き下げ補題 `CoverageStep.lower_target` により `M` を `m ≤ M` へ下げて結論を得る。

### `negative_epoch_undershoot_or_coverage_with_value` (L118)

**主張:** 負エポックの主定理(値追跡付き)。`m ≤ n + 1`、`CoordinatesAt n q r`、`G(q,r) < 0` のとき、時刻 `t`(`n ≤ t ≤ n + ⌊r/2⌋`)、座標 `q', r'`、借りデータ `b, s`、着地商 `k` が存在して、

- `a t ≤ a n` かつ(`t = n` または `a t < a n`)、
- `CoordinatesAt t q' r'`、`BorrowData t q' r' b s`、`CoordinatesAt (t+1) k s`、
- 次のいずれかが成り立つ:
  1. **undershoot 脱出**: `b = 1` で着地は `0 ≤ G(k,s) < m` を満たし、脱出の枝(合法減算で `k = q' − 2` か、強制加算で `k = q'` か)も記録される。
  2. **被覆**: `CoverageStep m (a n) n`。

**証明:** 剰余 `r` に関する強帰納法。現在の状態の借りデータを取ると、実軌道では `b ∈ {0, 1}` に限られる。

**(i) `b = 0`、合法減算。** 唯一の再帰枝である。zero-borrow 減算は負ポテンシャルを保存し、剰余は `s + 2 ≤ r` と 2 以上減る(`Recovery.lean`)ので、帰納法の仮定を次状態(時刻 `n+1`、目標条件は `m ≤ n + 2` に緩む)へ適用できる。減算なので `a (n+1) < a n` であり、再帰が返す時刻 `t` の値の追跡 `a t ≤ a (n+1) < a n` が親でも成り立つ。再帰の結論が被覆の場合は、値の厳密下降を使って `CoverageStep.mono_parent` で親 `a n` の証明書に持ち上げる。歩数は `1 + ⌊s/2⌋ ≤ ⌊r/2⌋` に収まる。

**(ii) `b = 0`、強制加算。** L8 の定理が直ちに `CoverageStep m (a n) n` を与え、`t = n` で終了する。

**(iii) `b = 1`、合法減算。** 着地 `k = q' − 2` のポテンシャルで三分する。着地が `m` 以上なら L51 で被覆。`0 ≤ G(k,s) < m` なら undershoot 脱出そのものであり、枝情報とともに終了する。着地が負なら `RecoveryFrontier.lean` により `k ≥ 4` で、`a (n+1) = (n+1)·k + s ≥ n + 1 ≥ m` となるから、フレッシュな減算着地値がそのまま値下降枝を与える(`subtraction_gives_coverageStep`)。

**(iv) `b = 1`、強制加算。** 同じく三分する。`m` 以上なら L71 で被覆。`0 ≤ G(k,s) < m` なら undershoot 脱出。負なら `RecoveryFrontier.lean` の blocker 定理(`..._below_doubleTime`)が `m ≤ n + 1 ≤ 2(n+1)` の範囲で被覆を与える。

再帰するのは (i) だけで、そこでは値が厳密に減るため、`t > n` なら `a t < a n` という付加情報も帰納的に維持される。undershoot 脱出は必ず一段借り(`b = 1`)で起こる点が、`Recovery.lean` の「横断は一段借りのみ」と整合している。

### `negative_epoch_undershoot_or_coverage` (L247)

**主張:** 主定理の後方互換な射影: 値追跡と脱出枝の情報を落とし、「`0 ≤ G(k,s) < m` の着地」か「`CoverageStep m (a n) n`」かの二択だけを述べる。

**証明:** L118 の結論から必要な成分を取り出すだけである。

## 全体の中での位置づけ

`RecoveryFrontier` を入力とし、`Undershoot.lean` から使われる。証明地図(docs/PROOF_MAP.md)の「負エポック有限化」の完成形であり、証明済み縮約図の「任意の負状態 → 高々 ⌊r/2⌋ 歩 → 一段借り着地 →(`G ≥ m` なら CoverageStep / `0 ≤ G < m` なら非負アンダーシュート)」がこのモジュールの主定理そのものである。`Undershoot.lean` の `negative_undershoot_cycle` はこの定理と undershoot 帯の有限降下を合成して符号一周期の解析を作り、さらに `PhaseEpoch.lean` や `OrbitReadyComplete.lean`、`NonnegativeSemantic.lean` などの位相統合層がこのエポック解析を意味的探索 domain 上で再利用する。
