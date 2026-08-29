# HistoryBudget

**役割:** 未出値の個数「履歴予算」を定義し、二成分・三成分の整礎な探索ランクと抽象オラクルを構成する。

## このモジュールの役割

全射性予想を「目標 `m` ごとの有限探索」に落とすには、探索の各ステップで必ず減少する整礎な量(ランク)が必要である。本モジュールはその中心量として**履歴予算** `missingBelowCount m n`(時刻 `n` までに未出である `m` 未満の値の個数)を導入する。履歴予算は時間が進むと増えず、`m` 未満の新しい値が初出すると真に減る、高々 `m` の有限量である。この予算を第一成分に置いた二成分ランク(予算, 親の値)と三成分ランク(予算, アンカー親, 局所軌道値)の辞書式順序が整礎であることを証明し、「各ノードで目標出現か真に小さい子を返す」という抽象オラクル(証明義務)から目標の実出現が従うことを示す。後続の `HistoryFrontier`、`PhaseSearch` 以降のすべての大域探索はこのランクの上に構築される。

## 主要な定義

### `missingBelowCount` (L9)

`missingBelowCount m n` は、時刻 `n` までの履歴 `valuesThrough n` に含まれない `m` 未満の値の個数である。有限集合ライブラリに依存しないよう、`m` に関する再帰で定義する:

```text
missingBelowCount 0 n = 0
missingBelowCount (m+1) n = missingBelowCount m n + (m が既出なら 0、未出なら 1)
```

この展開式はそのまま simp 補題 `missingBelowCount_zero` (L15)、`missingBelowCount_succ` (L18) として登録されている。

### `historyBudgetRank` (L121)

値と時刻の組(`Occurrence`)に対する二成分ランク `(missingBelowCount m 時刻, 値)`。第一成分が履歴予算、第二成分が通常の親の値である。

### `HistoryBudgetProgress` (L127)

`historyBudgetRank` に関する辞書式の真の減少。子が `m` 未満の未出値を少なくとも一つ消費するか、予算が不変のまま値が減るとき成り立つ。

### `HistorySearchNode` (L225)

三成分の探索状態。`horizon`(現在参照できる実軌道履歴の範囲。以下**horizon**と呼ぶ)、`parentValue`(blocker が下げるべき現在の初出親の値)、`orbitValue`(探索中の局所軌道値)を分離して保持する。初出時刻と前向きの horizon を混同すると、blocker への遷移が「履歴を過去へ巻き戻す」ように見えてランクが壊れるため、この分離は本質的である。

### `historySearchRank` (L234)

三成分ランク `(missingBelowCount m horizon, (parentValue, orbitValue))`。新しい `m` 未満の値の発見が最優先、blocker による親の下降が第二、局所軌道値の下降が最後のタイブレークとなる。

### `HistorySearchProgress` (L239)

`historySearchRank` に関する右入れ子の三成分辞書式順序での真の減少。

### `HistorySearchOracle` (L386)

抽象オラクル: 任意の `HistorySearchNode` に対し、目標 `m` が実軌道上に出現するか、三成分ランクで真に小さい子ノードが存在する、という命題。これは外部計算ではなく、後続モジュールが構成すべき証明義務である。

## 定理と証明

### `valuesThrough_mono` (L24)

**主張:** `n ≤ t` かつ `x ∈ valuesThrough n` ならば `x ∈ valuesThrough t`。履歴の所属は時間について単調である。

**証明:** `t` に関する帰納法。一歩の履歴保存則 `valuesThrough_persist` を繰り返すだけである。

### `missingBelowCount_antitone` (L40)

**主張:** `n ≤ t` ならば `missingBelowCount m t ≤ missingBelowCount m n`。履歴が増えると未出値の個数は増えない。

**証明:** `m` に関する帰納法。各段の寄与(値 `m-1` が未出なら 1)は、履歴の単調性(`valuesThrough_mono`)により時刻 `t` で 1 から 0 に変わることはあっても逆はない。よって全体の和も減少方向にしか動かない。

### `missingBelowCount_le` (L57)

**主張:** `missingBelowCount m n ≤ m`。未出値は高々 `m` 個であり、予算は有限である。

**証明:** `m` の帰納法で、各段の寄与が高々 1 であることから直ちに従う。

### `missingBelowCount_strict_of_new` (L67)

**主張:** `g < m` なる値 `g` が時刻 `n` で未出、時刻 `t ≥ n` で既出ならば、`missingBelowCount m t < missingBelowCount m n`。真に新しい下側値の出現は予算を厳密に減らす。

**証明:** `m` に関する帰納法。`g` が最上段 `m-1` に一致する場合は、その段の寄与が `n` で 1、`t` で 0 になり、残りの段は `missingBelowCount_antitone` により増えないので全体は厳密に減る。`g < m-1` の場合は帰納法の仮定で下位部分が厳密に減り、最上段の寄与は減少方向にしか動かないので、和も厳密に減る。

### `firstAt_not_mem_valuesThrough_before` (L97)

**主張:** `g` の初出時刻が `t` で `n < t` ならば、`g ∉ valuesThrough n`。

**証明:** もし `g` が時刻 `n` までの履歴にあれば、ある時刻 `u ≤ n < t` で `a u = g` となり、`t` が初出であることに矛盾する。

### `missingBelowCount_strict_of_firstAt` (L108)

**主張:** `g < m` の初出時刻 `t` が `n < t` を満たすなら、`missingBelowCount m t < missingBelowCount m n`。

**証明:** 前二定理の合成。初出前は未出、初出時刻では現在値として履歴に入るので、`missingBelowCount_strict_of_new` が適用できる。

### `natPairLex_wellFounded` (L133)

**主張:** 自然数の組の上の辞書式順序 `Prod.Lex Nat.lt Nat.lt` は整礎である。

**証明:** 各成分の `<` が整礎であることから、標準の補題 `Prod.lexAccessible` により各点の到達可能性(Acc)が従う。

### `historyBudgetProgress_wellFounded` (L144)

**主張:** `HistoryBudgetProgress m` は整礎である。すなわちこのランクで無限に減少し続ける列は存在しない。

**証明:** ランク写像 `historyBudgetRank` に沿った引き戻し。ランク値の到達可能性に関する帰納法で、ノード自身の到達可能性を示す標準的な議論である。

### `historyBudgetProgress_of_budgetDrop` (L161)

**主張:** 予算が厳密に減れば、値成分によらず `HistoryBudgetProgress` が成り立つ(辞書式の左分岐)。

**証明:** 定義より直ちに従う。

### `historyBudgetProgress_of_valueDrop` (L171)

**主張:** 時刻が進み(`parentTime ≤ childTime`)、値が厳密に減れば `HistoryBudgetProgress` が成り立つ。

**証明:** `missingBelowCount_antitone` により予算は減少方向にしか動かない。予算が等しければ右分岐(値の減少)、既に厳密に減っていれば左分岐が適用される。いずれにせよランクは下がる。

### `natPairLex_trans` (L188)

**主張:** 組の辞書式順序は推移的である。

**証明:** 左・右分岐の 4 通りの場合分けで、各成分の `<` の推移性に帰着する。

### `HistoryBudgetProgress.trans` (L211)

**主張:** 履歴予算の進捗は合成できる。通常減算の前置区間の後に局所的な低商ステップが続くとき、この推移性が全体の進捗を与える。

**証明:** `natPairLex_trans` の直接の帰結。

### `natTripleLex_wellFounded` (L246)

**主張:** 右入れ子の三成分辞書式順序は整礎である。

**証明:** 第一成分の `<` の整礎性と、残り二成分の `natPairLex_wellFounded` を `Prod.lexAccessible` で合成する。

### `natTripleLex_trans` (L256)

**主張:** 三成分辞書式順序は推移的である。

**証明:** 二成分の場合と同じ場合分けで、内側は `natPairLex_trans` に帰着する。

### `historySearchProgress_wellFounded` (L280)

**主張:** `HistorySearchProgress m` は整礎である。

**証明:** `historySearchRank` に沿った三成分順序の引き戻し。`historyBudgetProgress_wellFounded` と同じ議論である。

### `HistorySearchProgress.trans` (L296)

**主張:** 三成分の探索進捗は合成できる。

**証明:** `natTripleLex_trans` の直接の帰結。

### `historySearchProgress_of_budgetDrop` (L305)

**主張:** horizon での予算が厳密に減れば、親成分・軌道成分によらず三成分ランクは下がる。

**証明:** 辞書式の左分岐。

### `historySearchProgress_of_parentDrop` (L318)

**主張:** horizon が後退せず(`parentHorizon ≤ childHorizon`)、アクティブ親の値が厳密に減るなら三成分ランクは下がる。

**証明:** 予算は antitone なので、不変なら第二成分の減少(中央分岐)、既に減っていれば左分岐。

### `historySearchProgress_of_orbitValueDrop` (L339)

**主張:** 親成分が不変で horizon が後退せず、局所軌道値が厳密に減るなら三成分ランクは下がる。

**証明:** 同様に、予算が不変なら第三成分の減少、減っていれば左分岐。

### `natPairLex_embed_fixedMiddle` (L359)

**主張:** 固定した中央成分を挿入すると、二成分の辞書式減少は三成分の辞書式減少に埋め込まれる。

**証明:** 左分岐は左分岐へ、右分岐は「中央不変・右減少」へ写る。

### `HistoryBudgetProgress.toHistorySearchProgress` (L374)

**主張:** 局所的な `HistoryBudgetProgress` の各ステップは、任意のアクティブ親の値を固定したまま三成分の探索ステップになる。

**証明:** `natPairLex_embed_fixedMiddle` に親の値を中央成分として渡すだけである。局所座標力学の定理群(予算または軌道値を下げる)を、親の義務を保ったまま大域探索へ持ち込めることを意味する。

### `historySearchOracle_reaches_from` (L394)

**主張:** 全域の `HistorySearchOracle m` があれば、任意の開始ノードから `∃ t, a t = m` が従う。

**証明:** `historySearchProgress_wellFounded` による整礎帰納法。各ノードでオラクルが目標出現を返せば終了、真に小さい子を返せば帰納法の仮定を子に適用する。ランクの無限下降はないので、有限回で必ず目標出現に到達する。

### `historySearchOracle_implies_occurs` (L406)

**主張:** 全域の履歴探索オラクル一つから、開始状態の選択なしに目標の出現が従う。

**証明:** ノード `⟨0, 0, 0⟩` を開始点として前定理を適用する。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「三成分履歴ランク」段階に対応する。`missingBelowCount` は本リポジトリで最も広く使われる量であり、`HistoryFrontier` の各フロンティア定理はここで用意した `budgetDrop` / `parentDrop` / `orbitValueDrop` の三種の進捗補題へ帰着する。さらに `PhaseSearch` の四成分位相ランクは第一成分としてこの履歴予算をそのまま採用し、`natTripleLex_wellFounded` を内側順序として再利用する。`Crossing*` や `PermanentAbove*` の後続解析でも、予算の antitone 性と初出による厳密下降(`missingBelowCount_strict_of_firstAt`)が繰り返し使われる。
