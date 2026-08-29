# CrossingRefinedBoundary

**役割:** crossing recoveryノードからの脱出は履歴予算の厳密低下を必ず伴うこと、同一horizonのrefined後続はcrossingに留まることを、ランクの算術だけから証明する。

## このモジュールの役割

crossing recoveryノード(target未満の値からの強制加算横断を記録するノード)は、意図的にpre-crossing値、すなわちtarget未満の値を数値anchor(ランク比較の基準となる親値)に採用している。一方、refined domainの非crossing成分——orbit-ready current、ready debt、extended-history normal——のanchorはすべてtarget以上である。本モジュールはこの符号差だけから、crossingノードから非crossing子への任意のランク辺(rank edge)がanchor成分では成立し得ず、外側の履歴予算成分`missingBelowCount`(その時刻までに未出であるtarget未満の値の個数)の厳密低下を必ず伴うことを示す。これは生成元情報(provenance)の不足ではなく、ランクそのものの障害であることを確定する境界定理群である。

## 主要な定義

### `RefinedNonCrossingInvariant` (L17)

refined domainの非crossing部分、すなわち`ReadyCurrentOrDebtInvariant ∨ ExtendedHistoryNormalInvariant`である。crossing成分だけを除いた領域を一語で指すために定義する。

## 定理と証明

### `RefinedNonCrossingInvariant.target_le_anchor` (L23)

**主張:** 非crossing refinedノードのanchorはtarget以上である: `target ≤ node.anchorParent`。

**証明:** 三つの成分ごとに確かめる。orbit-ready currentノードでは証明書がノードの形`⟨time, a(time), normal, a(time)⟩`を保証し、anchorは`a(time)`で、証明書の`target ≤ a(time)`から従う。ready debtノードでは、debt証明書が`target ≤ value < anchor`を保持しており、推移律で従う。extended-history normalノードでは、anchorは代表時刻の値`a(representativeTime)`であり、証明書が`target ≤ a(representativeTime)`を持つ。

### `CrossingSearchInvariant.anchor_lt_target` (L46)

**主張:** crossing recoveryノードの数値anchorはtargetより厳密に小さい: `node.anchorParent < target`。

**証明:** crossing証明書はノードの形が`⟨horizon, a(crossingTime), normal, a(crossingTime)⟩`であることを保証する。anchorはpre-crossing値`a(crossingTime)`であり、厳密crossingの定義(`DebtCrossing`)の第一成分がまさに`a(crossingTime) < target`である。

### `crossing_to_nonCrossing_progress_forces_budgetDrop` (L61)

**主張:** crossing親から非crossing refined子への任意のランク進捗`PhaseSearchProgress`は、履歴予算の厳密低下

```text
missingBelowCount target child.horizon < missingBelowCount target parent.horizon
```

を強制する。予算が等しいままのanchor・位相・局所量による下降は算術的に不可能である。

**証明:** 四成分辞書式ランク`(missingBelowCount, anchor, phase, localMeasure)`の定義を展開する。辞書式比較の第一分岐が成立すれば、それがそのまま結論である。第一成分が等しい場合、第二成分の比較に進むが、前二定理により子のanchorはtarget以上、親のanchorはtarget未満なので、`child.anchor < parent.anchor`も`child.anchor = parent.anchor`もあり得ない(`target ≤ child.anchor`と`parent.anchor < target`から矛盾)。よって進捗は第一成分の厳密低下でしか起こり得ない。

### `crossing_no_sameHorizon_nonCrossing_progress` (L84)

**主張:** 特に、crossingノードは同一horizonの非crossing refined後続を持たない。将来の証明は、厳密な履歴予算イベントを顕在化させるか、より精密なcrossing内下降に留まらねばならない。

**証明:** 同一horizonなら`missingBelowCount`は両辺で等しく、前定理が要求する厳密低下と矛盾する。

### `crossing_refinedChild_budgetDrop_or_crossing` (L99)

**主張:** crossingノードの任意のrefined子(ランク進捗を伴う)の網羅的な形: 履歴予算が厳密に下がるか、さもなくば子自身がcrossing recovery状態である。

**証明:** 子のrefined domain三分岐で場合分けする。ready current/debtとextended-historyの二枝はいずれも非crossingなので、`crossing_to_nonCrossing_progress_forces_budgetDrop`により予算低下枝に入る。crossing枝はその証明書を返す。

### `crossing_sameHorizon_refinedChild_is_crossing` (L116)

**主張:** horizonが変わらないまま得られたcrossingノードのrefined後続は、必ずそれ自身crossingである。

**証明:** 前定理の二分岐のうち、予算低下枝は同一horizonでは`missingBelowCount`の非反射性に矛盾するので消え、crossing枝だけが残る。

### `crossingNumeric_progress_iff_budgetDrop_or_anchorDrop` (L133)

**主張:** crossing recoveryノードが使う数値形`⟨horizon, A, normal, A⟩`(anchorと局所量が同じ値`A`)同士については、ランク進捗は次と同値である:

```text
予算の厳密低下 ∨ (予算が等しい ∧ childAnchor < parentAnchor)
```

すなわち四成分ランクのうち実効的な厳密成分は履歴予算とtarget未満のcrossing anchorの二つだけであり、位相と局所座標はanchorが固定する定数の複製にすぎない。

**証明:** (⇒) 辞書式比較を順に剥がす。第一成分の勝ちなら予算低下である。第一成分が等しく第二成分の勝ちならanchor低下である。両方等しい場合、第三成分は双方`normal`の位相ランクで等しく、第四成分は双方anchorと同じ値なのでanchorが等しい以上等しい。よって厳密低下の余地はなく、この場合は起こらない。(⇐) 予算低下なら辞書式第一成分で進捗する。予算が等しくanchorが低下するなら、第一成分を書き換えたうえで第二成分の勝ちとして進捗を構成する。

## 全体の中での位置づけ

証明地図の「crossing rank境界」の行に対応し、状態は証明済みである。`RefinedOracleBoundary`が残した唯一の義務`CrossingRefinedStepHypothesis`について、その解の取り得る形を先に確定する役割を持つ。すなわち、crossingからの脱出には新しいbelow-target履歴値の発見(予算低下)が必須であり、さもなくばcrossing間のanchor下降を実際に構成するしかない。この二択は下流でそのまま使われる: `CrossingDowncrossRefined`は将来のdowncrossから予算低下枝を実現し、`CrossingBelowRefined`は本モジュールの同値定理(L133)を使ってcrossing継続の進捗・停留を正確に判定し、`PermanentAboveTail`のzero-budget解析も本境界に依拠する。
