# NormalPhase

**役割:** 負ポテンシャル領域にいる normal ノードの強い意味的不変量を定義し、負エポック定理の一歩を「目標出現・normal子・debt子・明示的な障害」に正確に分類する。

## このモジュールの役割

大域探索(`PhaseSearch`)のノードは数値の四つ組にすぎないため、そのままでは局所軌道解析を適用できない。本モジュールは、実軌道の負ポテンシャル状態(potential: 座標 `(q,r)` に対する符号付き量 `G(q,r) = r - upperTri(q)`)を表す normal ノードに対して、必要な証明をすべて束ねた強い不変量 `NormalPhaseInvariantAt` を定義する。そのうえで、負エポック(epoch: 同じ符号条件のもとで追跡する有限な軌道区間)の一歩を実行したとき、どの分岐で不変量が再建でき、どの分岐で証明インターフェースが不足するかを、命題として過不足なく分類する。この「障害を明示的に返す」設計により、後続の `NormalClosure`・`NormalComplete` は残された義務だけを個別に閉じればよくなる。

## 主要な定義

### `NormalPhaseInvariantAt` (L11)

目標 `target`、ノード `node`、時刻 `n`、座標 `(q,r)` について、次を同時に主張する強い不変量である。

- `node = ⟨n, anchorParent, normal, a n⟩`: ノードが実際に時刻 `n` の軌道値を局所量として持つ
- `target ≤ n+1`(時刻準備)、`target ≤ a n ≤ anchorParent`(値と anchor の挟み込み)
- `CoordinatesAt n q r`: 現在時刻での商・剰余表示
- `potential q r < 0`: 負領域にいること

anchor(anchorParent: 探索中に基準として固定する親の値)は現在値より大きくてもよいが、必ず現在値の上界である。これは履歴フロンティア補題群へ渡すための輸送仮定である。

### `NormalPhaseInvariant` (L22)

`NormalPhaseInvariantAt` の時刻・座標を存在量化した形。「このノードはある負ポテンシャル軌道状態を表している」という命題になる。

### `NormalParentDropEvidence` (L29)

負エポック定理の「親値下降」分岐が保持する証拠。子は `⟨horizon, value, normal, a horizon⟩` の形で、新 anchor `value` は `target ≤ value` を満たす真の初出値(`FirstAt a value firstTime`)、かつ `value < parent.anchorParent`(anchor の厳密下降)であり、ランク進捗 `PhaseSearchProgress` を伴う。ただし horizon での軌道値が target 以上であることや負ポテンシャルであることは主張しない。

### `NormalEpochExitEvidence` (L41)

前進軌道分岐が保持する証拠。子は `⟨time, parent.anchorParent, normal, a time⟩` で、時刻の前進 `parent.horizon < time`、時刻準備 `target ≤ time+1`、新時刻での座標、ランク進捗を持つ。負ポテンシャルや `target ≤ a time ≤ anchor` は結果型に含まれない。

### `NormalPhaseObstruction` (L52)

上記二種類の子について、証拠は揃っているのに `NormalPhaseInvariant` を再建できない場合を表す。`parent_drop` と `epoch_exit` の二構成子があり、それぞれ証拠と「不変量が閉じない」ことの否定を明示的に持つ。

### `NegativeNormalOutcome` (L74)

負エポック一歩の完全分類。五つの構成子を持つ。

1. `target_occurs`: 目標が軌道に出現する。
2. `normal_child`: `NormalPhaseInvariant` を再建できた normal 子とランク進捗。
3. `debt_child`: 完全な `DebtInvariant`(debt: 通常探索へ戻る前に解消すべき局所的な証明義務)を持つ debt 子とランク進捗。
4. `normal_obstruction`: 上記の normal 障害。
5. `debt_anchor_obstruction`: debt 側の障害。`DebtInvariant` の全条件のうち `value < anchorParent` だけが欠け、その字義どおりの否定 `anchorParent ≤ value` を記録する。

### `NegativePhaseInvariant` (L173)

normal 側の `NormalPhaseInvariant` と debt 側の `DebtInvariant` の選言。負領域の normal と debt が自然に共有する意味的 domain である。

### `NegativeNormalRestrictedObstruction` (L179)

`NegativeNormalOutcome` の二種類の障害だけを取り出した残余型。restricted oracle(oracle: 「各探索ノードで目標到達または真に小さい次ノードを構成できる」という証明義務)の一節を負エポック定理から直接供給しようとしたときに残る義務を表す。

## 定理と証明

### `negativeNormal_classify` (L104)

**主張:** `target > 0` とし、ノード `⟨n, activeParent, normal, a n⟩` が `NormalPhaseInvariantAt` を満たすとする。このとき `NegativeNormalOutcome` の五分岐のいずれかが成り立つ。

**証明:** 負エポックの統合定理 `negative_epoch_historySearchOutcome_or_qOneDebt`(`HistoryFrontier`)を不変量の各仮定に適用する。この定理は四つの選択肢を返すので、それぞれを処理する。

1. **目標出現**: そのまま `target_occurs`。
2. **親値下降**: ある horizon と初出値 `y`(`target ≤ y`、`FirstAt a y fy`、`y < activeParent`)と履歴探索進捗が得られる。子を `⟨horizon, y, normal, a horizon⟩` と置き、履歴進捗を位相進捗 `PhaseSearchProgress` へ持ち上げる。排中律により `NormalPhaseInvariant` が子で再建できるかどうかを場合分けし、できれば `normal_child`、できなければ証拠を `NormalParentDropEvidence` に詰めて `normal_obstruction`(`parent_drop`)とする。
3. **前進軌道**: ある `u > n` と座標が得られる。子 `⟨u, activeParent, normal, a u⟩` について同様に場合分けし、`normal_child` または `normal_obstruction`(`epoch_exit`)を返す。時刻準備 `target ≤ u+1` は元の `target ≤ n+1` と `n < u` から従う。
4. **商1の借り端点**: 商が1の一段借り(borrow: 時刻の法が変わる際の算術的な繰り下がり)で非負かつ target 未満のポテンシャルに着地した場合。`qOneDebt_target_or_phaseSearchProgress` を適用すると、目標出現か、初出値 `y`(`target ≤ y`、初出時刻 `fy < t`)を伴う debt ノード `⟨t, activeParent, debt, fy⟩` への厳密ランク進捗が得られる。`y < activeParent` なら `DebtInvariant` の全条件が揃うので `debt_child`、そうでなければ `anchorParent ≤ y` を明記して `debt_anchor_obstruction` とする。

### `negativeNormal_restrictedStep_or_obstruction` (L197)

**主張:** 同じ仮定の下で、(i) 目標出現、(ii) `NegativePhaseInvariant` を満たす子とランク進捗、(iii) `NegativeNormalRestrictedObstruction`、のいずれかが成り立つ。

**証明:** `negativeNormal_classify` の五分岐を機械的に振り分けるだけである。`normal_child` は (ii) の normal 側、`debt_child` は (ii) の debt 側に入り、二種類の障害はそれぞれ (iii) の対応する構成子となる。

## 全体の中での位置づけ

証明地図の「負エポック位相接続」から「意味的探索domain」への橋渡しの起点である。本モジュールの障害分類は `NormalClosure` に直接引き継がれ、そこで target 子 domain を `PhaseSemanticInvariant` に弱めることで `parent_drop` 障害と `epoch_exit` 障害の大部分が閉じ、最終的に `NormalComplete` が負 normal の完全閉包を与える。`NormalPhaseInvariantAt` 自体は `NormalSemanticBoundary` の `OrbitReadyNormalCertificate` から負ポテンシャルの場合に再構成され(`toNormalPhaseInvariantAt`)、orbit-ready normal の局所 totality の一角を支える。
