# NormalClosure

**役割:** 子 domain を強い負 normal 不変量から `PhaseSemanticInvariant` へ弱めることで、`NormalPhase` の障害のうち parent-drop を完全に、前進エポック脱出をランク等式の一点(sharp obstruction)を除いて閉じる。

## このモジュールの役割

`NormalPhase` の分類は「負ポテンシャル不変量を子で再建できるか」を基準としたため、二種類の normal 障害が残った。本モジュールの観察は、子に要求すべきは強い負不変量ではなく、既存の統合意味的 domain `PhaseSemanticInvariant`(canonical start・normal・debt・crossing recovery の四構成子)で十分だ、というものである。初出値から通常 normal 証明書を作る補題を軸に、parent-drop 障害は無条件に閉じ、前進脱出は「新値が target 未満・予算不変・anchor がちょうど現在値」というランク等式の残余 `NormalEpochSharpObstruction` だけを残して閉じる。結果として負 normal 一歩の残余は、この sharp 残余と debt-anchor 境界の二つに絞られる。

## 主要な定義

### `NormalEpochSharpObstruction` (L146)

前進エポック脱出の残余配置。時刻 `n` から `time` への前進で

- `a time < target < a n`(新値は target 未満へ下方横断、旧値は target 超)
- `activeParent = a n`(anchor が現在値ちょうど)
- `missingBelowCount target time = missingBelowCount target n`(履歴予算不変)
- `a time < a n`(軌道値は下降)

が同時に成り立つ状態である。missingBelowCount(履歴予算)は「時刻までに未出である target 未満の値の個数」で、四成分ランクの第一成分である。

### `NegativeNormalSemanticResidual` (L312)

意味的 domain へ弱めた後に残る義務。`epoch_sharp`(上記の残余)と `debt_anchor`(`NormalPhase` の debt-anchor 障害をそのまま引き継いだもの)の二構成子を持つ。旧来の一般的な `NormalPhaseObstruction` は現れない。

## 定理と証明

### 補助補題 (L7)

`natQuadLex_fst_le`・`natQuadLex_tail_of_fst_eq`・`natTripleLex_tail_of_fst_eq`・`natPairLex_tail_of_fst_eq`(L7〜L52)は、四成分辞書式順序の比較から成分ごとの情報を取り出す純粋に技術的な補題である。第一成分は広義に減少し、第一成分が等しければ残りの三成分の辞書式比較が成り立つ、という形の分解を順に与える。

### `phaseSearchProgress_of_horizonAndAnchor` (L56)

**主張:** normal ノード同士で、horizon が広義に増加し(`parentHorizon ≤ childHorizon`)、anchor が厳密に減少する(`childAnchor < parentAnchor`)なら、`PhaseSearchProgress` が成り立つ。

**証明:** 履歴予算 `missingBelowCount` は horizon について反単調(時間が進むと未出値は増えない)なので、子の予算は親以下である。厳密に減っていれば第一成分の下降、等しければ第二成分 anchor の厳密下降が辞書式順序を下げる。

### `firstAt_normalSearchInvariant` (L77)

**主張:** `target > 0`、`target ≤ value`、`FirstAt a value firstTime`、`firstTime ≤ horizon` なら、ノード `⟨horizon, value, normal, value⟩` は `NormalSearchInvariant`(通常 normal 証明書)を満たす。

**証明:** `a 0 = 0 < target ≤ value` より初出時刻は正である。正時刻には商・剰余表示 `CoordinatesAt firstTime q r` が存在するので、証明書の全フィールドが揃う。

### `normalParentDrop_phaseSemantic` (L104)

**主張:** parent-drop 証拠(新 anchor `value` が初出値で `value < activeParent`)があれば、ノード `⟨max horizon firstTime, value, normal, value⟩` は `PhaseSemanticInvariant` を満たし、元の親からのランク進捗を持つ。つまり parent-drop 障害は、強い負不変量を要求したことによる人工的な障害であった。

**証明:** 意味的性は `firstAt_normalSearchInvariant` から直ちに従う(`firstTime ≤ max horizon firstTime`)。進捗については、証拠が持つ元のランク進捗の第一成分から `missingBelowCount target horizon ≤ missingBelowCount target n` を取り出し、反単調性と合わせて子の予算が親以下であることを得る。予算が厳密に減っていれば第一成分で、等しければ anchor 下降 `value < activeParent` が第二成分で辞書式順序を下げる。

### `NormalEpochSharpObstruction.newValue_not_normal` (L155)

**主張:** sharp 残余の新値ノード `⟨time, a time, normal, a time⟩` は `NormalSearchInvariant` を満たさない。

**証明:** 通常証明書は anchor について `target ≤ value` を要求するが、残余では `a time < target` である。

### `NormalEpochSharpObstruction.oldValue_not_progress` (L165)

**主張:** 旧値からの再開ノード `⟨time, a n, normal, a n⟩` は親 `⟨n, activeParent, normal, a n⟩` に対してランク進捗を持たない。

**証明:** `activeParent = a n` と予算不変により、子と親の四成分ランクは(予算・anchor・位相・局所量が)すべて一致する。辞書式順序の分解補題を順に適用すると `a n < a n` が導かれ、矛盾する。つまり sharp 残余は「どちらの自然な子もランクを下げない」文字どおりのランク等式である。

### `normalEpochExit_phaseSemantic_or_sharp` (L187)

**主張:** 負 normal 不変量と前進脱出証拠のもとで、(i) 目標出現、(ii) 意味的な子とランク進捗、(iii) `NormalEpochSharpObstruction`、のいずれかが成り立つ。

**証明:** まず `target = a n` なら時刻 `n` で目標が出現している。以下 `target < a n` とし、新値と target の大小で分ける。

**場合1: `target ≤ a time`。** 現在値 `a time` は自分自身の履歴に属するので初出時刻を持ち、子 `⟨time, a time, normal, a time⟩` は `firstAt_normalSearchInvariant` により意味的である。進捗は予算の比較による。予算が厳密に減れば第一成分で下降する。予算が等しい場合は、脱出証拠のランク進捗を辞書式分解すると局所量の下降 `a time < a n` が残っているはずであり、`a n ≤ activeParent` と合わせて anchor `a time < activeParent` の厳密下降を得る。

**場合2: `a time < target`。** 予算を `n` と `time` で比較する。厳密に減っていれば、旧値から再開する子 `⟨time, a n, normal, a n⟩`(意味的性は `a n` の初出時刻から)が第一成分で下降する。予算が等しい場合はさらに anchor で分ける。`a n < activeParent` なら同じ再開子が `phaseSearchProgress_of_horizonAndAnchor` により進捗する。`activeParent = a n` の場合が唯一残る配置で、このとき脱出証拠の進捗を辞書式分解すると軌道値下降 `a time < a n` が取り出せ、五条件すべてが揃った `NormalEpochSharpObstruction` を返す。

### `normalPhaseInvariant_phaseSemantic_progress` (L285)

**主張:** 完全な負 normal 不変量を持つノードは、常に弱い意味的 normal ノード `⟨n, a n, normal, a n⟩` へ正規化でき、元のノードが親 `parent` に対して持っていたランク進捗を保存する。

**証明:** 意味的性は `a n` の初出時刻から。anchor について `a n = activeParent` なら数値ノードは変わらないので元の進捗をそのまま使う。`a n < activeParent` なら正規化自体が anchor を下げるので、`phaseSearchProgress_of_horizonAndAnchor`(horizon 不変・anchor 下降)による進捗を元の進捗と推移律で合成する。

### `negativeNormal_phaseSemanticStep_or_residual` (L332)

**主張:** 負 normal 不変量のもとで、(i) 目標出現、(ii) `PhaseSemanticInvariant` を満たす子とランク進捗、(iii) `NegativeNormalSemanticResidual`、のいずれかが成り立つ。

**証明:** `negativeNormal_classify`(`NormalPhase`)の五分岐を閉じ直す。`normal_child` は `normalPhaseInvariant_phaseSemantic_progress` で正規化して (ii) へ。`debt_child` は debt 構成子でそのまま (ii) へ。`parent_drop` 障害は `normalParentDrop_phaseSemantic` により無条件に (ii) へ。`epoch_exit` 障害は `normalEpochExit_phaseSemantic_or_sharp` により (i)・(ii)・`epoch_sharp` 残余のいずれかへ。debt-anchor 障害は本モジュールの対象外なのでそのまま (iii) の `debt_anchor` として保持する。

## 全体の中での位置づけ

証明地図の「負エポック位相接続」を意味的 domain の言葉で閉じる中核である。ここで残された `epoch_sharp` 残余は `BoundaryAudit` の `NormalEpochSharpObstruction.target_occurs`(下方横断は予算を消費するので予算不変と両立しない)により目標出現へ変換され、debt-anchor 残余も同所で処理されて、`NormalComplete` の無条件閉包 `negativeNormal_phaseSemanticStep` に至る。また `firstAt_normalSearchInvariant` と `phaseSearchProgress_of_horizonAndAnchor` は、`NormalProvenance`・`TypedNormalProvenance`・`EarlyForcedCandidateClosure`・`CrossingFrontier` など後段の多くのモジュールが共有する基礎補題である。
