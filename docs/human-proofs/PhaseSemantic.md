# PhaseSemantic

**役割:** canonical 開始・normal・debt・crossing 回復を統合した proof-carrying な意味的探索 domain を定義し、その中で debt の自己退出・アンカー境界・crossing 進入を閉じる。

## このモジュールの役割

`PhaseSearchStart` の制限オラクルは任意の述語 `Valid` を許すが、実際に探索を完成させるには、「実軌道・履歴・座標に関する証明を伴うノードだけ」を対象とする具体的な domain が必要である。本モジュールはその最初の統合版 `PhaseSemanticInvariant` を定義する。これは canonical 開始、通常の normal ノード、debt ノード、crossing 回復(target 未満の値から強制加算で target 以上へ上向き横断した直後の状態)の 4 種のコンストラクタを持つ帰納的命題であり、数値の `PhaseSearchNode` は小さなランク鍵のまま、各種の局所不変量を証明書として外付けする。さらに、この domain が主要な遷移(canonical 開始の normal 化、strong debt の自己退出、`anchor = value+1` 境界、debt からの crossing 進入)で保存されることを示し、domain を `Valid` に選んだ制限オラクル `SemanticPhaseSearchOracle` から目標到達が従うことを確認する。

## 主要な定義

### `NormalSearchCertificate` (L13)

通常の normal 探索ノードの意味的証拠。ノードが `⟨horizon, value, normal, value⟩` の形(アンカーと局所量がともに `value`)であること、`0 < target ≤ value`、`value` の初出時刻 `firstTime` が horizon 以内にあること(`FirstAt a value firstTime`、`firstTime ≤ horizon`)、そして初出時刻における座標 `CoordinatesAt firstTime q r` を保持する。数値 tuple には現在のアンカー・値だけを置き、初出時刻と座標は存在量化された証明書側に retain する。

### `NormalSearchInvariant` (L24)

ある `value, firstTime, q, r` について `NormalSearchCertificate` が成り立つこと。注意: この証明書は「`value = a horizon`」も「`target ≤ horizon+1`」も含まない弱い不変量であり、過去の初出値と後の horizon の組み合わせを許す。この弱さが後に `NormalSemanticBoundary` で反例として顕在化し、`OrbitReadyNormalCertificate` などへの精密化を要求することになる(証明地図「現在の一点」参照)。

### `CrossingSearchCertificate` (L33)

強い crossing 回復ノードの意味的証拠。ノードは数値的には normal だが(`⟨horizon, a crossingTime, normal, a crossingTime⟩`)、通常の normal ノードではない: そのアンカーは target 未満だった横断直前の値である。旧 debt アンカー `oldAnchor`、横断時刻 `crossingTime`、加算後の座標を `CrossingRecoveryInvariant` として保持する。数値 tuple 単独では符号化できない情報を wrapper が記憶する。

### `CrossingSearchInvariant` (L42)

ある `oldAnchor, crossingTime, quotient, remainder` について `CrossingSearchCertificate` が成り立つこと。

### `PhaseSemanticInvariant` (L54)

制限位相探索のための意味的 domain。4 つのコンストラクタ

* `canonical_start`: `TargetStartInvariant` を持つ canonical 開始、
* `normal`: `NormalSearchInvariant` を持つ通常ノード、
* `debt`: `DebtInvariant`(blocker の値・初出時刻・`value < anchorParent` などを保持する strong debt 証明書)を持つ負債ノード、
* `crossing_recovery`: `CrossingSearchInvariant` を持つ crossing 回復ノード

を持つ帰納型である。各コンストラクタが proof-carrying である一方、`PhaseSearchNode` は小さな数値ランク鍵に留まるので、異なる局所不変量を互換であるかのように混同せずに共存させられる。

### `SemanticPhaseSearchOracle` (L216)

意味的 domain `PhaseSemanticInvariant target` を `Valid` に選んだ `RestrictedPhaseSearchOracle`。オラクル構成者は上記 4 形のノードだけを扱えばよい。

## 定理と証明

### `targetStartInvariant_phaseSemantic` (L71)

**主張:** すべての certified canonical 開始は統合意味 domain に属する。

**証明:** コンストラクタ `canonical_start` を適用するだけである。

### `targetStartInvariant_normal` (L80)

**主張:** 正の目標の canonical 開始は、一般の normal 探索証明書も持つ。特に、現在値の初出が選ばれた開始時刻より早い場合でも、その初出時刻での座標が存在する。

**証明:** `TargetStartCertificate` から `target ≤ a n` と、初出時刻 `f ≤ n` の初出証明を取り出す。`f = 0` なら初出値は `a 0 = 0` となり `target ≤ 0` に矛盾するので `f > 0`。正の時刻には必ず座標が存在する(`exists_coordinatesAt`)ので、`f` での座標を選んで `NormalSearchCertificate` の全フィールドを埋める。ノード形の条件は `targetStartNode n = ⟨n, a n, normal, a n⟩` により自動的に満たされる。

### `targetStartInvariant_phaseSemantic_normal` (L105)

**主張:** したがって canonical 開始は、数値ノードを変えずに同じ意味 domain の ordinary-normal 部へ入れる。

**証明:** 前定理の証明書に `normal` コンストラクタを適用する。

### `debtInvariant_selfExit_phaseSemantic` (L118)

**主張:** strong debt には常に domain 保存的な自己退出がある: debt の値 `value` 自身から normal 探索を再開する子 `⟨horizon, value, normal, value⟩` は意味 domain に属し、親 debt ノードからの厳密なランク下降を持つ。

**証明:** `DebtInvariant` は `target ≤ value`、`value` の初出証明、`firstTime < horizon`、そして `value < anchorParent` を保持する。初出時刻は正(値が target 以上で正だから)なので座標が取れ、子の `NormalSearchCertificate` が組み上がる。ランクの下降は `phaseSearch_exitDebt_of_anchorDrop`: 子のアンカー `value` が親のアンカーより厳密に小さいので、debt → normal の位相増加はアンカー下降の背後に隠れる。

この定理は同時に、**この自己退出を将来制限したければ、それは normal 側の不変量の追加条件として述べるしかない**ことを明示している。現在の数値ランクにも意味的証明書にも、自己退出を禁じる情報は存在しない。

### `anchorBoundary_phaseSemantic_closure` (L149)

**主張:** 長さ 1 の境界 `anchor = value + 1` は意味 domain の内部で閉じる。目標との一致なら出現の証拠、そうでなければ着地値が certified normal 子となり、アンカーが厳密に減る。

**証明:** `AnchorBoundary` の定理 `anchorBoundary_target_or_exitNormal` が「出現」か「ランク下降付きの normal 退出」を返す。後者の場合、自己退出と同様に debt 証明書から `NormalSearchCertificate` を組み立て(初出時刻の正値性から座標を取得)、子を `normal` コンストラクタで domain に入れる。

### `debtCrossing_enters_phaseSemantic` (L181)

**主張:** 既存の厳密 crossing 遷移(debt 中の時刻 `n+1` で減算が阻止され、`a n < target` から target 以上へ横断する強制加算)は、専用の回復コンストラクタに入ることで統合意味 domain を保存する。目標の出現か、`crossing_recovery` の子 `⟨horizon, a n, normal, a n⟩` とランク下降が得られる。

**証明:** `DebtCrossing` の定理 `debtCrossing_enters_recovery` が、出現か、加算後座標付きの `CrossingRecoveryInvariant` とランク下降を返す。後者を `CrossingSearchCertificate`(旧アンカー `anchor`、横断時刻 `n`)に包み、`crossing_recovery` コンストラクタで domain に入れる。子のアンカーは横断直前の below-target 値 `a n` なので、旧アンカーが target 以上なら厳密なアンカー下降になっている。

### `exists_phaseSemantic_start` (L208)

**主張:** 統合意味不変量はそのまま制限オラクルの domain として使用可能であり、すべての正の目標はこの domain 内のノードを持つ。

**証明:** `exists_targetStartNode` の canonical 開始ノードを `canonical_start` コンストラクタで包む。

### `semanticPhaseSearchOracle_implies_occurs` (L221)

**主張:** 意味的オラクルは上記 4 種の certified ノード形だけを扱えばよく、それがあれば目標は出現する。

**証明:** `targetStart_reaches_of_restrictedOracle` に、`Valid := PhaseSemanticInvariant target`、開始の包含(canonical 開始は `canonical_start` で domain に入る)、および仮定のオラクルを渡す。

## 全体の中での位置づけ

証明地図の「負債・crossing閉包」から「意味的探索domain」への入口であり、用語集の「semantic domain / 意味的domain」の定義実体である。`PhaseSearchStart` の制限オラクルスキーマ、`DebtInvariant` / `AnchorBoundary` / `DebtCrossing`(`CrossingRecovery`)の局所閉包定理を統合し、探索対象を数値 tuple 全体から proof-carrying なノードへ絞った。ただし `NormalSearchInvariant` の weak normal constructor は「過去の初出値 + 後の horizon」の組み合わせを許すため、任意の normal ノードに局所エポック定理を適用することはできない。この境界は `NormalSemanticBoundary` で反例として証明され、以後 `OrbitReadyNormalCertificate`、`NormalProvenance`、`ExtendedHistoryNormal` などによる精密化(refined domain)へと発展する。すなわち本モジュールは、完成形ではなく「どの意味情報をノードに持たせるべきか」を確定させた基準点である。
