# NormalProvenance

**役割:** 通常 normal ノードを「実軌道状態を表す current ノード」と「rank edge 付きの historical ノード」に分離する provenance 付き domain `ProvenancedNormalInvariant` を定義し、その基礎 API を証明する。

## このモジュールの役割

`NormalSemanticBoundary` により、弱い `NormalSearchInvariant` だけでは epoch 機構を適用できないことが確定した。しかし探索の途中で生じる normal 子は current 状態とは限らない。本モジュールは provenance(生成元証明: その子がどの局所定理からどの親を経て生成されたかの証明データ)という発想で、この二種類を型のレベルで分離する。current ノードは `OrbitReadyNormalInvariant` を携え、historical ノードは「信頼された非 normal ルートまたは既に provenance を持つ normal ノード」からの実際のランク下降 edge を携える。生の `NormalSearchInvariant` 単独では domain に入れない。これは意図的に domain API のみの構成であり、各 provenance ノードが局所後続を持つことまでは主張しない(それは extended-history 系モジュールの課題である)。

## 主要な定義

### `NormalProvenanceRoot` (L28)

historical normal 子を正当に生成しうる非 normal の意味的ノード。`canonical_start`(`TargetStartInvariant`)、`debt`(`DebtInvariant`)、`crossing_recovery`(`CrossingSearchInvariant`)の三構成子を持つ。通常 normal ノードは意図的に含まれない。normal からの再帰的閉包は下の `historical_from_normal` が担うので、弱い通常証明書が自分自身のルートになることはできない。

### `HistoricalNormalStep` (L45)

provenance を生む一回の normal 遷移が保持する正確なデータ。子の通常証明書 `NormalSearchInvariant target child` と、親から子への実際の大域ランク下降 `PhaseSearchProgress target child parent` の組である。

### `ProvenancedNormalInvariant` (L55)

精密化された通常 normal domain。帰納的に

1. `current`: `OrbitReadyNormalInvariant` を持つノード
2. `historical_from_root`: 非 normal ルートから一回の `HistoricalNormalStep` で到達したノード
3. `historical_from_normal`: 既に domain に属する normal 親から一回の `HistoricalNormalStep` で到達したノード

として定義される。すなわち orbit-ready な current ノードと、そこ(または非 normal ルート)から証明付きランク下降の有限鎖で到達できる normal 子を含む最小の domain である。

## 定理と証明

### `NormalProvenanceRoot.toPhaseSemanticInvariant` (L71)

**主張:** 信頼された非 normal ルートはすべて既存の統合意味的 domain に属する。

**証明:** 三構成子はそれぞれ `PhaseSemanticInvariant` の canonical_start・debt・crossing_recovery 構成子に一対一で対応する。

### `HistoricalNormalStep.target_positive` (L81) / `HistoricalNormalStep.toPhaseSemanticInvariant` (L91)

**主張:** historical 遷移の子は `0 < target` を満たし、旧意味的 domain に埋め込まれる。

**証明:** どちらも子が持つ通常証明書から直ちに従う(証明書は `target_positive` フィールドを持ち、normal 構成子で埋め込める)。後者の埋め込みは、provenance が別途 domain への加入を正当化した後で初めて使う想定である。

### `ProvenancedNormalInvariant.toNormalSearchInvariant` (L99)

**主張:** provenance を忘れると、ちょうど旧来の通常 normal 証明書が回収される。

**証明:** current の場合は orbit-ready 証明書の再構成定理(`NormalSemanticBoundary`)による。historical の二構成子は step が証明書を直接保持している。

### `ProvenancedNormalInvariant.target_positive` (L112) / `ProvenancedNormalInvariant.toPhaseSemanticInvariant` (L122)

**主張:** 目標の正値性は再帰的に provenance 付けされた全 historical 子を含む domain 全体の不変量であり、精密化 domain は `PhaseSemanticInvariant` の normal 構成子の保守的な強化である。

**証明:** どちらも前定理で通常証明書へ落としてから、その証明書のフィールド、または normal 構成子への埋め込みを使う。

### `OrbitReadyNormalInvariant.toProvenancedNormalInvariant` (L129)

**主張:** orbit-ready な current ノードは精密化 domain に直接入る。

**証明:** `current` 構成子そのものである。

### `TargetStartInvariant.toOrbitReadyNormalInvariant` (L137)

**主張:** `target > 0` なら、canonical 開始点(canonical start: 目標の直前領域で証明付きで選ばれる探索開始状態)は orbit-ready である。

**証明:** 開始証明書は開始時刻 `n` について、ノード形・時刻準備 `target ≤ n+1`・値準備 `target ≤ a n`・現在座標の存在をすべて保持しているので、その座標の証人を取り出せば orbit-ready 証明書の全フィールドが揃う。

### `TargetStartInvariant.toProvenancedNormalInvariant` (L153)

**主張:** 正の目標の canonical 開始点は、historical 構成子を経由せずに精密化 domain に属する。

**証明:** 前定理と `current` 構成子の合成である。

### `historicalNormalStep_of_firstAt` (L161)

**主張:** `target ≤ value` を満たす初出値(`FirstAt a value firstTime`、`firstTime ≤ horizon`)と、ノード `⟨horizon, value, normal, value⟩` への既証明のランク下降があれば、それらは一回の historical 遷移 `HistoricalNormalStep` をなす。

**証明:** 証明書部分は `firstAt_normalSearchInvariant`(`NormalClosure`)、進捗部分は仮定そのものである。後段のモジュールが historical 子を作るときの標準的な包装である。

### `DebtInvariant.selfExit_provenancedNormal` (L179)

**主張:** 強い debt 証明書を持つノードは、保持している初出値 `value` を anchor とする normal 子 `⟨parent.horizon, value, normal, value⟩` へ自己退出でき、その子は精密化 domain に属する。

**証明:** debt の自己退出定理 `debtInvariant_selfExit_phaseSemantic` が意味的性とランク進捗を与える(debt 証明書の `value < anchorParent` により anchor が厳密に下がり、debt から normal への復帰でもランクは下降する)。通常証明書は `firstAt_normalSearchInvariant` から、初出時刻が horizon 未満であることを使って作る。debt 証明書自身を `NormalProvenanceRoot.debt` としてルートに据え、`historical_from_root` で domain へ入れる。これは historical 加入の代表例である。

### `NormalParentDropEvidence.toProvenancedNormal` (L200)

**主張:** 親が精密化 domain に属する normal ノードのとき、parent-drop 証拠から作られる子 `⟨max horizon firstTime, value, normal, value⟩` も精密化 domain に属する。

**証明:** 閉包定理 `normalParentDrop_phaseSemantic`(`NormalClosure`)がランク進捗を与え、証明書は初出値から作る。親の provenance を `historical_from_normal` の source とする。すなわち parent-drop は provenance 鎖を一段延長する。

### `horizonMismatch_provenance_is_historical` (L225)

**主張:** `NormalSemanticBoundary` の mismatch 反例ノード `⟨2, 1, normal, 1⟩`(target 1)がもし精密化 domain に属するなら、その証明は必ず明示的な historical 親とランク下降 edge を露出する。current 構成子経由ではあり得ない。

**証明:** domain の帰納的定義で場合分けする。`current` の場合、`normalSearchInvariant_not_orbitReady`(`NormalSemanticBoundary`)がこのノードの orbit-ready 性を否定しているので矛盾する。残る二構成子はそれぞれ「ルート親と step」「provenance 付き親と step」を文字どおり与える。これは精密化 domain が境界反例を正しく historical 側へ隔離していることの検証である。

## 全体の中での位置づけ

証明地図の「意味的探索domain」段階の基礎 API である。ここで定義された `ProvenancedNormalInvariant` と `HistoricalNormalStep` の上に、`TypedNormalProvenance` が五種類の生成機構別 provenance を実装し、`ExtendedHistoryNormal` が historical ノードの局所後続定理を追求し、`CoverageDebtBridge`・`OrbitReadyAdapters` が CoverageStep や orbit-ready 側との接続を与える。current/historical の分離は、そのまま refined child domain(orbit-ready・ready debt・extended-history・crossing)の設計原理へ受け継がれる。
