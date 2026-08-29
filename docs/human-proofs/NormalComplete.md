# NormalComplete

**役割:** 負ポテンシャル normal ノードの一歩を、残余なしで「目標出現または意味的な子とランク進捗」へ閉じる完全閉包定理を与える。

## このモジュールの役割

`NormalClosure` の段階では、負 normal の一歩に `epoch_sharp`(ランク等式)と `debt_anchor` の二つの残余が残っていた。`BoundaryAudit` はこの両方が実は起こり得ない、あるいは目標出現に吸収されることを個別に証明した。本モジュールはそれらを統合し、負ポテンシャル normal ノードからの一歩が常に成功することを単一の定理として述べる。これにより「負領域の normal」は semantic 閉包済みの領域となり、orbit-ready normal の局所 totality(`OrbitReadyComplete`)や canonical 閉包(`CanonicalOracle`)の部品として無条件に使えるようになる。

## 定理と証明

### `negativeNormal_phaseSemanticStep` (L13)

**主張:** `target > 0` とし、ノード `⟨n, activeParent, normal, a n⟩` が負 normal 不変量 `NormalPhaseInvariantAt`(ノード形・`target ≤ n+1`・`target ≤ a n ≤ activeParent`・現在座標・`potential q r < 0`)を満たすとする。このとき

- ある時刻 `witness` で `a witness = target`(目標出現)、または
- `PhaseSemanticInvariant target child` かつ `PhaseSearchProgress target child ⟨n, activeParent, normal, a n⟩` を満たす子 `child` が存在する。

障害や残余の選択肢は存在しない。

**証明:** 負エポックの統合定理 `negative_epoch_historySearchOutcome_or_qOneDebt` を不変量に適用し、四つの分岐をそれぞれ処理する。

1. **目標出現**: そのまま結論の第一選択肢である。

2. **親値下降**: 得られた初出 anchor と厳密下降・進捗の情報を `NormalParentDropEvidence` に詰め、`normalParentDrop_phaseSemantic`(`NormalClosure`)を適用する。子 `⟨max horizon firstTime, value, normal, value⟩` が意味的な normal 子として得られ、ランク進捗も付いてくる。この分岐に残余はない。

3. **前進軌道脱出**: 証拠を `NormalEpochExitEvidence` に詰め、`normalEpochExit_phaseSemantic_or_sharp`(`NormalClosure`)を適用する。目標出現と意味的な子はそのまま結論に流れる。第三の可能性である sharp 残余(新値が target 未満へ下方横断・履歴予算不変・anchor がちょうど現在値)については、`NormalEpochSharpObstruction.target_occurs`(`BoundaryAudit`)を使う。その内容は次のとおりである: 時刻 `n` から `time` への区間で軌道は `target < a n` から `a time < target` へ下方横断しているから、downcrossing 定理により目標が出現するか、`target` 未満の新しい値の初出によって履歴予算が厳密に減るかのいずれかである。後者は残余が主張する予算不変 `missingBelowCount target time = missingBelowCount target n` と矛盾する。よって目標が出現する。すなわち sharp 残余は見かけ上の障害であり、実際には常に目標出現の証拠である。

4. **商1の借り端点**: 商1・一段借りで非負かつ target 未満のポテンシャルに着地する例外分岐には `normalPhase_qOneDebt_already_occurs`(`BoundaryAudit`)を適用する。その証明の要点は、`qOneDebt_target_or_diagonalSuccessor` がこの配置を「目標出現」または「対角的な例外配置 `n = t`、`target = t+1`、`a t = t`」へ分類することにある。後者では `target = t+1 > t = a t = a n` となり、負 normal 不変量が保持する下界 `target ≤ a n` と矛盾する。したがってこの分岐でも常に目標が出現する。

以上で四分岐すべてが結論の二択に収まる。

## 全体の中での位置づけ

証明地図の「負エポック位相接続」の最終形であり、負領域(negative region: `potential < 0` の座標領域)に関しては restricted oracle の一節が無条件に成立することを示す。`NormalSemanticBoundary` はこの定理を `OrbitReadyNormalCertificate.negative_phaseSemanticStep` として orbit-ready 証明書へ接続し、`CanonicalOracle` は canonical 開始点の負分岐でこれを使う。すなわち本定理は、`OrbitReadyNormalInvariant.phaseSemanticStep` が負・高ポテンシャル・非負アンダーシュート・level 0/1/2 の全分岐を閉じるという current-state normal の局所 totality のうち、負分岐を担う部品である。
