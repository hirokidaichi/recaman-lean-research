# CrossingFrontierRefined

**役割:** ready debt(horizon が target-ready な負債状態)を源とする crossing-frontier 初出の全分岐を refined domain へ昇格し、唯一残っていた二時計 middle 区間を extended-history normal 子として収容して residual-free の refined step を与える。

## このモジュールの役割

`HistoricalDebtBridge` は、crossing frontier で見つかった初出値(target 以上・旧 anchor 未満)を、その初出時刻と debt 時刻・horizon の位置関係で分類した: 目標出現、future current 子、より早い debt 子、そして「debt 時刻以後かつ horizon より前」という二時計 middle 区間の残余である。middle 区間は current 子にも debt 子にもならない本物の中間ケースだった。本モジュールは、源の debt が horizon readiness(`target ≤ horizon + 1`)を持つ ready debt であれば、この middle 区間をそのまま extended-history normal 子(初出時刻を representative time とし、horizon readiness を源から継承する historical normal 節点)として refined domain に収容できることを示す。これにより crossing-frontier 初出の refined step は残余なしに閉じる。

## 定理と証明

### `CrossingFrontierCurrentDebtOutcome.toReadyRefinedStep` (L17)

**主張:** `0 < target` と ready debt 源 `ReadyDebtInvariant target ⟨historyHorizon, debtAnchor, debt, debtTime⟩ debtValue debtTime` のもとで、crossing-frontier の分類結果 `CrossingFrontierCurrentDebtOutcome` の任意の分岐から、「目標の出現証人、または `OrbitReadyRefinedInvariant`(orbit-ready current / ready debt / extended-history / crossing のいずれかの refined 資格)と旧 debt 節点への `PhaseSearchProgress` を併せ持つ子」が得られる。

**証明:** 分類の四つの構成子を順に処理する。

- `target_occurs`: 出現証人をそのまま返す。
- `current_child`: 証明書が保持する future current 子は `targetStartNode firstTime = ⟨firstTime, a firstTime, normal, a firstTime⟩` であり、refined domain の第一分岐(orbit-ready current)にそのまま入る。進捗も証明書に含まれている。
- `debt_child`: より早い初出時刻への debt 子は、`DebtInvariant` としては証明書が供給するが、refined domain に入るには horizon readiness が要る。ここで子の horizon は源と同じ `historyHorizon` なので、源の `horizon_ready`(`target ≤ historyHorizon + 1`)をそのまま継承して `ReadyDebtInvariant` に格上げできる。
- `middle_residual`: 核心の分岐である。middle 証明書は `target < value`、初出 `FirstAt a value firstTime`、`value < debtAnchor`、`debtTime ≤ firstTime < historyHorizon`、および current 化が失敗する理由(初出時刻の時計が target に届かない、または初出時刻から horizon までに履歴予算が真に減っている)を保持する。まず `firstTime > 0` を確かめる: `firstTime = 0` なら時刻 0 の初出値は 0 だが `target < value = 0` は不可能である。正の時刻なので座標 `CoordinatesAt firstTime q r` が取れる。子として `⟨historyHorizon, a firstTime, normal, a firstTime⟩` を選び、`ExtendedHistoryNormalInvariant` の証明書を組み立てる: representative time は `firstTime`(`firstTime < historyHorizon` より horizon 以下)、horizon readiness は源の `horizon_ready` の継承、値条件 `target ≤ a firstTime` は `hfirst.1` と `target < value` から、座標は上で取ったものを使う。進捗は `value = a firstTime < debtAnchor` による anchor 降下(`phaseSearch_exitDebt_of_anchorDrop`)である。

middle 区間の要点は、current 化の失敗理由が何であれ、extended-history 証明書は representative time の時計条件を要求しない(要求するのは horizon の readiness だけ)ため、源の ready debt がちょうど欠けていた事実を供給することである。すなわち「二時計」問題 — 初出の時計と horizon の時計のずれ — は、historical normal の設計(representative time と history horizon の分離)にそのまま吸収される。

### `ReadyDebtInvariant.crossingFrontierFirstAt_refinedStep` (L80)

**主張:** ready debt 源と、crossing frontier で成功した初出(`target ≤ value`、`FirstAt a value firstTime`、`value < debtAnchor`)から、residual なしの refined step が得られる: 目標の出現証人、または `OrbitReadyRefinedInvariant` と `PhaseSearchProgress` を持つ子が必ず存在する。

**証明:** `HistoricalDebtBridge` の分類定理 `crossingFrontierFirstAt_currentOrDebt_or_middle` を、源の horizon readiness と debt 不変量に適用して四分岐の outcome を得る。あとは前定理 `toReadyRefinedStep` がすべての分岐を refined step に変換する。二定理の合成により、`CrossingFrontier` の段階では self-exit という保険に頼っていた crossing-frontier 初出の処理が、refined domain の中では構成的な子の供給として完結する。

## 全体の中での位置づけ

証明地図の「位相統合」層、行「historical 回避: refined 閉包済み」に対応する。`ReadyDebtRefined` の上に立ち、`HistoricalDebtBridge` が残した crossing frontier の二時計 middle 区間を horizon-ready extended-history 子へ収容することで、refined child domain(orbit-ready current / ready debt / extended-history / crossing)の constructor 監査を前進させる。この閉包の結果、`RefinedOracleBoundary` に残る未証明点は `CrossingSearchInvariant` 自身の provenance だけとなり、以降の `CrossingRefinedBoundary`・`CrossingDowncrossRefined`・`CrossingTailRefined` の crossing 境界解析へ焦点が移る。本モジュールの結果は `ExtendedHistoryDirectRefined` から使われる。
