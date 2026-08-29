# ExtendedHistoryNormal

**役割:** 代表時刻と履歴horizonが分離したhistorical normal nodeを定式化し、orbit-ready理論を再利用するための2条件(代表時刻の準備、履歴予算の安定)を分離した完全分類を与える。

## このモジュールの役割

大域探索で扱うnormal nodeには、「現在の軌道状態そのもの」ではなく、過去のある時刻の軌道値を保持したまま、履歴だけを後の時刻まで進めた状態が現れる。このとき値と座標が実際に成り立つ時刻を**代表時刻**(representative time)、未出値数を数える時刻を**履歴horizon**(history horizon)と呼び、両者を分離して保持するのが**extended-history node**である。本モジュールは、この最小限の証明書 `ExtendedHistoryNormalCertificate` を定義し、current-state用の完全定理(`OrbitReadyNormalCertificate.phaseSemanticStep`)を再利用できる条件を正確に切り出す。分類は全域的(total)であり、閉じない場合は失敗した前提条件そのものを残余(residual)として返す。残余は後続の `EarlyRepresentative*`、`ExtendedHistoryBudgetClosure` で閉じられる。

## 主要な定義

### `extendedHistoryRepresentativeNode` (L23)

代表時刻 `time` における現在状態そのもののnode `⟨time, a(time), normal, a(time)⟩` である。extended-history nodeを、この「代表時刻での現在node」と比較することで解析する。

### `ExtendedHistoryNormalCertificate` (L32)

historical ordinary-normal nodeの最小証明書。目標 `target`、node、代表時刻、商・剰余に対して次を保持する。

- `target > 0`
- nodeの形が `⟨node.horizon, a(代表時刻), normal, a(代表時刻)⟩` であること
- `代表時刻 ≤ node.horizon`
- **horizon time-readiness**: `target ≤ node.horizon + 1`
- `target ≤ a(代表時刻)`
- `CoordinatesAt 代表時刻 q r`(商・剰余座標が実際の軌道値に一致)

代表時刻自身のtime-readiness(`target ≤ 代表時刻 + 1`)は**仮定しない**。historicalなnodeを生成する機構が自然に保存できるのはhorizon側の条件だけだからである。

### `ExtendedHistoryNormalInvariant` (L43)

代表時刻・商・剰余を存在量化した包み。「あるextended-history証明書を持つnode」を表す。

## 定理と証明

### `ExtendedHistoryNormalCertificate.toOrbitReadyAtRepresentative` (L51)

**主張:** 代表時刻でのtime-readiness `target ≤ 代表時刻 + 1` を追加で与えれば、代表時刻の現在node `extendedHistoryRepresentativeNode` はorbit-ready normal証明書(値が実際に現在値であり、座標・目標下界・時刻条件を同時に持つ状態)を成す。

**証明:** 証明書の各フィールドがorbit-ready証明書の対応フィールドにそのまま写る。代表時刻の現在nodeでは値・anchor・局所値がすべて `a(代表時刻)` なので、node形状条件は定義から明らか。

### `ExtendedHistoryNormalCertificate.toNormalSearchInvariant` (L71)

**主張:** 最小のextended-history証明書は、従来の広い(弱い)ordinary-normal証明書 `NormalSearchInvariant` の正当なインスタンスでもある。

**証明:** まず `代表時刻 > 0` を確かめる。代表時刻が0なら `a(0) = 0` であり、`target ≤ a(0) = 0` が `target > 0` に矛盾する。値 `a(代表時刻)` は時刻`代表時刻`までの履歴に属するから、その初出時刻 `firstTime ≤ 代表時刻` が取れる。`firstTime = 0` なら初出値は0となり同様に矛盾するので `firstTime > 0` であり、初出時刻での商・剰余座標が存在する。`firstTime ≤ 代表時刻 ≤ horizon` により、初出時刻・座標・目標下界をまとめて `NormalSearchInvariant` が得られる。ポイントは、値を「horizonでの現在値」と偽らず、証明済みの時刻順序だけで初出情報を輸送している点である。

### `ExtendedHistoryNormalCertificate.toPhaseSemanticInvariant` (L108)

**主張:** 前定理により、extended-history nodeは広いsemantic不変量 `PhaseSemanticInvariant` のnormal枝に埋め込める。1行の系である。

### `ExtendedHistoryNormalCertificate.transportProgress_of_budgetStable` (L118)

**主張:** 履歴予算(`missingBelowCount`、目標未満の未出値数)がhorizonと代表時刻で等しいとき、代表時刻の現在nodeからのあらゆるrank下降 `PhaseSearchProgress target child (代表node)` は、そのままhistorical node自身からの下降 `PhaseSearchProgress target child node` になる。

**証明:** 四成分rankは `(履歴予算, anchor, 位相rank, 局所値)` の辞書式順序である。node形状条件により、historical nodeのanchor・位相・局所値は代表nodeのそれと文字通り一致する。相違し得るのは第一成分の履歴予算だけであり、それが等しいと仮定したから、両nodeのrankは完全に一致する。ゆえにrank比較は書き換えだけで移る。

### `ExtendedHistoryNormalCertificate.progress_fromRepresentative_of_budgetGap` (L149)

**主張:** 逆に履歴予算がhorizonで真に落ちているとき(budget gap)、rankの向きは反対を向く: historical node自身がすでに代表nodeより辞書式に真に小さい。

**証明:** 第一成分の比較 `missingBelowCount target node.horizon < missingBelowCount target 代表時刻` がそのまま辞書式順序の第一成分での真の下降になる(`Prod.Lex.left`)。この定理は、budget gapのもとでは「代表nodeから下がるchild」をhistorical nodeからの下降として輸送できない理由を正確に述べている。childは代表nodeより下だが、historical nodeはさらに下にいるかもしれない。

### `ExtendedHistoryNormalCertificate.phaseSemanticStep_of_ready_stable` (L167)

**主張:** 2つの輸送条件(代表時刻の準備 `target ≤ 代表時刻 + 1`、および履歴予算の安定)が両方成り立つとき、extended-history nodeは完全に閉じる: 目標の出現証人が存在するか、semantic不変量を持つchildへの真のrank下降が存在する。

**証明:** orbit-ready完全定理を代表時刻に適用し、得られた下降を `transportProgress_of_budgetStable` で輸送する。追加の位相もrankも導入しない、orbit-ready理論の最も直接的な再利用である。

### `ExtendedHistoryNormalResidual` (L189)

**主張(定義):** 最小証明書の**正確な残余**を表す帰納命題。2つのconstructorを持つ。

- `representative_not_ready`: 代表時刻が早すぎる(`代表時刻 + 1 < target`)場合。このときorbit-ready定理を呼ぶ前に失敗する。値が目標を真に超えること(`target < a(代表時刻)`)も併せて記録する。
- `budget_transport`: 代表時刻は準備済みだが履歴予算が真に落ちている場合。semantic childと代表nodeからの正当な局所下降は得られているのに、rank輸送だけが欠けている、という状況を文字通り保持する。

### `ExtendedHistoryNormalCertificate.phaseSemanticStep_or_residual` (L216)

**主張:** 任意のextended-history証明書について、(i) 目標の出現、(ii) semantic childへの真のrank下降、(iii) 上記いずれかの残余、の三択が成り立つ。全域的かつ「正直な」分類である。

**証明:** まず `a(代表時刻) = target` なら出現。そうでなければ `target < a(代表時刻)` である。代表時刻が準備済みなら、orbit-ready完全定理を実行する。出現ならそのまま返し、childが得られた場合は履歴予算で場合分けする。予算が安定なら輸送して(ii)。安定でなければ、履歴予算の単調性(`missingBelowCount` は時間について非増加)から真のgapが従い、childと局所下降ごと `budget_transport` 残余に格納する。代表時刻が準備済みでなければ `representative_not_ready` 残余である。

### `ExtendedHistoryNormalInvariant.phaseSemanticStep_or_residual` (L248)

**主張:** 存在量化版の包み。代表時刻・座標を開いて前定理を適用するだけである。

### `extendedHistory_horizonReady_not_representativeReady` (L261)

**主張:** horizon readinessは代表時刻のreadinessを含意しない。具体例: `a(3) = 6` を目標5に対しhorizon 4で再利用したnode `⟨4, a(3), normal, a(3)⟩` は正当なextended-history証明書を持つ(`5 ≤ 4 + 1`)が、`5 ≤ 3 + 1` は偽である。

**証明:** 各フィールドをLeanカーネルの `decide` で数値検証する。これがepoch前提条件に関わる最小の例である。

### `extendedHistory_representativeReady_with_budgetGap` (L281)

**主張:** budget輸送は独立した真の境界である。目標4に対し、時刻3の代表状態はすでにtime-ready(`4 ≤ 3 + 1`)だが、履歴を時刻4まで延ばすとそれまで未出だった値2(`a(4) = 2`)が発見され、`missingBelowCount 4 4 < missingBelowCount 4 3` と第一rank成分が真に下がる。

**証明:** `decide` による数値検証。2つの残余がそれぞれ独立な実例を持つことが、以降のモジュールで両者を別々の機構で閉じる動機になる。

## 全体の中での位置づけ

証明地図の「意味的探索domain」段階に属する。`NormalSemanticBoundary` が示した弱いnormal証明書の反例を受けて、historical nodeに保持させるべき最小のproof-carrying dataを定めたのが本モジュールである。ここで特定された2残余は、`EarlyRepresentative`・`EarlyRepresentativeClosure`・`EarlyRepresentativeComplete`(代表時刻不準備)と `ExtendedHistoryBudgetClosure`(budget gap)で閉じられ、`ExtendedHistoryComplete` で残余なしの完全なsemantic stepに統合される。さらに `ExtendedHistoryDirectRefined` では同じ分類をrefined domainの上で直接構成し直す。
