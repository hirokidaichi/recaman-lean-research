# PermanentAboveCorridorRank

**役割:** canonical下側回廊(canonical below corridor)の内部遷移がすべて強制加算である場合を`AllForcedAdditionCorridor`として型付けし、return時刻がtarget未満に収まること、値が加算clockの総和に従うtelescoping式で厳密増加すること、および残りclock `target − time`によるwell-foundedなrankで回廊踏破が有限化されることを証明する。

## このモジュールの役割

`PermanentAboveCorridor.lean`は、fresh historical downcross endpoint(合法減算で初出したtarget未満の着地点)から、その後最初のweak upcrossing(canonical return)の直前までの有限軌道区間 — canonical below corridor — を抽出し、内部の合法減算がhistory budget(未出のtarget未満値の個数`missingBelowCount`)を厳密に下げることを示した。本モジュールはその補集合、すなわち内部遷移がひとつ残らず強制加算(forced addition: 減算先が負または既出のため加算せざるを得ない一歩)である回廊を扱う。この場合、return時刻は必ずtargetより前に来て、値は各stepで加えられるclockの総和どおりに厳密増加するため、回廊の中の前進は有限な残りclock rankで測れる。任意の遅延回廊(returnが即時でないもの)は「内部に合法減算がありbudgetが下がる」か「全強制加算で有限clock証明書を持つ」かの二形に完全分類される。ただしこのrankが有限化するのはreturnへの到達までであり、再基底化されたstationary crossing(`PermanentAboveCycleRebase.lean`の停留残余)からの脱出そのものは主張しない — その区別を型として明示することも本モジュールの役割である。

## 主要な定義

### `AllForcedAdditionCorridor` (L22)

回廊証明書`CanonicalBelowCorridorCertificate`(開始endpoint `downTime + 1`、canonical return `returnTime`)に対し、`downTime + 1 ≤ time < returnTime`を満たすすべての時刻`time`で減算が不可能(`¬ CanSubtract (time+1) (stateAt time)`)、すなわちreturn直前までの内部遷移がすべて強制加算であることを表す述語。

### `forcedClockSum` (L62)

強制加算runで加えられるclockの総和。再帰式
`forcedClockSum start 0 = 0`、
`forcedClockSum start (steps+1) = forcedClockSum start steps + (start + steps + 1)`
で定義され、`start`から`steps`歩の間に加算されるclock `start+1, …, start+steps`の和に相当する。

### `corridorClockRemaining` (L139)

targetまでの残りclock `target − time`。

### `CorridorClockProgress` (L141)

残りclockの厳密下降 `corridorClockRemaining target child < corridorClockRemaining target parent` を回廊内前進の進捗関係とする。

### `DelayedCanonicalCorridorOutcome` (L171)

遅延回廊の完全分類。constructorは二つ:

1. `internal_subtraction`: 内部時刻`time`での合法減算と、`missingBelowCount target (time+1) < missingBelowCount target time`という履歴予算の厳密下降。
2. `all_forced`: 全強制加算の証明、`returnTime < target`、およびgap上界 `returnTime − (downTime+1) < target − (downTime+1)`。

## 定理と証明

### `AllForcedAdditionCorridor.returnTime_lt_target` (L30)

**主張:** 遅延した(`downTime + 1 < returnTime`)全強制加算回廊のreturn時刻はtargetより前にある: `returnTime < target`。

**証明:** 最後の内部時刻`lastTime = returnTime − 1`を取る。この時刻での遷移は仮定により強制加算であり、その着地点`a returnTime`は回廊の内側なのでまだtarget未満である。回廊証明書の`internalForced_clockBelowTarget`(`PermanentAboveCorridor.lean`)は「着地後もtarget未満に留まる強制加算のstep clockはtarget未満」と述べるので、`lastTime + 1 = returnTime < target`が従う。直観的には、target未満の値にclock `returnTime`を加えてなおtarget未満なら、そのclock自体がtargetより小さいほかない。

### `AllForcedAdditionCorridor.gap_lt_targetGap` (L51)

**主張:** 回廊のgapは開始endpoint以後に残るtarget区間で抑えられる: `returnTime − (downTime+1) < target − (downTime+1)`。

**証明:** L30の`returnTime < target`から自然数の減算算術で直ちに従う。

### `AllForcedAdditionCorridor.value_eq_add_forcedClockSum` (L67)

**主張:** 全強制加算回廊の値は正確なtelescoping式に従う: `downTime + 1 + steps ≤ returnTime`なら
`a (downTime + 1 + steps) = a (downTime + 1) + forcedClockSum (downTime + 1) steps`。

**証明:** `steps`についての帰納法。0歩なら両辺一致。`steps + 1`歩目では、時刻`downTime + 1 + steps`の遷移が仮定により強制加算なので、レカマン数列の定義から`a (t+1) = a t + (t+1)`という加算式が成り立つ(`a_succ_of_not_canSubtract`)。帰納法の仮定でここまでの値を展開し、`forcedClockSum`の再帰式と合わせると総和がちょうど一致する。

### `AllForcedAdditionCorridor.value_strictMono` (L98)

**主張:** 全強制加算回廊の空でない任意の部分区間で軌道値は厳密増加する: `downTime + 1 ≤ earlier < later ≤ returnTime`なら`a earlier < a later`。

**証明:** 距離`later − earlier`についての帰納法。各内部stepは強制加算なので`a (t+1) = a t + (t+1) > a t`であり、一歩なら直ちに、複数歩なら帰納法の仮定と一歩分の増加を推移律でつなぐ。この局所的な増加は回廊内の事実であって、外側cycleの下降(rank進捗)ではないことに注意する。

### `corridorClockProgress_wellFounded` (L145)

**主張:** 残りclock rankによる進捗関係`CorridorClockProgress target`は整礎である(無限下降列が存在しない)。

**証明:** 自然数の`<`の整礎性のaccessibility(到達可能性)を、rank写像`corridorClockRemaining target`に沿って時刻へ引き戻す標準的な議論である。

### `corridorClockProgress_succ` (L161)

**主張:** targetより厳密に手前で一歩進むこと(`time + 1 < target`のもとで`time → time + 1`)は残りclock rankの下降である。

**証明:** `target − (time+1) < target − time`の算術。

### `CanonicalBelowCorridorCertificate.delayedOutcome` (L191)

**主張:** すべての遅延canonical回廊(`downTime + 1 < returnTime`)は、`DelayedCanonicalCorridorOutcome`の二形のいずれかの厳密有限証明書を持つ。

**証明:** 「内部に合法減算可能な時刻が存在するか」で排中律により場合分けする。存在するなら、その時刻を取り、回廊証明書の`internalSubtraction_budgetDrop`(内部の合法減算は初出のtarget未満値を作り履歴予算を厳密に下げる、`PermanentAboveCorridor.lean`)を添えて`internal_subtraction`とする。存在しないなら、定義によりそのまま`AllForcedAdditionCorridor`であり、L30とL51が`all_forced`枝の二つの有限性データを与える。

### `CanonicalReturnRebaseCertificate.corridorOutcome` (L212)

**主張:** 再基底化されたstationary証明書(`PermanentAboveCycleRebase.lean`のcanonical return rebase)は、正確な即時谷(`returnTime = downTime + 1`)であるか、または予算下降/有限clockデータを運ぶ遅延回廊outcomeを露出する。

**証明:** returnが即時かどうかで場合分けする。即時なら左枝。そうでなければ、rebase証明書のdischargeから`exists_belowCorridor`によりcanonical回廊証明書を取り出し、crossingの`start_le`(return時刻はendpoint以後)と即時でないことから`downTime + 1 < returnTime`を得て、L191の`delayedOutcome`を適用する。これが停留kernelから有限回廊解析への型付きの接続である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「all-forced corridor rank(有限化済み)」に対応する。入力は`PermanentAboveCorridor.lean`の`CanonicalBelowCorridorCertificate`とその内部step分類、および`PermanentAboveCycleRebase.lean`のstationary rebase証明書である。出力の`forcedClockSum`とtelescoping式は、`PermanentAboveCorridorWindow.lean`のterminal all-forced crossing windowの加算trace、さらに`PermanentAboveCorridorFiniteClosure.lean`の数値的矛盾導出まで繰り返し使われる。直接の下流は`PermanentAboveCorridorSuffix.lean`で、そこでは本モジュールが有限化した「同一return内の踏破」を、legal endpointの消費cursor(`returnTime − endpointTime`)へ精密化する。本モジュール自身が明記するとおり、ここで閉じたのは固定returnまでの有限踏破であって、外側stationary cycleの脱出は後続のrestart/master rank群(`PermanentAboveCorridorRestartRank.lean`、`PermanentAboveCorridorMasterRank.lean`)の課題である。
