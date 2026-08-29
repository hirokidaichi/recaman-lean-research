# LandingFloorThirtytwo

**役割:** landing固定点側へ輸送されたhistory cursorを使って再訪排除を発火させ、頂点定理の固定点枝の時計床を無条件に`32 ≤ crossingTime`へ引き上げる。

## このモジュールの役割

固定点解析には二つの分岐がある。discharge replay側と landing側である。replay側は自前の
kernel掃過で早くから`112 ≤ crossingTime`の床を持っていたが、landing側の床は長らく
`18 ≤ crossingTime ∨ target = 19`という、例外つきの弱い形にとどまっていた。第七十三ラウンドの
道具移植で判明した欠落は**downcross前置界ただ一つ**であった。すなわち「targetを超える軌道値が
landing時刻より前に存在する」という情報を、landing分岐が持っていなかった。

第七十九〜第八十二ラウンドで、その情報を`TerminalHistoryCursor`という source-free な型として
history辺の定義に組み込み、生成点からlanding時刻まで通した。本モジュールはその輸送の**受け取り側**であり、
到着したcursorから再訪排除を発火させて床を上げる。結果として頂点定理の固定点枝は
**例外なしの`32 ≤ crossingTime`かつ`19 ≤ target`**になる。

なお本モジュールが上げるのは**固定点枝の中身**であって、頂点定理の二択そのものではない。
semantic枝が`0 < target`だけから出る空の枝である事実(`SemanticOracleRecursion.lean`)は
本モジュールでは何も変わっていない。床の価値は枝の内容にある。

## 定理と証明

用語:「cursor」はtargetを超える軌道値の存在時刻を指す記録、「record排除」は
「crossing時刻の値が過去の最大値を更新していない」ことを示す論法、「再訪排除」は
「既出値がtailの遅い時刻で再び現れることはない」という論法である。

### `TerminalHistoryCursor.aboveTarget_before` (L29)

**主張:** cursorからは直ちに「`bound`より前のある時刻で軌道値がtargetを超える」が読み出せる。

**証明:** cursorの構造体から`cursorTime`と、その二つのフィールド`hlt : cursorTime < bound`、
`habove : target < a cursorTime`を取り出すだけである。補助補題だが、これが
record排除(L72)への入力になる。

### `TerminalHistoryCursor.thirtytwo_le_bound` (L38)

**主張:** target床19が使えるとき、cursorのbound は32以上である: `19 ≤ target → 32 ≤ bound`。

**証明:** `32 ≤ bound`でないと仮定して矛盾を導く。cursorは
`cursorTime`(target超の時刻)、`minimumTime`(ピン留めされたtail最小値の時刻)、`tailStart`、
および「tail開始以降の低い軌道値がすべて`minimumTime`の値より上にある」という下界条件`hlow`を持つ。

`prefixCursor_successor_witness`は、target床19と`target < a cursorTime`、そして
`cursorTime`がkernelのprefix内(`bound < 32`から従う)にあることから、**後続値のwitness**を供給する:
ある`witness`があって、その値が`a minimumTime`と一致し、しかも時刻としても値としても
kernel prefixの内側にある。ここで`a 131 = 4`をkernelで計算し(`decide`)、
cursorの下界条件`hlow`を時刻131に適用すると、`witness`の位置と値が
`minimumTime`より厳密に前・厳密に下であることが確定する。

すると`a minimumTime = a witness`は、既出値が後の時刻`minimumTime`で再び現れたことを意味する。
これは`value_no_late_recurrence`(遅い再訪の禁止)に真っ向から反する。よって矛盾。

**気持ち:** ここが本モジュールの実質である。「cursorが浅い位置にある」と仮定すると、
そのcursorが指すtarget超の値の**後続値**がkernel prefixの中に witness を持ってしまう。
そしてcursor自身が抱えているtail最小値のピン留めが、その witness を「後から再訪された既出値」に
変えてしまう。再訪排除は既に無条件で成立している(第七十三ラウンドで landing側へ無条件移植済み)ので、
必要だったのは**発火のための入力**だけだった。それが cursor である。

kernel計算`a 131 = 4`はcutoff 131の実測上限に対応する。landing側のcoverage cutoffは
実測131が上限であり(`a 32 = 46`の後継47の初出が時刻222)、32を超えるには先にtarget床を
48以上へ上げてcutoff 222を解禁する必要がある。床上げがreplay側と同じ階段構造を持つ理由である。

### `landing_thirtytwo_le_crossingTime` (L59)

**主張:** landing固定点の時計は32以上: 固定点core・targetの未出・landingからcrossingへの
first weak upcrossing step・landing cursorがあれば`32 ≤ crossingTime`。

**証明:** coreの`nineteen_le_target`がtargetの未出から`19 ≤ target`を出す。これをL38に食わせると
`32 ≤ landingTime`。upcrossing stepの`start_le`が`landingTime ≤ crossingTime`を与えるので
`32 ≤ crossingTime`。

**従来との差:** 同じcoreに対する共有カーネルの床は`18 ≤ crossingTime ∨ target = 19`にすぎない。
本定理は**例外枝`target = 19`を持たない**。これがcursor輸送の見返りである。

### `landing_crossingTime_not_record` (L72)

**主張:** landing固定点に対するrecord排除が無条件になる:
`∃ time < crossingTime, a crossingTime < a time`。すなわちcrossing時刻の値は過去の最大値を更新しない。

**証明:** L29でcursorからtarget超の時刻を一つ取り出し、`start_le`で
その時刻が`crossingTime`より前であることを確認して、coreの
`crossingTime_not_record_of_prefixAbove`に渡す。

**気持ち:** record排除は第七十三ラウンドで「共有核レベルの汎用形として無条件に成立」していたが、
landing分岐で発火させるには`predecessorFirstTime < landingTime`型の情報が必要だった。
cursorはまさにその情報の source-free 版である。

### `PermanentTailUnifiedOutcome.semantic_or_thirtytwo` (L86)

**主張:** 統合outcomeの**両方の**固定点枝が床32を持つ:
「semantic進行辺 ∨ (`32 ≤ crossingTime` かつ `19 ≤ target` な固定点core)」。

**証明:** 統合outcomeの三枝を場合分けする。`semantic_progress`はそのまま左へ。
`discharge_replay`は自前のkernel掃過による`onehundredtwelve_le_crossingTime`(112以上)を持つので
32はそこから直ちに従う。`landing_cycle`はL59を適用する。いずれの固定点枝でも
`19 ≤ target`はcoreの`nineteen_le_target`から出る。

**気持ち:** これまでこの統合outcomeは`semantic_or_thirtytwo_or_landingGap`という**三択**で、
第三枝がlanding gap(`crossingTime < predecessorFirstTime`かつ`target < a predecessorFirstTime`)という
未攻略の穴だった。cursorの輸送によりその穴が塞がり、二択へ戻った。

### `LeastMissingTarget.semantic_or_thirtytwo` (L114)

**主張:** 頂点定理。最小未出targetは外側の再帰に「semantic位相の子」か
「時計32以上・target 19以上の固定点core」を渡す。

**証明:** 最小未出targetからmissing permanent tail、combined証明書を取り、
その`unifiedOutcome`にL86を当てる。

**留保:** この二択そのものは、`SemanticOracleRecursion.lean`の
`semantic_or_flooredCore_of_pos`と同様に**`0 < target`だけから導出できる**。
第一disjunctが空だからである。本定理の価値は第二disjunctの内容が強くなった点にあり、
「頂点定理が新たに何かを証明した」わけではない。この区別は隠してはならない。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「landing固定点の床上げ」段の到達点である。上流は
`RefinedLandingOutcome.lean`(統合outcomeとlanding cursorを含むlanding cycle枝)で、
その手前に`TerminalHistoryCursor`を生成・輸送する6段
(`PermanentAboveCorridorInstalledStep`から`PermanentAboveCorridorHistoryLanding`まで)がある。
輸送が当初想定の「コンストラクタへ2フィールド追加」ではなく
`TerminalChronologyHistoryProgress`の定義強化(`TerminalHistoryBudgetDrop`と
`TerminalHistoryCursor target (parentTime + 1)`の連言)として実現されたおかげで、
型が`(target childTime parentTime)`だけで添字付けされ、`source`依存が生成点に閉じ、
下流6段をNat持ち上げなしに通せた。副次的にhistory枝自身の情報量も回復している。

第八十六ラウンドの敵対的再検査により、本モジュールの結果が**空虚に真ではない**ことが確認されている。
`TailFixedPointCore`を伴う右枝は実際に居住する(target 50・clock 32で
`a 32 = 46 < 50 ≤ 79 = a 33`が強制加算のstraddleをなし、`node_reproduction`も
`⟨0, 46, .normal, 46⟩`で成立する。5フィールドすべて`decide`で検証済み)。
`landing_cursor`の空虚性も否定された。L38の床導出では、cursorの第5条項
「`a witness ≤ target` なる witness はすべて `tailStart` より前」が`hlow 131`から
`131 < tailStart`を出す一点で実際に効いており、自由に得られる情報ではない。

下流は頂点そのものである。第八十二ラウンド以降、大域残余は
`0 < target ∧ TargetTailReturnHypothesis target ⟹ ∃ t, a t = target`の一本に縮約されているが、
`targetTailReturn_iff_occurs`によりこの仮定は出現と同値であり、**難しさは減っていない。
減ったのは足場の量である**(`CrossingReadinessClosure.lean`を参照)。
本モジュールの床32も、`PinnedConfigurationAttack.lean`が示すとおり、
kernel列挙による床上げが無限トレッドミルである以上、それ単独で予想へ到達する道具ではない。
