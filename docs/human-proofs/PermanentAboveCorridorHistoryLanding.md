# PermanentAboveCorridorHistoryLanding

**役割:** history辺の抽象的なmissing-count下降不等式から、その背後に必ずあるbelow-target値のfresh landing(parent cursorより後・child cursor以前の初出)を逆算し、そこからのcanonical restart crossingを同梱したanchored interfaceへ三形分類を強化する。

## このモジュールの役割

`PermanentAboveCorridorReplayInterface.lean`の三形interfaceのうち、history枝は`missingBelowCount target childTime < missingBelowCount target parentTime`という不等式だけを運んでいた。これは停止性の証明には十分だが、外側の再帰を実際に継続するには「どこで何が起きたのか」という具体的な素材が要る。本モジュールの観察は、strictなmissing-budget下降は抽象的な大小関係ではなく、常に明示的なwitnessを伴うということである: child cursorまでに出現しているがparent cursorまでには出現していないtarget未満の値が必ず存在し、その初出時刻は二つのcursorの間の窓に厳密に入る。重要なのは、この逆算が下降不等式*単独*から可能なことである。従って、history progressを生成している上流の定理群(chronology rank、blocker position、iteration closureなど)を一つも書き換えることなく、事後的にwitnessを回収できる。さらにlandingの値はtarget未満なので、canonical upcrossing機構(最初のweak upcrossingの存在定理)がそこから再起動でき、interfaceは「fresh landing + そのrestart crossing」という、外側再帰がhistory辺を越えて継続するのにちょうど必要なデータを持つanchored形へ強化される。

## 定理と証明

### `exists_new_below_of_missingDrop` (L24)

**主張:** strictなmissing-count下降は、child cursorには見えているがparent cursorには見えていないbelow-target値を露出する: `missingBelowCount m childTime < missingBelowCount m parentTime`なら、`v < m`かつ`v ∉ valuesThrough parentTime`かつ`v ∈ valuesThrough childTime`なる`v`が存在する。

**証明:** 境界`m`についての帰納法。`m = 0`ではカウントが両辺0なので下降は不可能。`m + 1`の場合、最上位の値`m`が二つの履歴に属するかで4通りに分ける。

- `m`がchild履歴にあり、parent履歴にない場合: `m`自身がwitnessである。
- 残る3通り(両方にある、両方にない、childになくparentにある)では、`missingBelowCount`の一段展開`missingBelowCount_succ`により最上位項の寄与を比べると、下位部分`m`未満のカウントにもstrictな下降が残ることが算術的に従う(childになくparentにある場合は最上位項がむしろ逆向きに働くが、その場合も下位のstrict下降は保たれる)。帰納法の仮定でwitness `v < m`を取り、`v < m + 1`として返す。

この定理は不等式以外の何も仮定しない、純粋に組合せ的な補題である。

### `TerminalChronologyHistoryProgress.exists_freshLanding` (L58)

**主張:** すべてのterminal history辺はfresh landingを運ぶ: `value < target`、`parentTime < landingTime ≤ childTime`、`FirstAt a value landingTime`を満たす`value`と`landingTime`が存在する。

**証明:** L24でwitness値`v`を取る。`v`はchild履歴の元なので、履歴の元は必ず初出時刻を持つという事実(`history_member_has_firstAt`)から、初出時刻`u ≤ childTime`と`FirstAt a v u`を得る。もし`u ≤ parentTime`なら`v`はparent履歴にも属することになり、L24の非所属に矛盾する。よって`parentTime < u`であり、初出は二つのcursorの間の窓に厳密に入る。

### `PermanentTailTerminalAnchoredOutcome` (L74)

anchored interface。三constructorを持つ帰納型である。

- `fresh_landing`: 元のhistory progressに加えて、landing値・landing時刻・restart crossing時刻、値のbelow-target性、`parentTime < landingTime ≤ childTime`という窓条件、landingの`FirstAt`、そしてlanding時刻からの`FirstWeakUpcrossingStep`(canonical restart crossing)。
- `semantic_progress`: 従来どおりの比較元付きsemantic位相辺。
- `exact_replay`: 従来どおりのreplay固定点(descendantのdischarge証明書とreplay証明書)。

history辺だけが強化され、他の二枝は情報を失わない。

### `PermanentTailCombinedCertificate.terminalAnchoredOutcome` (L103)

**主張:** missing-target interfaceはanchorする: すべての枝が、semantic child、replay固定点、または具体的なfresh landingとそのrestart crossingのいずれかを外側再帰へ渡す。

**証明:** combined証明書の`terminalMissingOutcome`(前モジュールの三形)を場合分けする。semantic枝とreplay枝はそのまま移送する。history枝ではL58でlanding `(value, landingTime)`を取り、`FirstAt`の値等式から`a(landingTime) = value < target`。targetの正値性とあわせて`exists_firstWeakUpcrossingStep_from_below`(`PermanentAboveCanonical.lean`)を適用し、landing時刻からの最初のweak upcrossing `nextCrossingTime`を得る。全成分を`fresh_landing`へ詰めて終了する。

landingはbelow-targetの実軌道点なので、これはまさにcanonical corridor機構(fresh below点 → 最初のupcrossing → crossing node)の再起動条件であり、history辺の先で解析を継続するための入口が型として確保されたことになる。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「history landing anchor(history枝をfresh landing＋restart crossingへ強化済み)」に対応する。上流は`PermanentAboveCorridorReplayInterface.lean`(三形interface)と`PermanentAboveCanonical.lean`(最初のweak upcrossingの存在)である。下流では、直後の`PermanentAboveCorridorLandingHorizon.lean`が、missing-target反例ではtarget未満の全値がtail開始までに出現済みであることを使ってlanding時刻をtail開始前へ束縛し、restart crossingが`crossing + 1 ≤ start < parent.horizon`という履歴内境界を満たすこと、すなわちinstalled crossing node `⟨parent.horizon, a(c), normal, a(c)⟩`の形状に必要な条件を上流の書き換えなしで獲得できることを示す。全体としては、三形interfaceのhistory枝が「予算が減った」という会計情報から「次にどのcrossing nodeで再開するか」という探索情報へ具体化され、terminal解析の三つの攻略線(landing再開・replay数値挟撃・semantic位相ランク)がいずれも構成的な素材を持つ段階に達した。
