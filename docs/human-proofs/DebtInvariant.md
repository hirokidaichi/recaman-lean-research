# DebtInvariant

**役割:** debt(負債)ノードが満たすべき強い意味的不変量を定義し、初出値の最終遷移の分類とともに、debt状態の基本的な進行補題を証明する。

## このモジュールの役割

位相探索(`PhaseSearch.lean`)では、探索ノードは「通常(normal)」と「負債(debt)」の二つの位相を持つ。debtとは、対角分岐などで見つかった「過去に初出した値」を処理するモード、すなわち通常探索へ戻る前に解消すべき局所的な証明義務の比喩である。本モジュールは、debtノードが単なる数値の組ではなく実軌道の証拠を伴うことを保証する不変量 `DebtInvariant` を定義する。あわせて、初出(FirstAt: ある値が時刻`t`で初めて出現すること)の最終遷移が「初期値・合法減算・強制加算」の三通りに完全分類されることを示し、それを用いてdebtノードの一歩の解析(先行値の取り出し、通常位相への復帰、debt継続)を与える。四成分ランク `(履歴予算, anchor, 位相, 局所量)` のどの成分が下降するかを、各補題が明示する構成になっている。

## 主要な定義

### `DebtInvariant` (L10)

目標`target`と探索ノード`node = ⟨horizon, anchorParent, phase, localMeasure⟩`、値`value`、初出時刻`firstTime`に対する命題で、次を同時に要求する。

- `node.phase = debt` かつ `node.localMeasure = firstTime`(局所量は初出時刻)
- `target ≤ value`(値は目標以上)
- `FirstAt a value firstTime`(`value`は時刻`firstTime`に初出する)
- `firstTime < node.horizon`(初出は履歴horizon: 履歴予算を評価する固定時刻、より前)
- `value < node.anchorParent`(値は固定されたanchor親: 探索の基準となる親の値、より真に小さい)

最後の狭義不等式が本質的である。後の補題が示すように、この不等式があるからこそ、debtから通常位相へ戻るときに`value`自身を新しいanchorとして採用でき、四成分ランクのanchor成分が真に下降する。

## 定理と証明

### `firstAt_time_zero_value` (L20)

**主張:** 時刻0で初出する値は0に限る。

**証明:** 定義より `a 0 = 0` なので、`FirstAt a value 0` の第一成分 `a 0 = value` から直ちに従う。

### `firstAt_succ_transition` (L26)

**主張:** `value`が時刻`n+1`で初出するならば、その最終遷移は実際のレカマン遷移そのものである。すなわち、減算可能(`CanSubtract`)なら `value = a(n) − (n+1)`、不可能なら `value = a(n) + (n+1)` である。

**証明:** 減算可能性は決定可能なので場合分けする。各場合で、レカマン数列の一歩の定義(`a_succ_of_canSubtract` / `a_succ_of_not_canSubtract`)と `a(n+1) = value` を突き合わせるだけである。

### `not_canSubtract_cases` (L41)

**主張:** 時刻`n+1`で減算が不可能な理由は、定義に現れる二つに限る: 候補が非正(`a(n) ≤ n+1`)であるか、候補 `a(n) − (n+1)` がすでに履歴 `valuesThrough n` に含まれている。

**証明:** `n+1 < a(n)` かどうかで場合分けする。正でなければ前者。正なら、候補が未出だと仮定すると `CanSubtract` の両条件が揃って矛盾するので、候補は既出である。

### `firstAt_final_transition` (L56)

**主張:** 初出の最終遷移の完全な三分類。`firstTime = 0` かつ `value = 0`、あるいは合法減算(`value = a(n) − (n+1)`)、あるいは強制加算(`value = a(n) + (n+1)`)であり、強制加算の枝では減算が失敗した理由(非正または既出)も記録される。

**証明:** `firstTime`が0か後続かで分け、後続の場合は`firstAt_succ_transition`と`not_canSubtract_cases`を合成する。

### `firstAt_succ_not_mem_history` (L78)

**主張:** 時刻`n+1`で初出する値は、履歴 `valuesThrough n` に含まれない。

**証明:** 含まれるとすると、ある時刻 `t ≤ n < n+1` で `a(t) = value` となり、初出性(それ以前に出現しない)に反する。

### `debt_firstTime_pos` (L86)

**主張:** 目標が正のとき、有効なdebtノードの初出時刻は正である。

**証明:** `firstTime = 0` なら `value = 0`(`firstAt_time_zero_value`)だが、不変量の `target ≤ value` と `0 < target` に矛盾する。

### `debtInvariant_exitNormal_at_value` (L103)

**主張:** 強いdebt不変量を満たすノードは、いつでも自分の初出値`value`をanchorとする通常ノード `⟨horizon, value, normal, value⟩` へ復帰でき、これは`PhaseSearchProgress`(四成分ランクの真の下降)である。さらに `target ≤ value` と初出証明も引き継がれる。

**証明:** 不変量の `value < anchorParent` がそのままanchor成分の狭義下降を与える(`phaseSearch_exitDebt_of_anchorDrop`)。位相成分はdebt→normalで増えるが、辞書式順序で先に比較されるanchorが下がるため問題にならない。この定理が意味するのは、局所的なdebtの全域性は難所ではなく、真の困難は「先行する通常ノードからランクを下げてこの強い不変量を構成すること」にある、ということである。

### `debt_legalSubtraction_earlierPredecessor` (L118)

**主張:** debtノードの値が時刻`n+1`の合法減算で生じたなら、直前値 `a(n)` はより早い初出時刻`predecessorTime < n+1`を持ち、`value < a(n)` であり、debt局所時刻を`n+1`から`predecessorTime`へ下げる`PhaseSearchProgress`が成り立つ。

**証明:** 合法減算より `value = a(n) − (n+1)` かつ `n+1 < a(n)`、したがって `value < a(n)`。直前値 `a(n)` は履歴 `valuesThrough n` の元なので、履歴の任意の元が初出時刻を持つこと(`history_member_has_firstAt`)から `predecessorTime ≤ n < n+1` を得る。ランク下降はdebt局所成分(初出時刻)の下降である。注意すべきは、先行値は`value`より大きいため、固定anchorの下に留まる保証はないことである。

### `debt_legalSubtraction_preservesInvariant` (L143)

**主張:** 合法減算の先行値 `a(n)` は、追加で `a(n) < anchor` が分かっているとき、そしてそのときに限り、再び有効なdebtノードになる。このときdebt時刻下降の`PhaseSearchProgress`も成り立つ。

**証明:** 不変量の各条項を確認する。`target ≤ value < a(n)` より目標下界は保たれ、初出時刻は `predecessorTime < n+1 < horizon` で推移的にhorizonより前、anchor下界は仮定そのものである。ランク下降は前補題と同じdebt時刻下降である。

### `debt_forcedAddition_predecessor` (L179)

**主張:** debtノードの値が時刻`n+1`の強制加算で生じたなら、直前値 `a(n)` はより早い初出時刻を持ち、しかも `a(n) < anchor` が(仮定なしに)成り立つ。残る算術的分岐は `a(n) < target` か `target ≤ a(n)` かだけである。

**証明:** 強制加算より `value = a(n) + (n+1)`、ゆえに `a(n) < value < anchorParent` となり、合法減算の場合と違ってanchor下界が自動的に従う。先行値の初出時刻は履歴所属から取る。目標との比較は自然数の全順序による二分である。

### `debt_forcedAddition_exitProgress` (L202)

**主張:** 強制加算の先行値が `target ≤ a(n)` を満たすなら、`a(n)` を新anchorとする通常ノードへの復帰が`PhaseSearchProgress`になる。

**証明:** 前定理で示した `a(n) < anchor` がanchor成分の狭義下降を与える(`phaseSearch_exitDebt_of_anchorDrop`)。目標下界と初出証明は仮定から引き継ぐ。

### `diagonal_successor_or_validDebt` (L223)

**主張:** 対角状態 `a(n+2) = n+2` からは、次の値`n+3`が軌道に出現するか、さもなければ強い`DebtInvariant`を満たすdebtノードへ、`PhaseSearchProgress`(位相成分の下降)を伴って進入できる。

**証明:** `Diagonal.lean`の結果を用いる。対角状態からは、`n+3`の出現か、極大な後方減算鎖が得られる(`diagonal_successor_occurs_or_longDescent`)。後者では鎖の解析(`diagonal_longDescent_exposes_blocker`)により、鎖の開始値 `a(start)` より小さく目標 `n+3` 以上の妨害値(blocker: 減算を阻む既出値)`y`と、その初出時刻 `fy < n+2` が取り出せる。anchorを鎖の開始値 `a(start)` に選ぶと、`DebtInvariant`の全条項(目標下界 `n+3 ≤ y`、初出、`fy < n+2 = horizon`、`y < a(start)`)が揃う。ランク下降はnormal→debtの位相下降(`phaseSearch_enterDebt`)である。

## 全体の中での位置づけ

証明地図の「対角負債分岐」から「負債・crossing閉包」に至る負債局所解析層の起点である。ここで定義した`DebtInvariant`は、一歩分類を行う`DebtStep`、crossing(目標をまたぐ強制加算)を解析する`DebtCrossing`、後方鎖を解析する`DebtBackward`(いずれも本モジュールを直接import)のほか、`NormalPhase`経由で位相統合層全体、さらに`HistoricalDebtBridge`や`ReadyDebtInvariant`(horizon-ready debt)の基礎として使われる。`debtInvariant_exitNormal_at_value`が示す「局所的な出口は常にある」という事実は、未解決点を「強い不変量をランク下降付きで構成する側」へ移す、この層全体の設計方針を要約している。
