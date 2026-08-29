# PhaseSearch

**役割:** normal/debt の位相を持つ四成分探索ランクを定義し、その整礎性と debt 出入りのランク規則、および抽象オラクルからの目標到達を証明する。

## このモジュールの役割

`Diagonal` の解析は、対角状態から「後継値の出現」または「初出時刻が真に早い blocker」を取り出した。しかし三成分の履歴探索ランク(予算・親・軌道値)には「過去の初出時刻をたどる」動きを厳密下降として登録する場所がない。本モジュールは探索状態に**位相(phase)**という第 3 成分を追加する。位相は `normal`(通常の値・履歴探索)と `debt`(負債: 対角分岐で得た早期 blocker を処理し、初出時刻の下降を追うモード)の二値で、debt の方が小さいランクを持つ。これにより「debt への進入」「debt 中の初出時刻下降」「アンカー親が下がったあとの normal への復帰」がすべて四成分辞書式ランクの厳密下降になる。モジュール末尾では、このランクに対する抽象オラクル(各ノードで目標出現か真に小さい子を返す証明義務)から目標の出現が従うことを整礎帰納法で示す。

## 主要な定義

### `SearchPhase` (L7)

探索位相の二値帰納型。`debt` と `normal` の 2 つのコンストラクタを持つ。数値順序は「debt に入ることが厳密なランク減少になる」ように選ばれている。

### `SearchPhase.rank` (L12)

位相の数値化: `debt ↦ 0`、`normal ↦ 1`。

### `PhaseSearchNode` (L19)

四成分の探索状態。`horizon`(参照可能な実軌道履歴の範囲)、`anchorParent`(アンカー親: 局所探索中に基準として固定する親の値)、`phase`(位相)、`localMeasure`(局所量: normal では軌道値、debt では下降していく初出時刻)。debt 中も horizon は固定されたままであることが重要で、初出時刻を horizon と混同すると履歴予算成分が壊れる。

### `phaseSearchRank` (L28)

四成分ランク `(missingBelowCount m horizon, (anchorParent, (phase.rank, localMeasure)))`。優先度は履歴予算 > アンカー親 > 位相 > 局所量の順である。

### `PhaseSearchProgress` (L33)

`phaseSearchRank` に関する右入れ子の四成分辞書式順序での真の減少。

### `PhaseSearchOracle` (L118)

抽象的な完成義務: 任意の `PhaseSearchNode` について、目標 `m` が実軌道上に出現するか、四成分ランクで真に小さい子ノードが存在する、という命題。

## 定理と証明

### `natQuadLex_wellFounded` (L39)

**主張:** 右入れ子の四成分辞書式順序は整礎である。

**証明:** 第一成分の `<` の整礎性と、`HistoryBudget` で示した三成分順序の整礎性 `natTripleLex_wellFounded` を `Prod.lexAccessible` で合成する。

### `phaseSearchProgress_wellFounded` (L50)

**主張:** `PhaseSearchProgress m` は整礎である。

**証明:** ランク写像 `phaseSearchRank` に沿った四成分順序の引き戻し。ランク値の到達可能性(Acc)に関する帰納法でノード自身の到達可能性を示す、`HistoryBudget` と同型の標準的議論である。

### `phaseSearch_enterDebt` (L68)

**主張:** horizon とアンカー親を固定したまま normal から debt へ移ることは、新しく露出した初出時刻(debt の局所量)が何であっても、ランクの厳密下降である。

**証明:** 上位二成分は不変で、位相成分が `1` から `0` へ厳密に下がる。辞書式順序では位相成分の下降が局所量の任意の変化を覆い隠す。ここが位相導入の要点であり、blocker の初出時刻に値の上界を課す必要がなくなる。

### `phaseSearch_debtTimeDrop` (L80)

**主張:** debt が続く間、より早い初出時刻へ移ることは horizon を変えずにランクを厳密に下げる。

**証明:** 上位三成分が不変で、第四成分(初出時刻)が厳密に下がる辞書式の右分岐。

### `phaseSearch_exitDebt_of_anchorDrop` (L91)

**主張:** アンカー親が厳密に下がってさえいれば、debt から normal へ復帰できる。位相成分の増加(0 → 1)はアンカー下降の背後に隠れる。

**証明:** 辞書式順序で第二成分(アンカー親)の厳密下降は、それより下位の位相・局所量の任意の変化に優先する。したがって debt の解消と normal への復帰が一つのランク下降として登録される。

### `diagonal_successor_or_entersPhaseDebt` (L102)

**主張:** `a(n+2) = n+2` なる対角状態からは、後継値 `n+3` が出現するか、または `n+3 ≤ y`、初出時刻 `fy < n+2` なる blocker `y` が存在して、horizon `n+2`・任意のアンカーのもとで normal ノードから debt ノード `⟨n+2, anchor, debt, fy⟩` への `PhaseSearchProgress` が成り立つ。

**証明:** `Diagonal` の無条件二分法 `diagonal_successor_occurs_or_earlierBlocker` の blocker 分岐に `phaseSearch_enterDebt` を適用するだけである。blocker の値 `y` に上界がないことは問題にならない: ランクを下げるのは位相成分だからである。極大後方鎖の定理はこうして「値の下降を証明できない」という以前の障害を回避して整礎探索に組み込まれる。

### `phaseSearchOracle_reaches_from` (L125)

**主張:** 全域の `PhaseSearchOracle m` があれば、任意の開始ノードから `∃ t, a t = m` が従う。

**証明:** `phaseSearchProgress_wellFounded` による整礎帰納法。オラクルが出現を返せば終了、真に小さい子を返せば帰納法の仮定を子へ適用する。

### `phaseSearchOracle_implies_occurs` (L135)

**主張:** 全域の位相探索オラクル一つから目標の出現が従う。

**証明:** ノード `⟨0, 0, normal, 0⟩` を開始点として前定理を適用する。

## 全体の中での位置づけ

証明地図の「四成分位相ランク」段階(状況一覧「位相探索」行、骨格証明済み)である。三成分ランク(`HistoryBudget`)を内側順序として再利用し、`Diagonal` の早期 blocker をランク下降へ変換する受け皿を提供する。この上に、`PhaseProgress`(推移性)、`PhaseEpoch`(負エポックの位相ランク接続)、`PhaseSearchStart`(canonical な開始ノードと制限オラクル)、`PhaseSemantic`(proof-carrying な意味的 domain)が積み上がる。また `DebtInvariant` 以降の負債局所解析と `Crossing*` 系はすべて、ここで定めた `enterDebt` / `debtTimeDrop` / `exitDebt_of_anchorDrop` の三規則に従ってランクを下げる。`PhaseSearchOracle` 自体は数値 tuple 全体にわたる強すぎる義務であることが後に判明し、`PhaseSearchStart` の制限オラクル、さらに `PhaseSemantic` の意味的 domain へと精密化されていく。
