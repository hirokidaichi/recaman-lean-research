# Diagonal

**役割:** 対角状態 `a t = t` を後方解析し、後継値の出現または「より早い初出時刻を持つ blocker」を無条件に取り出す。

## このモジュールの役割

`HistoryFrontier` で負エポックの解析から唯一残った命題が `DiagonalSuccessorProperty`(すべての正の対角状態 `a t = t` について `t+1` が軌道上に出現する)であった。本モジュールは対角状態(時刻と値が一致する状態)へ至る軌道を**後方に**たどる。対角状態の直前の一歩、さらにその前の一歩を復元すると、後継値 `t+1` が既に出現しているか、または対角状態が長い連続減算の末端であることがわかる。後者の場合、その減算鎖を後方に極大まで延長し、鎖の開始点で加算を強制した blocker(妨害値: 減算先が既出であるために合法減算を止める値)を取り出す。この blocker は後継値以上の大きさを持ち、しかも初出時刻が対角時刻より真に早い。この「早期 blocker」が、`PhaseSearch` の負債位相(debt)への厳密なランク下降の材料になる。

## 定理と証明

### `diagonal_last_step` (L8)

**主張:** `a(n+2) = n+2` ならば、直前の一歩は合法減算であり、`a(n+1) = 2(n+2)` である。

**証明:** 直前が加算だったとすると `a(n+1) = a(n+2) − (n+2) = 0` となるが、正の時刻で軌道値は正なので矛盾する。よって直前は減算で、`a(n+1) = a(n+2) + (n+2) = 2(n+2)`。

### `diagonal_successor_occurs_or_longDescent` (L32)

**主張:** `a(n+2) = n+2` ならば、次のいずれかが成り立つ。

1. `∃ u, a u = n+3`(後継値は既に出現している)。
2. 時刻 `n+1` の一歩も合法減算であり、時刻 `n` の座標は `(3, 5)`、ポテンシャルは `−1` である。

**証明:** さらに一歩さかのぼる。時刻 `n+1` の一歩が加算(減算阻止)だったなら、`a n = a(n+1) − (n+1) = 2(n+2) − (n+1) = n+3`。すなわち後継値は時刻 `n` に既に出現している(分岐 1)。減算だったなら `a n = a(n+1) + (n+1) = 3n + 5` で、これは `a n = 3·n + 5` すなわち座標 `(3, 5)` を意味する。座標の条件 `5 < n` は `n ≥ 6` を要するが、`n ≤ 5` の各場合は Lean カーネルの `decide` による具体計算で `a 2 ≠ 2, …, a 7 ≠ 7` が確認され、対角仮定と矛盾するので排除される。ポテンシャルは `potential 3 5 = 5 − 6 = −1`(分岐 2)。

### `diagonal_longDescent_has_maximalTail` (L78)

**主張:** 未解決分岐(最後の二歩がともに減算)では、この二歩は一意に後方へ延長され、極大な連続減算接尾辞になる。すなわち `start + length = n+2`、`length ≥ 2`、`start > 0` なる下降列 `DescentRun start (a start) length` が存在し、`start` への一歩は減算でない。

**証明:** 最後の二歩が減算であることから長さ 2 の下降列(合法減算が連続する区間)を作り、`DescentRun` の後方極大延長補題を適用する。`start = 0` はあり得ない: もしそうなら最初の一歩が時刻 1 の減算になるが、`a 0 = 0` からの減算は不可能である(`decide` で確認)。極大性から、`start` の直前の一歩は減算でない、すなわち強制加算である。

### `diagonal_longDescent_exposes_blocker` (L115)

**主張:** その極大接尾辞の開始点では、加算が既出の候補によって強制されていた。具体的に、`start + length = n+2`、`length ≥ 2` の下降列に対して、値 `y` とその初出時刻 `fy` が存在して

* `a start = (n+2) + descentDrop start length`(下降の総量の等式)、
* `y + 2·start = a start`、
* `n+3 ≤ y`、`FirstAt a y fy`、`y < a start`、`fy < start`

が成り立つ。blocker は単に正であるだけでなく、目標の後継値 `n+3` 以上の大きさを持つ。

**証明:** 下降列の等式から、開始値は終端値 `n+2` に下降総量 `descentDrop start length = length·start + upperTri length` を加えたものである。`start = u+1` と書くと、開始点への一歩は強制加算 `a(u+1) = a u + (u+1)` であり、そのとき阻止された減算候補は `y = a u − (u+1) = a(u+1) − 2(u+1)`、すなわち `y + 2·start = a start`。下界は `length ≥ 2` から `descentDrop ≥ 2·start + upperTri 2 = 2·start + 3` なので `y = (n+2) + descentDrop − 2·start ≥ n+5 ≥ n+3`。特に `y` は正だから、減算が阻止された理由は「候補が既出」以外にない。よって `y ∈ valuesThrough u` であり、履歴の元は初出時刻を持つので `fy ≤ u < start` なる `FirstAt a y fy` が得られる。`y < a start` は `y + 2·start = a start`、`start > 0` から従う。

### `diagonal_longDescent_gives_coverageStep` (L175)

**主張:** 未解決の長下降分岐は、そのままで目標 `n+3` に対する具体的な `CoverageStep`(極大接尾辞の開始値を親とする)を与える。

**証明:** 前定理の blocker `y` は `n+3 ≤ y < a start` を満たし初出時刻を持つので、CoverageStep の blocker 分岐そのものである。

### `diagonal_successor_occurs_or_coverageStep` (L187)

**主張:** すべての正の対角終端は無条件の局所解決を持つ: 後継値が既に出現しているか、極大減算接尾辞がその開始値における証明付き CoverageStep を露出する。

**証明:** `diagonal_successor_occurs_or_longDescent` の二分岐に、未解決側では前定理を適用する。

### `diagonal_successor_occurs_or_earlierBlocker` (L201)

**主張:** 同じ二分法の座標なし形。後継値が出現しないなら、`n+3 ≤ y` なる値 `y` とその初出時刻 `fy < n+2` が存在する。すなわち blocker の初出は対角終端より真に早い。

**証明:** 未解決分岐で `diagonal_longDescent_exposes_blocker` を適用し、`fy < start ≤ n+2` から `fy < n+2` を得る。この形は、時刻と値を混合した将来の探索(位相探索の debt 進入)がそのまま消費できる。

### `LongDiagonalDescentResolvable` (L216)

**定義:** 「二歩前の状態が `q = 3, G = −1` の面上にある対角終端に限って後継値の出現を示せばよい」という縮約された命題。`∀ n, a(n+2) = n+2 → CoordinatesAt n 3 5 → ∃ u, a u = n+3`。

### `longDiagonalDescentResolvable_implies_diagonalSuccessor` (L220)

**主張:** `LongDiagonalDescentResolvable` から `DiagonalSuccessorProperty` 全体が従う。

**証明:** 対角時刻 `t` について場合分けする。`t = 1` なら `a 1 = 1` の後継 `2` は `a 4 = 2` として出現する(`decide`)。`t ≥ 2` なら `t = n+2` と書け、`diagonal_successor_occurs_or_longDescent` により後継が出現するか、前状態が `(3, 5)` 座標を持つ。後者は仮定した縮約命題がちょうど処理する形である。

## 全体の中での位置づけ

証明地図の「対角負債分岐」から「極大後方鎖・早期blocker」への段階であり、状況一覧の「対角後方履歴」行(証明済み)に対応する。`HistoryFrontier` が分離した `DiagonalSuccessorProperty` を入力とせず、逆にその性質を「後継出現 or 早期 blocker」という無条件の二分法(`diagonal_successor_occurs_or_earlierBlocker`)に置き換えるのが本モジュールの成果である。この二分法は `PhaseSearch.diagonal_successor_or_entersPhaseDebt` が直接消費し、blocker の早い初出時刻 `fy` を負債位相の局所座標として保存することで、対角例外を四成分位相ランクの厳密下降(debt 進入)へ変換する。また `DebtBackward` 以降の負債局所解析は、ここで得た「初出時刻の真の下降」を反復する。
