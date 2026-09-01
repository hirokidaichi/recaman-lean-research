# NoDoubleAdditionRun

**役割:** legal subtraction直後に始まるforced additionのrunは長さちょうど2を取れないことを無条件に証明する。

## このモジュールの役割

legal subtraction(合法減算)の直後にforced addition(強制加算)が1回だけ入り、
すぐ次のlegal subtractionで返済されるのが既知のimmediate repayment恒等式である:
時刻 `n+1` で減算、`n+2` で加算すると `a (n+2) = a n + 1` となり、続く時刻 `n+3` の
減算が合法なら着地は `a (n+2) − (n+3) = a (n+1) − 1`、すなわち減算後の値の
ちょうど1下になる。これがcomb run(櫛状区間: 加算と即時返済減算の交互区間)の
low railが1周期に1ずつ下降する仕組みである。本モジュールはその次のケースを
記録する: legal subtractionの後にforced additionが2回続くと、露出する次の減算候補は
減算前の値そのものに戻ってしまう。その値は履歴に既にあるので、3回目の加算が
強制される。ゆえに「減算に挟まれた長さちょうど2の加算run」は存在しない。
これはA枝・B枝のどちらの分岐にも依存しない無条件の恒久資産である。

## 定理と証明

### `double_forcedAddition_candidate_returns` (L25)

**主張:** 時刻 `n+1` の減算が合法で、時刻 `n+2` と `n+3` の減算がともに不能
(2連続forced addition)ならば、次の減算候補は減算前の値に正確に戻る:

`a (n+3) − (n+4) = a n`。

**証明:** 3ステップを順に計算する。減算の合法性から `n+1 < a n` であり、

- `a (n+1) = a n − (n+1)`(合法減算)
- `a (n+2) = a (n+1) + (n+2) = a n + 1`(1回目の強制加算)
- `a (n+3) = a (n+2) + (n+3) = a n + n + 4`(2回目の強制加算)

よって `a (n+3) − (n+4) = a n`。背後にあるのはclockの完全な打ち消し

`−(n+1) + (n+2) + (n+3) − (n+4) = 0`

であり、4連続clockのこの交代和が恒等的に0になるため、候補は出発値へ
戻るしかない。∎

### `double_forcedAddition_extends` (L42)

**主張(長さちょうど2のrunは不可能):** 同じ仮定のもとで、時刻 `n+4` の減算も
不能である。すなわち2連続forced additionは必ず3連続に延長される。

**証明:** 時刻 `n+4` の減算が合法だったと仮定する。合法性の履歴半分により、
候補 `a (n+3) − (n+4)` は `valuesThrough (n+3)` に属さないはずである。しかし
前定理よりこの候補は `a n` に等しく、`a n` は時刻 `n ≤ n+3` に既に出現している
(`mem_valuesThrough_iff`)。矛盾。∎

系として、legal subtractionの直後に始まる極大forced addition runの長さは
1または3以上である。長さ1のrunはimmediate repaymentとしてcomb runを構成し、
長さ2は本定理が禁止し、長さ3以上だけが残る。

## 全体の中での位置づけ

本モジュールは無条件定理であり、`TargetTailResidualKernel` によるA枝/B枝の
二分のどちらにも依存せず、どの分岐の解析でもそのまま使える。10億ステップの
exact probe(`experiments/corridor_structure_probe.cpp`)は極大加算runの長さとして
`1, 3, 4, 5, 6` のみを観測し、長さ2はちょうど0件だった。本定理はこの観測を
計算に頼らず無条件に説明する。

理論側では、comb run(GLOSSARYの「comb run / 櫛状区間」)は長さ1のrunを基本単位と
する圧縮軌道検証の道具である。本定理は「combパターンから外れる最初の逸脱は
一気に3加算以上になる」という形でrun長のスペクトラムを制約し、corridor構造解析
(`EventualHighCorridorStructure` / `EventualHighCorridorSupply`)における
加算runの帳簿付けを単純化する。
