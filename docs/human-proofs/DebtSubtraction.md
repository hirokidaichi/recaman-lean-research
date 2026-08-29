# DebtSubtraction

**役割:** 合法減算で生まれた初出値の一歩後方を解析し、先行値の回収・CoverageStep・debt時刻下降を、debt不変量を仮定せずに与える。

## このモジュールの役割

debtモードで扱う値は「時刻`fy`に初出した値`y`」である。本モジュールは、その初出が合法減算で作られた場合に、一歩だけ後ろを見ることで何が回収できるかを、`DebtInvariant`の仮定なしの汎用形で証明する。得られるのは、初出時刻がより早く値がより大きい先行値`x`であり、これは(1)値に関する強帰納法の一段である`CoverageStep`、(2)debtの局所時刻を下げる`PhaseSearchProgress`、の双方に直ちに変換できる。仮定が軽いため、debt解析(`DebtBackward`)以外の文脈からも再利用できる基礎部品である。

## 定理と証明

### `legalSubtraction_firstAt_predecessor` (L10)

**主張:** `y`が正の時刻`fy`に初出し、その最終遷移が合法減算(`CanSubtract fy (stateAt (fy−1))`)であるとする。このとき先行値 `x = a(fy−1)` について、

- `x`はある時刻`fx < fy`に初出する、
- `y + fy = x`(すなわち `y = x − fy`)、
- `y`は時刻`fy−1`までの履歴に未出、
- `y < x`

がすべて成り立つ。

**証明:** 合法減算の定義から `a(fy) = a(fy−1) − fy` かつ `fy < a(fy−1)` なので、`y = x − fy` と `y < x`、和の等式 `y + fy = x` が従う。`y`の未出性は`CanSubtract`の第二条件(減算先が履歴に無いこと)そのものである。先行値`x`は時刻`fy−1`までの履歴の元なので、履歴の各元が初出時刻を持つこと(`history_member_has_firstAt`)から `fx ≤ fy−1 < fy` を得る。要点は、初出時刻は真に早くなる一方で値は真に大きくなる、という時刻と値の逆向きのトレードオフである。

### `legalSubtraction_firstAt_gives_coverageStep` (L45)

**主張:** さらに目標が `m ≤ y` を満たすなら、先行値を親とする `CoverageStep m (a(fy−1)) (fy−1)` が成り立つ。ここで`CoverageStep m v f`とは「目標`m`が出現する、または `m ≤ y' < v` を満たす初出値`y'`が存在する」という、値に関する強帰納法の一段である。

**証明:** `Mechanisms`の一般補題 `subtraction_gives_coverageStep` に、着地値 `a(fy) = y ≥ m` を渡すだけである。着地値`y`自身が、親値 `x = a(fy−1)` より真に小さい目標以上の初出値として第二枝の証人になる。

### `legalSubtraction_firstAt_gives_debtProgress` (L63)

**主張:** 同じ状況で、任意のhorizonとanchorに対し、先行値`x`と初出時刻`fx`は

- `m ≤ x`、`FirstAt a x fx`、`y < x`、
- debtノード `⟨horizon, anchor, debt, fy⟩` から `⟨horizon, anchor, debt, fx⟩` への `PhaseSearchProgress`

を与える。

**証明:** `legalSubtraction_firstAt_predecessor`の結論から、`m ≤ y < x` により目標下界が引き継がれ、`fx < fy` がdebt局所成分(初出時刻)の狭義下降(`phaseSearch_debtTimeDrop`)を与える。horizonとanchorは固定のままである。ここでは`DebtInvariant`の再構成(特に `x < anchor`)までは主張しない点に注意。anchor条件を要するかどうかの精密な分岐は`DebtInvariant`の `debt_legalSubtraction_preservesInvariant` と`DebtStep`の分類に委ねられる。

## 全体の中での位置づけ

証明地図の負債局所解析層のうち、合法減算枝の最小部品である。本モジュールは`DebtBackward`から直接importされ、そこでは一歩の後方解析をここから出発して極大後方減算鎖へ拡張し、鎖長に応じてblocker露出(`CoverageStep`)かanchor境界かの三分法(`legalSubtraction_maximalBackward_trichotomy`)へ発展させる。`DebtInvariant`(不変量込みの一歩解析)と対になる、不変量なしの汎用版という位置づけである。
