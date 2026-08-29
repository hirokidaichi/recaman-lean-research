# PermanentAbovePotential

**役割:** tail最小値で強制される二連続forced additionがポテンシャル`G`に一様な方向性を課さないことを、カーネル検証済みの実軌道例二つで棄却監査する。

## このモジュールの役割

`PermanentAboveTail.lean`は、恒久上方tail(以後ずっとtargetより大きい軌道区間)の最小値で二連続の強制加算(forced addition、減算先が使えず加算を強いられる遷移)が起きることを証明した。この局所パターンから新しい下降尺度を作れないか、という自然な候補が「符号付きポテンシャル`G(q,r) = r − upperTri(q)`(商剰余座標に対する本研究固有の整数量)が二連続forced additionで単調に動く」という仮説である。本モジュールはこの候補を反例で棄却する。実軌道上の二つの二連続forced addition(`2→7→13`と`7→13→20`)がポテンシャルをそれぞれ厳密減少・厳密増加させることをLeanカーネルの`decide`で検証し、二連続forced additionのパターン単独では非増加不変量も非減少不変量も支えられないと結論する。したがって新しいtail rankはポテンシャルではなく、historical blocker(既出値による下降妨害の証明書)などの大域的証明書と結合しなければならない。

## 主要な定義

### `DoubleForcedAdditionAt` (L15)

時刻`time`で強制される局所遷移パターン: 時刻`time+1`への一歩と時刻`time+2`への一歩がともに減算不能(`¬CanSubtract`)であること。`PermanentTailMinimumCertificate`から最小値・履歴の情報を忘れ、座標解析に関係する二歩のパターンだけを残した形である。

## 定理と証明

### `PermanentTailMinimumCertificate.doubleForced` (L21)

**主張:** tail最小値の証明書は`DoubleForcedAdditionAt time`を含意する。

**証明:** 証明書のフィールド`first_forced`と`followup_forced`の射影のみ。

### `doubleForced_potential_decrease_actual_example` (L29)

**主張:** 実軌道の時刻4では二連続forced addition `2 → 7 → 13`が起き、座標は`CoordinatesAt 4 0 2`(`a(4) = 2 = 4·0 + 2`)から`CoordinatesAt 6 2 1`(`a(6) = 13 = 6·2 + 1`)へ移り、ポテンシャルは`potential(0,2) = 2`から`potential(2,1) = −2`へ厳密に減少する。

**証明:** レカマン数列の実装は実行可能なので、四つの主張(二歩の減算不能性、両端の座標関係、ポテンシャルの不等式)はいずれも有限計算であり、Leanカーネルの`decide`で検証する。数値の確認: `a(4) = 2, a(5) = 7, a(6) = 13`。`upperTri(0) = 0`より`G = 2 − 0 = 2`、`upperTri(2) = 3`より`G = 1 − 3 = −2`。

### `doubleForced_potential_increase_actual_example` (L41)

**主張:** 一つ重なった時刻5では二連続forced addition `7 → 13 → 20`が起き、座標は`CoordinatesAt 5 1 2`(`a(5) = 7 = 5·1 + 2`)から`CoordinatesAt 7 2 6`(`a(7) = 20 = 7·2 + 6`)へ移り、ポテンシャルは`potential(1,2) = 1`から`potential(2,6) = 3`へ厳密に増加する。

**証明:** 同様に`decide`による有限計算。`upperTri(1) = 1`より`G = 2 − 1 = 1`、`upperTri(2) = 3`より`G = 6 − 3 = 3`。

### `doubleForced_potential_has_both_directions` (L53)

**主張:** 二連続forced additionのパターンは、ポテンシャルの非増加不変量も非減少不変量も支えない。すなわち、`DoubleForcedAdditionAt`と両端の座標を満たしつつポテンシャルが厳密減少する実例と、厳密増加する実例が、ともに存在する。

**証明:** L29の例(時刻4、`G: 2 → −2`)とL41の例(時刻5、`G: 1 → 3`)をそれぞれの存在文のwitnessとして与えるだけである。二例は時刻が一つ重なった同じ実軌道区間`2 → 7 → 13 → 20`から取れている点が要点であり、局所パターンの同一性が方向を決めないことを最小限の材料で示している。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「tail potential監査」(局所候補棄却)に対応する。`PermanentAboveTail.lean`の最小値証明書を入力とし、そこから伸び得た証明方針の一つ(ポテンシャル単独の新しいtail rank)を、実軌道のカーネル検証例で閉じた否定的監査である。この棄却を受けて、後続の`PermanentAboveHistory.lean`はポテンシャルではなくhistorical blockerの反復(downcrossによる履歴予算下降、またはtail最小値の厳密下降)を下降尺度に採用し、`PermanentAboveCanonical.lean`・`PermanentAboveCycleRank.lean`はdual budget `seenBelowCount`と四成分cycle rankへ進む。計算実験を仮定に使わないという本リポジトリの方針(実例はすべて`decide`によるカーネル検証)を体現するモジュールでもある。
