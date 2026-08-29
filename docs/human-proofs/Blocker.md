# Blocker

**役割:** 下降を止めた既出値(blocker)の抽象証明書を定義し、値と初出時刻が同時に下がる「二重降下」と、その整礎性を証明する。

## このモジュールの役割

レカマン数列の全射性予想への攻略では、目標値へ向かう連続減算(下降)が途中で止まったとき、
止めた原因である既出値を新しい探索ノードとして再帰する。このモジュールは、その原因値を
証明付きで保持する抽象的な証明書 `BlockerCertificate` を定義し、証明書から

1. blockerの値は現在値より真に小さい、
2. blockerの初出時刻は現在値の初出時刻より真に早い、

という二重降下を導く。さらに `(値, 時刻)` の同時降下関係が整礎であることを示し、
blockerをたどる無限の系譜が存在しないことを保証する。ここでの議論は数列 `seq` を
抽象化して行い、実軌道への特殊化は `ActualDescent.lean` が担う。

## 主要な定義

### `FirstAt` (L6)

`FirstAt seq x t` は「`seq t = x` であり、かつすべての `u < t` で `seq u ≠ x`」、
すなわち値 `x` が時刻 `t` で初めて出現することを表す。大域探索では値だけでなく
この初出時刻も進行度として使う。

### `SeenBefore` (L10)

`SeenBefore seq x t` は「ある `u < t` で `seq u = x`」、すなわち値 `x` が時刻 `t` より
真に前に出現済みであることを表す。

### `BlockerCertificate` (L24)

下降中に出会ったblocker(妨害値: 減算先がすでに履歴にあるため合法減算を続けられなく
する既出値)の抽象証明書である。次のデータと証明を保持する。

- 現在値 `v` とその初出時刻 `f`(`first_v : FirstAt seq v f`)
- 妨害値 `y` とその初出時刻 `fy`(`first_y : FirstAt seq y fy`)
- 下降歩数 `k` と正値性 `0 < k`, `0 < y`
- blocker方程式 `y + (k·f + upperTri k) = v`。これは「時刻 `f` から `k` 歩の連続減算で
  `v` から `y` に届く」という減算算術を、切り捨て減算を使わずに書いたものである
- `seen_before_block : SeenBefore seq y (f + k)`。`y` は下降が止まる時刻より前に出現済み
- `above_during_descent : ∀ t, f ≤ t → t < f + k → y < seq t`。下降区間の内部では
  数列の値は常に `y` より真に大きい(つまり `y` は下降の内部では現れていない)

### `Occurrence` (L70)

値と時刻の組 `⟨value, time⟩` を保持する探索ノードである。blockerが同時に減らす
二つの量をひとつのデータにまとめる。

### `EarlierSmaller` (L75)

`Occurrence` の間の関係で、子の値が親の値より真に小さく、かつ子の時刻が親の時刻より
真に早いことを表す。blocker一回分の再帰でノードがこの関係で降下する。

## 定理と証明

### `upperTri_pos` (L13)

**主張:** `0 < k` ならば `0 < upperTri k`。ここで `upperTri k = k(k+1)/2` は上三角数である。

**証明:** `k = j + 1` と書けば `upperTri (j+1) = upperTri j + j + 1 ≥ 1` である。補助補題。

### `BlockerCertificate.value_decreases` (L38)

**主張:** どの証明書についても `y < v`。

**証明:** blocker方程式 `y + (k·f + upperTri k) = v` において、`k > 0` だから
`upperTri k > 0`(前補題)、したがって加えられる量 `k·f + upperTri k` は正である。
正の量を足して `v` になるのだから `y < v` が従う。

### `BlockerCertificate.first_time_decreases` (L52)

**主張:** どの証明書についても `fy < f`。すなわち、真のblockerは現在値 `v` の初出より
前に初めて出現していた。これが二重降下の時刻成分である。

**証明:** `seen_before_block` により、ある `u < f + k` で `seq u = y` である。
初出時刻の最小性から `fy ≤ u`(もし `u < fy` なら `FirstAt` の第二条件に反する)、
よって `fy < f + k` を得る。次に `f ≤ fy` と仮定して矛盾を導く。このとき `fy` は
下降区間 `[f, f+k)` に入るので、`above_during_descent` より `y < seq fy` となるが、
`FirstAt` の第一条件より `seq fy = y` であり、`y < y` という矛盾が生じる。
したがって `fy < f` である。

直観的には、「下降の内部では値はずっと `y` より上にある」ので、`y` の出現は下降開始
時刻 `f` より前でしかありえない、という議論である。

### `earlierSmaller_wellFounded` (L80)

**主張:** 関係 `EarlierSmaller` は整礎である(無限降下列が存在しない)。

**証明:** `EarlierSmaller` は第一成分(値)だけを見ても真に減少するので、自然数値を
測度とする整礎関係の部分関係である。部分関係の整礎性は親関係の整礎性から従う。
時刻の減少は帰納には不要な追加情報だが、blocker辺が常にそれも減らすことを
`EarlierSmaller` の定義に記録している。

### `BlockerCertificate.earlierSmaller` (L86)

**主張:** 証明書があれば、ノード `⟨y, fy⟩` はノード `⟨v, f⟩` に対して
`EarlierSmaller` の関係にある。

**証明:** 値の降下は `value_decreases`、時刻の降下は `first_time_decreases` そのものである。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「下降・blocker」層の最下部にあたる。`FirstAt` と
`SeenBefore` はここで定義され、`History.lean` 経由でリポジトリ全体の基礎語彙になる。
抽象証明書 `BlockerCertificate` は `ActualDescent.lean` の
`ActualBlocker.exists_certificate` によって実軌道の具体的なblocker配置から構成され、
その二重降下が `TargetDescent.lean` の `targetDescent_lands_or_doubleDescent` を経て
`Coverage.lean` の値に関する強帰納法(`CoverageStep` の第二枝)を駆動する。
