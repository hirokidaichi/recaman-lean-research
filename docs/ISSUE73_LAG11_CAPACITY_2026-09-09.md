# Issue 73: lag-11 capacity, all periods; lag-by-lag charging stopped

## 結論

**任意の周期長に対し、lag≤7のP2供給と最小lagがちょうど11の加算phaseの和は
減算phase数以下であることをLeanで証明した。全lagの供給不足という#73本体は
未解決で、issueはOPENのままとする。型ごとのlag延長による課金クラスは停止した。**

これは固定符号周期の全面的な排除でも、全射性・非全射性の証明でもない。
正符号和の語では `|A| > |D|` なので、残る加算は最小lag≥15を使う。
lag-15までの和は紙上で成り立つが、dに依らない共通の課金は得られなかった。

作業baseは`8b07f93fbbb17352c091cabaa333fc366a66c04f`。
第1passは[短い供給の容量](ISSUE73_PERIODIC_SUPPLY_2026-09-07.md)（E-071）。
本passの仮説カードは
[H-20260908-01](HYPOTHESIS_CARD_2026-09-08_LAG11_INJECTION.md)、
[H-20260908-05](HYPOTHESIS_CARD_2026-09-08_LAG11_GLUE.md)、
[H-20260908-04](HYPOTHESIS_CARD_2026-09-08_LAG15_INJECTION.md)、
[H-20260908-06](HYPOTHESIS_CARD_2026-09-08_UNIFORM_SELECTOR.md)。
再現は[issue73_20260908 bundle](data/issue73_20260908/README.md)。

## 証明した正確な命題

周期pの符号列ε: Z→{−1,+1}で、加算phase集合をA、減算phase集合をDとする。
加算phase t のP2供給lag d は

```text
Σ(i=1..d) ε(t−i)=1,    Σ(i=1..d) i·ε(t−i)=0.
```

U7を`1≤d≤7`の供給lagを持つ加算phase集合、U11minを最小P2 lagがちょうど11の
加算phase集合とする。全ての周期語で

```text
|U7 ∪ U11min| ≤ |D|.                          PROVED-LEAN  (E-080)
```

U7とU11minは最小lagが異なるので相として交わらない。したがってこれは

```text
|U7| + |U11min| ≤ |D|.
```

と同値である。U7側だけは既にE-071、U11min側だけはE-087である。
本passが閉じたのは両者の像がDへ単射に落ち、互いに交わらないことである。

主要定理は[LagElevenPeriodic.lean](../Recaman/LagElevenPeriodic.lean)の
`suppliedCount_add_u11Count_le_subtractionCount`。
補助は`phi7Phase_inj`（実7窓の強制ビット衝突）、`phi11Phase_inj`、
`phi7_phi11_image_ne`（`u7Blocked`を実際の11窓へ接着）。
有限核は[LagElevenSupply.lean](../Recaman/LagElevenSupply.lean)の17型、
chargeがSであること、3つのU7規則との矛盾、型対のsame-time衝突（E-079）。

紙上では同じ方法で155個のmin-lag-15型にも単射chargeがあり

```text
|U7 ∪ U11min ∪ U15min| ≤ |D|.                 PROVED-PAPER  (E-086)
```

となる。これは155行の型→offset表であり、lagの閉形式ではない。Lean化していない。

## 紙上証明とLeanの検証方法

min-lag-11窓は`{1..11}`の5元部分集合で和33、かつlag 3と7のP2接頭辞を持たない
ものに限られ、ちょうど17型である。各型を窓内の一つのS-offsetへ送る。
そのSは、U7の三規則（lag3 → t−3、lag7 h=1 → t−7、lag7 h=2 → t−5）の
いずれを置いても強制符号と矛盾する。相異なる型をcharge距離`δ=j−i`で重ねると
符号が衝突する。したがってφ11はU7像と交わらず単射である。

最初のgap-2優先割り当ては周期15の`SSSASSAAAASSAAA`で単射が壊れた。
衝突距離を`i−j`と書いていたのが原因である。CSPで取り直した割り当て
（`δ=j−i`、独立ワーカーのSOLUTION0と一致）が本証明の写像である。

Leanでは17型の有限核を`decide`し、任意の周期符号列から11符号窓を復元して
円上の単射と像の非交を構成する。potentialの有限状態検査ではなく、実際の
過去符号からのsemantic bridgeである。周期長の上限はない。

U7のfollowing-gap類（=1, =3, ≥4）と交わらないgap類への一様課金は、
HARD型`(1,4,7,10,11)`が交わりのないexact gapを持たず、gap=2が
`ASSSASSAAAASSA`（p=14）で同一Sへ衝突するため棄却した（E-085）。

## 本体を狙った反証検査

以下は全lagの証明ではなく`COMPUTED`である。

| 対象 | 固定した検査 | 結果と限界 |
|---|---|---|
| φ11の循環回帰 | period1..18の正符号和229,045語、26,586件のlag-11 | 単射・U7非交。証明の正当化ではない |
| φ15の循環回帰 | period1..18の全524,286語、20,621件のlag-15 | 単射・φ7∪φ11非交。E-086の確認のみ |
| E-067の未使用period | p=19,20 discovery、p=21,22 holdout、正符号和3,487,066語 | U=Aは0。全periodの証明ではない |
| L=23シフトグラフ | 8,388,608状態、辺不等式0違反 | 正サイクルなし、max P=5。全Lの証明ではない |

## 失敗した一般化と停止

- following-gap分割によるlag-11一様課金：E-085 `REFUTED`。
- two-child κ降下のS単射（I_inv）：`ASSSAASAAASAA`のt=11は両childがA。E-082。
- その許可修理（least-P2窓のκ降下S）：`ASASASAAASS`でHall衝突。E-083。クラス停止。
- L=7 potentialの新しい7bit埋め込み：`SSAAAAAASSS`へのA辺で偽。修理も偽。E-084。
- 宣言したd非依存セレクタ（raw Sのmin/max/median等、blocked集合のmin/max/median）：
  φ7の3型を同時に再現しないか、lag-15でZ開対を持つ。E-088。
  **lag-by-lag型→offset課金クラスを停止。**

これらは特定の証明案の停止であり、#73本体や非周期の数列に対する反例ではない。

## 残る問いと次の判断

E-067/E-070は`CONJECTURED`のまま。正符号和の反例語は最小lag≥19を使う。
155行表のlag-19延長、period延長、155行の`decide`は完了に数えない。

再開条件は一文である。155のmin-lag-15型に対し、新しい型表なしで単射な局所障害が
書けるか、`SSAAAAAASSS`で上がり`AAASAASSSSS`のSで高々1下がる閉形式potentialが
出たときだけ再開する。

変更は新Lean module2本とAudit/import統合、仮説カード、証拠台帳、frontier/maps、
実験bundle。実行コマンドと出力は
[再現一覧](data/issue73_20260908/README.md)に保存する。
