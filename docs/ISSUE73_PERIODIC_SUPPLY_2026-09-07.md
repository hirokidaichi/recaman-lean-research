# Issue 73: short supply capacity, all periods

## 結論

**任意の周期長に対し、7歩以内のP2供給を持つ加算phase数は減算phase数以下であることを
Leanで証明した。全lagの供給不足という#73本体は未解決で、issueはOPENのままとする。**

期間を固定した列挙から、周期長に上限のない部分定理へ進んだ。一方、この結果は固定符号周期の
全面的な排除でも、全射性・非全射性の証明でもない。依然として必要なのは長い供給区間の制御である。

作業baseは`b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`。仮説カードは
[H-20260907-09](HYPOTHESIS_CARD_2026-09-07_ISSUE73_PERIODIC_HALL.md)。
前回の並列調査で1位とした④を、今回の作業対象とした。

## 証明した正確な命題

周期pの符号列ε: Z→{−1,+1}で、加算phase集合をA、減算phase集合をDとする。
加算phase t のP2供給lag d は

```text
Σ(i=1..d) ε(t−i)=1,    Σ(i=1..d) i·ε(t−i)=0.
```

U7を`1<=d<=7`の供給lagを持つ加算phase集合とすると、全ての周期語で

```text
|U7| <= |D|.                                      PROVED-LEAN
```

したがって符号和が正なら`|A|>|D|>=|U7|`で、U7に含まれない加算phaseがある。
周期が最小周期である必要はなく、小周期で履歴窓が複数回折り返す場合も含む。

主要定理は[ShortPeriodicSupply.lean](../Recaman/ShortPeriodicSupply.lean)の
`periodic_capacity`と`exists_phase_without_short_supply`。
`supplied_window_iff`が、符号列の実際の過去7符号から作った判定と上記P2を両方向に結ぶ。
`lag_eleven_survives_short_exclusion`は`SSSSAAAASAAA`のphase7について、lag11の供給と
lag<=7の供給不能を同時に証明する。短い供給の排除から全供給の排除へ飛躍してはいけない。

## 紙上証明とLeanの検証方法

独立した紙上証明は、最小供給lagによる三つの割り当てを使う。lag<=7なら最小lagは3または7。
lag3は直前のSへ、lag7の二つの新しい型はそれぞれ2つ前・1つ前のSへ割り当てる。
像のSの次のgapは、それぞれ4以上・1・3となるため、三種類は衝突しない。
同種内でも固定したS-index移動なので単射となる。任意部分集合のHall条件もU7については従う。

Leanでは同じ容量結論を、全128状態の7bit窓に対する明示的な整数potentialで証明した。
加算でP2供給があれば+1、他の加算で0、減算で−1を課金し、全256遷移のpotential不等式を
`decide`でkernel検証する。実符号列から窓を構成し、任意の周期に沿って不等式を足すと
potential差が消える。未知の状態閉包や周期長上限を仮定していない。

このLean証明が形式化するのは容量結論であり、紙上の具体的なmatching写像自体ではない。
U7に制限したHall全部分集合の結論は、独立監査済みの`PROVED-PAPER`として区別する。

- [三分類の紙上証明と反証検査](data/issue73_20260907/macro_proof_attempt.md)
- [周期折り返しの独立監査](data/issue73_20260907/short_lag_independent_audit.md)
- [Lean statementと意味の独立監査](data/issue73_20260907/lean_semantic_audit.md)

## 本体を狙った反証検査

以下は全lagの証明ではなく`COMPUTED`である。

| 対象 | 固定した検査 | 結果と限界 |
|---|---|---|
| 最小P2 lag区間の全S候補によるHall条件 | period1..12の3,458語、13..18の225,587語 | 反例0。全periodのHallは未証明 |
| 短い供給だけで容量超過する周期の探索 | lag上限3,7,11,15,19の有限状態グラフ | 正重みcycleなし。各potentialを全edgeで検査。上限19では524,288状態・1,048,576辺。全lagへは外挿しない |
| U7の既知写像を固定したlag11への拡張 | 同じ229,045語、最小lag11の26,586行 | 残るS候補からmatching可能。一般に固定写像を拡張できるとはまだ言えない |

第1・第3検査は既使用の語範囲を新しい性質について調べたもの。未使用のcanonical軌道や独立な
新規データとは呼ばない。第2検査は周期長を伸ばした列挙ではなく、正重みcycleがあれば任意長の
周期語反例を抽出できる検査だが、固定したlag上限に限る。Leanへ昇格したpotentialは上限7だけ。

## 失敗した一般化と反例

- 最小供給lagの最古位置が必ずS、という簡略化はlag11の`SAAASAASSSA`
  （新しい符号から古い符号へ記載）で偽。
- 最小供給区間の第2momentが必ず負、というrank案は`AAASSASSSAA`で偽。
  第1momentは0だが第2momentは+36。
- 今後Aだけを続けた時の残り供給回数を予算にする案は、履歴`SSSAAAA`へSを一つ追加すると
  需要が0から2へ増えて破れる。古いSによる供給が再び可能になる点を無視できない。
- 正の高さを保つ「escape phase」を選べば供給不能になるという案と、その許可された修理も偽。
  `A^5 S^4 (AS)^8`は符号和1、唯一のescape phase0がlag119で供給される。
  [幾何の調査](data/issue73_20260907/geometry_attempt.md)では同じ機構の全r反例族を紙上で与えた。

これらは特定の証明案を停止する反例であり、#73本体や非周期の数列に対する反例ではない。
限定した[一次文献調査](data/issue73_20260907/literature_audit.md)では直接使える定理は確認できなかった。
これは新規性の証明や網羅的な文献調査ではない。

## 残る問いと次の判断

全加算がP2供給可能な正符号和の反例語が存在すると仮定するなら、今回の定理から少なくとも一つの
加算は7歩より長い最小lagを使う。P2の符号数・momentのparityにより、紙上では最小lag>=11となる。

次の具体的な入口は、lag11の新しい型を既存のU7割り当てへ一様に追加できるかである。
ただし有限lagごとの形式化を延々と増やすだけでは#73は閉じない。追加の分類から全lagに共通する
割り当て・potentialの構造が得られるか、または全供給を満たす反例語が得られるかを継続条件とする。
本体の`U!=A`と強化`|U|<=|D|`は`CONJECTURED`のまま。今回反証したselectorや単純予算は再開しない。

変更は新Lean moduleとAudit/import統合、仮説カード、証拠台帳、frontier/maps、実験bundle。
実行コマンド、source hash、exact出力、全体監査は
[再現一覧](data/issue73_20260907/README.md)に保存する。
