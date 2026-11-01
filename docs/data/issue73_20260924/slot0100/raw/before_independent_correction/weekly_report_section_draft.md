## 確立済み部分: E-360 の短い緊密集合と削除系

今週確立できた最大の主張は、周期長の上限を外した一方で lag を短い三種に限定した局所結果である。
E-360 の最終Q `short_tight_avoids_ss2_donor` は、任意の `p>0` と周期符号語 `e` について、重複のない
緊密リスト `B` の各要素が `p` 未満のcurrent-A位相であり、その窓が最小P2かつ
`lag in {3,7,11}` なら、最小lag-11・SS=2 donorの真の最古S位相が `N(B)` に入らないことを
`PROVED-LEAN` とする。pには上限がない。ただし任意lagではなく、lag 15以上の要素を含むBには何も言わない。
ambient `U`、仮定Hall、正driftは最終Qの仮定ではない。短窓selectorからBの全sublistのHallを内部で導く。

局所Wは別の読み方が必要である。`w1_owns_oldest` と `w1_next_addition` は、周期性から直接出る無条件定理
ではなく、`OwnerFamily` の4フィールド `window/addA/own_mem/onto` を仮定し、w1メンバーがoffset 7の
最古Sを所有し、その次符号がAであると述べる条件付き定理である。周期的な緊密Bへ使うときは、
`p>0`、周期性、nodup U、U上のHall、`B.Sublist U`、緊密性、範囲内current-A、最小P2
lag 3/7/11からE-358/E-359の構成でOwnerFamilyを実現する段階を省けない。
`ownerFamily_of_minimal` と `tight_owner_family` は既存依存の抽出であり、E-360の新規性には数えない。
E-351のfuture-AAS定理はW側の仮定を既に必要とするため、Wの証明入力として循環利用していない。

`short_supply_donor_deletion` も任意の正周期pを扱うが、全 `U` メンバーが範囲内current-Aで、
最小P2のlag 3/7/11に限られる。任意の `B.Sublist U` についてdonorの真の最古Sを削除した後もHallを保つ。
Uの完全性、donorのU所属、正drift、実軌道は仮定しない。従って「完全な全lag供給集合からの削除」ではなく、
短い要素だけからなるUに限った直接系である。証明は短窓Hall、E-360 Q、既存のtight/slack削除補題の
合成であり、非空・実削除例を持つ意味のある `PROVED-LEAN` 系ではあるが、新しい数学的入力でも新規E行でもない。

意味監査では、p8/p11の非空・実削除例、空B、周期境界、E-240の非AAS緊密集合、E-069/E-133の
最古S単射反例を照合した。SS=2を外すとp12 `AAAASAAASSSS`, `B=[2,5,7]` で失敗する。
また7 donorの真の最古offsetは10または11であり、固定offset11への置換は不可である。
使用済みp32/33標本は有限証拠にすぎず、全体の独立認証も未完了で、Lean証明の代用にしない。

以上から、今週言えるのは「一般p・短lagにおけるQと、そのall-short Uに限る削除系」までである。
一般lag、lag 15以上を含む緊密集合、一般Gate T6、完全all-lag U、E-070/E-067、実Recaman軌道、
全射性は未解決。昼の形式化前独立入口検査欠落と初回checker保存欠落も履歴として残す。
公式G5冒頭の `application pending` は適用前時点の履歴文であり、実適用と適用後PASSの正本は
`docs/adversarial_audits/H-20260920-01_20260921_0200.md` の最終節である。旧文言は遡及改変しない。
この週は範囲を延長せず、次の計画では一般lagへの独立した橋を新しい一問として入口監査から始める。
