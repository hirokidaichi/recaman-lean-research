## 後半候補・反例・停止の監査済み範囲

対象版と合同判定は [01:30合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、
凍結元文・逐語signature・根拠対応は
[01:30 packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。

後半候補は、限定意味監査の合格と総合研究手続きの合格を分けて記録する必要がある。
H-20260920-02、H-20260920-03、H-20260920-05はいずれも、対象を限定した独立監査で
statementと証明・例の対応が合格した部分を持つ。しかし三者とも昼の形式化前に必須だった独立入口検査が
欠け、後日の意味監査で遡及的に埋められない。カードは `CONJECTURED`、総合判定は**未完了**であり、
新規登録・昇格・確立済みの後続依存への採用は行わない。

H-02で限定合格した `short_tight_avoids_ss2_window` は、任意の正周期 `p` と周期符号語 `e`、
nodup・範囲内current-Aの緊密 `B`、各メンバーが最小P2のlag 3/7/11、任意の整数donor時計 `u0`、
長さ11 P2・SS=2 donorを量化する。donor最小性、donor current-A、ambient Hall、正driftは不要だが、
一般lag・lag 15以上・完全all-lag U・実Recaman軌道には届かない。p13
`AASSSAAAASSSS`, `u0=10`, `B=[7]` はnonminimal/current-S donorと非空tight Bの共存例で、
真offset11・phase12は回避される。これは非空性の確認であって、全周期の証明や新holdoutではない。

H-03で限定合格した `tight_neighborhood_eq_of_p2_prefix` は、`m<=lag<=11`、m側P2、lag側tightから
`N_m(B)=N_lag(B)` を結論する。Lean文はfull-lag P2もmの最小性も仮定せず、元カードより広い。
元カードからLean文への向きは確認されたが、逆向きは成り立たない。元カードのstrict/full-P2/tight領域は
既知p1..12とp15で0件であり、globalな不存在でも等式の反例でもない。p4 `AAAS` のlag4例は
full-P2でなく、p9 `ASAAASASS` のlag7例はtightでない。従ってstrict prefix reductionを
行使済みの新入力と記載しない。

H-05で限定合格したのは `moment_ending_A_budget`、`moment_ending_AA_ss2`、
`ss2_intervening_prefix` の局所3宣言だけである。最後は任意有限語 `w` について、A-endedな
`X=w++[A]` がmass 0、`moment(X)+|X|<=0`、SS数2以下ならstrictなS-ended P2 prefixを持つ。
非空例は `AASASASASSSA`、一仮定ずつ落とす負対照は `AAASSS`、`SASASSSA`、`SA`、
`AAASSSSA`。一方、後半Lean、紙§3-5、AAS/w1各配置、true-oldest分解との結合、周期lift、
任意長donor回避・削除は未監査で、H-05全体の最終定理もない。

H-20260920-04については範囲の異なる確定的な負結果がある。p16周期語
`SAAASSSASASASAAA`、`u0=15`、`B=[3]` ではdonor窓 `AASASASASSSAAAS` がP2・SS=2、
proper P2 prefix 3、真oldest offset15・phase0で、`N(B)=[0]`。従って真oldest回避と削除後Hallが失敗する。
この監査済みliteralは**非最小lag15 donorへの延長だけ**を `REFUTED` とし、その同一ルートを
`STOPPED` とする。最小lag15、任意lag、一般Gate T6、実軌道、旧census、第二w1例、最小p/lagは
決めない。固定offset11はphase4で、真oldestの代用ではない。

共通の境界として、E-240は純AAS forcing、E-069は最古Sの大域単射を退ける。E-345はSS>=3対照、
E-351はnext-A等を既に仮定するため未来AAS結論へ逆用できない。短いUの完全性をall-lag Uへ、
有限周期語を実軌道へ、限定意味合格を総合合格へ読み替えない。p32/33や旧censusは既に使用済みまたは
独立再認証されておらず、新holdoutと呼ばない。

以上より、週間後半の確立済み結論は「三つの限定意味監査結果」と「H-04の非最小lag15に限る反例・停止」
までである。H-02/H-03/H-05は総合未完了のため `CONJECTURED` を維持する。新しい独立入力なしに
一般lagルートを延長しない。次に再開するなら、任意lagと実軌道を分離した新しいbounded cardを作り、
形式化前の独立入口監査を先に完了する。
