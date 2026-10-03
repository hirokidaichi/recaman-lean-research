## 2026-09-24 週間記載の監査

`tight_neighborhood_eq_of_p2_prefix` のLean文は、任意の正周期 `p`、周期符号語 `e`、nodup・範囲内
current-Aの `B`、`m b <= lag b <= 11`、`P2(past e b (m b))`、lag側の緊密性から
`N_m(B)=N_lag(B)` を結論する。full-window `P2` と `m` の最小性を仮定しないため、元カードより広い。
元カードからLean文への向きは `exists_minimal_p2_prefix` で得られるが、Lean文の例を元カードのstrict例へ
逆向きに流用できない。

限定意味監査は合格したが、元カードの `m<lag`・full-lag P2・tightを同時に満たす領域は既知の
p1..12およびp15で0件で、globalな非存在も反例も証明されていない。p4 `AAAS`, `B=[2]`,
`m=3,lag=4` は広いLean文のstrict/tight例だがlag4窓はP2でない。p9 `ASAAASASS`, `B=[4]`,
`m=3,lag=7` はfull-P2 strict例だがtightでなく近傍が異なる。昼の独立入口検査も欠落するので、
総合手続きは**未完了**、状態は `CONJECTURED` のまま、strict reductionを行使済み新入力としない。
詳細は [9/24合同監査](adversarial_audits/H-20260920-02_20260924_0130.md)、その根拠となる
[9/23監査](adversarial_audits/H-20260920-03_20260923_0200.md) と
[9/24週間整理packet](data/issue73_20260924/slot0130/candidate_packet.md) を参照。
