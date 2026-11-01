# Hypothesis card: 同mass old源は近くに集まりarea幅4か

- ID: H-20261027-12
- Status: PROVED-LEAN（E-426）
- Parent: R-20261027-01/E425/H10-R19小商gate。Mode: 局所探索、07:11開始、15分gate、CPU探索0。

任意BlockWord wの任意prefix uでmass u=0ならlength u<=6かつ-4<=area u<=4を導けるか。これから同じwの同mass suffix二本は開始位置距離<=6/area差絶対値<=4となるか。
同じpadded実prefixで、同じ高さへ終わる二つの実old P2窓には同massが必要なので、元source pairの必要area差にも同じ制約を接続する。
全mass/全語長を量化し、mass3/4だけの既知分類を新成果にしない。mass4 area9/13は差4で残す。独立prefix由来のpairを同じprefixのように扱わない。

紙上chain: prefixを最後のatom内で切る。atom途中mass>=-2だから、それまでの全BlockWord mass<=2。既存mass1/2分類と三atomの有限prefix表だけを使い、zero-prefix長6/area±4を証明。二old suffixをprefix+suffixに分け、mass差0とarea加法で差を供給。
反証: 空prefix/同じstart、tripのmass4 area9/13境界、atom内でmass0となる長さ2/4/6、途中S負mass、元Intp/実Winの全clock。強い幅3や距離5へは修理せず、既知境界を壊さない。
受入: 全長zero-prefix条件と同mass源差のLean/G5/Audit/check、actual window接着。次のr4削減測定をする場合は独立の新入力として費用/holdout/argvを再固定し、旧jobの時間追加はしない。
15分で全長同mass制約に届かなければSTOPPED。表サイズ超過をcap増加で解決しない。数学修理は1回まで。

07:14全体check424jobs/2904宣言/G5/lint/Audit成功。数学修理0、aasW/tripWのsimp展開だけ修正。全長の新しいsource関係を供給したがE427のr4候補削減は0/0で、同大表kernel再開条件には届かなかった。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-12/explore/same-mass-old-span: 1分47.306秒、H-20261027-12/audit/same-mass-old-span: 1分20.899秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
