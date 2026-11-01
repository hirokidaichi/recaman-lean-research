# H-20261102-05: 低separatorのsource-prefix二乗課金

Status: PROVED-LEAN（末尾の終了時判断を正本とする。以下は開始時の仮説・費用条件）。親R-20261102-01、H04/H06の後の別機構。06:45近傍開始、15分gate07:00。CPU探索追加0。旧五tuple kernelはSTOPPEDを保持し再実行しない。

任意元p/padded/zero-fullpositive/正三run zerohead/同old targetmass3/最終S1又はS2で全長full-tail free-gapか。直前のactual critical/cutはheadfree4/fullfree=j/R<=M<=6/第二S source必須を供給している。これを結論として利用し、同じ基点のsource条件から矛盾できるか。未知Propやfree結論は入力しない。

新しい機構: 第二S源の残q、d=m-q>=0、source以前b=Sh AM Sd、source以後x=Sq AL Ss AU Svと置く。p=i+j-T=i+2-v>=0。原始二P2の同source恒等式E460とmass3から
2(M-p)^2 = 2R²+ku+16+4Md+4p cntF(x)。
mass条件はM-p=h+d-3>=-2。BlockWord mass3のkeyは-2<=ku<=2、actual counterはM<=6/R>=5/R<=M。

p>=1ならM-p<=5で左<=50、右>=64。p0/d>=1なら左<=72、右>=84。p0/d0なら2(M²-R²)=ku+16 in[14,18]だがM=Rなら0、M>Rなら次の平方差で>=22。全場合矛盾。S/head面積/U4/五tupleを上限へ切らず、同じprefixのcrossを残す独立した一様不等式である。

反証pass: p0と負(M-p)の境界-2を含め、M-pを非負と仮定しない。d0をcross正の場合へ混ぜない。M>=RはA cutでありfree-prefix置換ではない。ku<=2は同じmass3 targetのみから供給し他massへ外挿しない。p>=0/T+2=v+j/R5/M6はactualから供給しraw補題で黙って仮定を落とさない。

受入: raw全長矛盾とactual criticalからの内部接着、元p adapter、個別-M512/10CPU per-process/20wall/G5/Audit/全check。定数だけの修理や旧jobの資源追加はしない。一回数学修理後失敗ならこの方法もSTOPPEDとし、残時間は異なるsource位置/非zeroheadの仮定監査へ。四run全体/任意rank/C1/全射性は未解決。

結果: E-514 PROVED-LEAN。全check H07-low-fullcheck 06:52:05終了、575jobs/3310宣言、全axiom許可集合内。個別-M512/全10module lint/G5/Audit接続済み。停止五tuple法の復活なし。次unitは長いseparatorのsource予算と実old課金。

## 終了時判断

E-514 PROVED-LEAN、全体check成功。 全体検証・逐語audit・実績正本は11/02 DAILY/journalを参照。親C1全体は未解決。
