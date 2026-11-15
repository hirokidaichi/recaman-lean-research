# 一つのSの削除でも古い供給を任意に多く失う

2026-11-16、H-20261116-04。E726のm1はPROVED-LEAN相当の閉じた反例証明書（registry label REFUTED）。以下の全mは完全PAPER/未Lean・人間レビュー未、E727 REFUTED。停止するのは「同じpadded old prefixを保った一S削除のfree変化を、削除本数・head長・幅だけの固定費用で抑える」機構。C1 counterではない。

任意m>=1で

    f_m = SAAA (SSSSAAAA)^m
    g_m = SAAA SSSAAAA (SSSSAAAA)^(m-1)

を同じ元Nat0から読む。範囲外はA。old境界n4は両側で同じBlockWord SAAA。h4/C3、削除するSは1本、元幅4/新幅4固定、最初S-run直後を基準にした元future上ceiling4=C+1。gの全tailはFn+1以下。各語の有限全tail非空prefixで元actual供給+1<=Sが成立する。global originより前やold sourceを切り捨てない。

## 全元供給の分類

H(k)は元walk、B(k)=Σ_{i=1}^k H(i)。供給の必要十分条件は source高さがtarget高さ-1、かつB(q)-B(t)-(q-t)H(t)=0。
fでは各blockの第一〜第四Aの始点高さは-2,-1,0,1。第一Aは全体floor-2のためfree。第二Aの必要sourceはfloor-2で、全区間の相対高さが非負かつ最後1なのでarea>0、free。第三Aは同じblock内のSAAが実供給する。第四Aはclockq_j=11+8j（0<=j<m）で高さ1/B0。
第四Aのsource高さ0の全候補はold0/B0、old2/B-1、各blockのS中間clock6+8l/B3と第三A clock10+8l/B-1で尽くす。source高さ0ではarea=Btarget-Bsourceなのでold0だけがarea0。従って第四Aはすべて唯一のold source0からactual。全tail actual=2m、free=4m-2m=2m。

## 新履歴の全sourceも尽くす

gの第一〜第四Aの始点高さは-1,0,1,2。第一Aはglobal floor-1でfree。第二Aはfloor+1なので上と同じ非負areaの理由でfree。第三Aは各block内のSAAでactual。
第四Aのclockはq'_j=10+8j、高さ2/B( q'_j )=5+8j。必要source高さ1の候補はold3（B0）、first block内5/9（ともにB3）、以後のperiodからq'_l+3/q'_l+7（B11+8l）で尽くす。old3からのareaは-2、5から-3、9から1。l<jの二種類もそれぞれ-3/1であり、どれも0でない。
この分類は選んだold witnessの消失だけを確認したものではなく、新しい全local/old源を含む。従って第四Aはすべて新free。新actual=m、free=3m、free増加は正確にm。

## Positiveと反証の量化範囲

元tailでは第一block S4が正不足を作り、第三/第四Aのactual2が不足を2まで下げる。各追加blockはS4/actual2で不足を2増やし、途中にも不足1以上を保つ。新tailは第一block S3/actual1で不足2、その後各S4/actual1で3増える。全非空prefixがactual-positiveである。
同じold BlockWord、削除1S、head4->3、幅4、ceiling4が固定のまま、free増加mは任意に大きい。従ってこれら固定量だけの任意有限上限を破る。E726 m1の違反を全てのmへ単に外挿せず、上の全clock/source分類が全量化の根拠。
最後はA-run内でgapj0、free>=2なのでC1 counterを作っていない。実C1 counterに追加のsource条件があれば別の費用上界が成立する可能性は残る。標準Recamán軌道への到達も主張しない。

## 新しい正不足原理と実供給輸送の境界

E722のpadded_first_S_height_one_positiveは、任意の元padded BlockWord/firstS/相対ceiling1で全relative actual-positiveを供給する。しかしsource輸送はglobal initial-Sから除く操作だけが確定している。上の両tailはpositiveを保ちながらold supplierを失うので、positive原理を満たしただけでold source保存を推定しない。
古いE707/E708のbalanced spliceとは異なる、一Sのunbalanced deletionである。次の有用な操作には、crossing old源のgain/lossを元source-height/area spectrumで同時計上し、counterのfree余裕から支払う義務がある。定義したloss/gainの式だけで進展にしない。

## 有限独立検算

m1..8をreverse literal全source、m9..24をforward key全sourceで検算し、全供給集合/自由数/両positive/ceilingに一致。worker CPU .031717+.033418=.065135秒、controller別。これは固定族の有限支持COMPUTEDでありfresh holdout/全m kernel証明ではない。sourcehash/argv/guard/停止receiptはdocs/data/depth_general_20261116/PADDED_FLUX_PROTOCOL.jsonとH04-flux-*に保存。数学worker日計2.178690CPU秒、宣言6秒以内。範囲を広げて枠を埋めない。
