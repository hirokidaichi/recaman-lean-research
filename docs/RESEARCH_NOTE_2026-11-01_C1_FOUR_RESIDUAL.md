# 2026-11-01 D4/early source: 残るS13とjoint予算

最終状態: E497によりS13を含むD>=4/headfree5はPROVED-LEANで完了。E495一般I25 joint4は未Leanのまま。E484/E485 full-gapは独立E498/E499でkernelへ接着済み。途中の「S13未供給」は時点記録であり現行状態ではない。

E-493/E-494は個別512MB検査済み、全check同期中。E-495の全D4 headfree5はPROVED-PAPER（未Lean・人間レビュー未）。一般full-tail gap/C1とは別。

E493: I<=9、M>=2で第三初期S源なら(q+m+s)^2=2I+1、Q>=3/Q<=4からI4だがI>=2(m+s)+Ls>=5。第一A例外はI12、中央S例外L4/s1/m>=2はI>=10で不可能。全第三源がclock2へ合流し1。第二の非2例外M4/m1はL>=3と共存するとI>=11なので第二も1。M1の場合はfirst actual<=1と既存joint3、M>=2はfirst<=2/joint2で、一般actual予算min(M,2)+第二local+第三local+old2からhead実供給6。

E494: 同じ元Intp/padded/zero-positiveの実old supplier D>=4/clock<=2から同keyとI>=3でS>=11。S11はI<=9/head6、S12はI<=16/head7、S14はI<=34/head9、S>=15はhead10なのでheadfree5。S13は出力disjunctionに残す。S13を除去したと書かない。

E495紙上chain: I<=25の第二非clock2源はQ=q+m、Q²=2Mm+1、M+i=Q+1、i<L。I>=Mm+M+Lかつi<LからQ<=6、偶奇でQ3又は5。Mm4/12とq>=1,i>=0から(M,m,i)=(4,1,0)/(6,2,0)/(3,4,3)だけ（clock2と重なるM2/m2、M4/m3は数えない）。第二に2clockあれば、それぞれL>=3/3/4。

この三形でI25を使うと第三initial S源はQ>=6/Q<=7とI24が衝突する。M4/m1ではL3..4が必要だが4+(4+L)s=24を満たさず、M6/m2はQ>=8で即矛盾、M3/m4はL4..5/s1とI24が矛盾。第一A源はM4/m1でs1..3、M6/m2及びM3/m4でs1へ縮約し、source keyと非負clockに解無し。中央Sは0/2に限る。従って第三local<=2、第二<=2。これ以外は第二<=1/第三<=3でjoint<=4。元actual予算からhead<=8。E494の残余S13でI<=25を同sourceから内部供給すればheadfree5。

停止: InversionTwentyFiveのmonolithic/export kernelは512MBで失敗。16個のcross-product分類を一つの固定clockへ数学的pruningする一回repairも同上限で失敗。sourceはpacketの`.lean.txt`に隔離、Recaman/root/Auditから除去、通常buildやcompiled import移動で採用しない。このPAPER chainをkernel証拠に数えない。再開にはS13固有の独立数学的pruning又は小さく完全なcertificateと測定改善が必要。

次の独立pruning候補: 実source D=4/S13ならblock_mass_fourからsource keyは-2..6、同じclock二次式からIは23..25へ狭まる。M+L<=12もactual zerohead/U>=1から来る。これを先に内部供給してI25全域より小さなsource条件を評価する。元D>=4でD>4ならE491 headfree6が既存供給なのでD=4だけを対象にする。有限六prefixの反例不在だけで全prefixへ上げない。

## 07:28 更新: S13固有pruningで元headfreeを供給

E496 PROVED-LEAN: 同じ実source D4/S13からI23..25（oldkey -2..6）を内部供給。E497 PROVED-LEAN（個別512MB、全check同期中）: zerohead/U>=1からM+L<=12。この新しいactual条件で第二に2clockがあれば六形(4,1,6,2)/(4,1,3,3)/(6,2,5,1)/(6,2,6,1)/(3,4,8,1)/(3,4,9,1)。Q>=6ならMm>=18かつM+L>=8でI>=26になる費用不等式を先に使いQ3/5へ。単なる旧I25 sourceの分割ではない。

各六形の第三initial-S/first-A/middle-S源を実mass/keyで排除し、全h/Kでclock2だけ。sixShapesという有限patternはraw局所lemmaの明示仮定だが、actual結論ではsecond_non_two_shapeが同じ実wordから内部供給する。それ以外第二1/第三3でjoint4。元actual予算からhead8、S13なのでfree5。D>=5はE491のより強いfree6で払い、D4全Sのheadfree5を元pで供給済み。

一般I25全域のE495 joint4はこのkernel結果からは主張しない。STOPPED sourceは隔離を維持。六形factorとsource補題で大きいOrをomegaに直接証明させた初稿は512MBで失敗したが、同じ数式/同じ仮定のexplicit constructor proofを同512MBで検査し採用。資源上限変更/compiled移動なし。このproof構成の差は実測logで確認でき、数式上の反例修理ではない。

E497はheadfreeの前向き供給。E484 mass3/S3/old0 fullgapのPAPERがLeanへ完了した意味ではない。新headfree5からcounter R>=6、同target/oldareaからR6と四SB、M<=7、第一A local源の0/2衝突とlast供給4を元full-tailへ接着する義務が残る。既知firstA clock3 positive例はheadfree12でcounter外、黙って削除しない。
