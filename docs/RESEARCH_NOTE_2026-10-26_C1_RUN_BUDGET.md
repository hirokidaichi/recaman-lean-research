# 2026-10-26 C1: run供給予算からfree-gapへ

## 結論と証拠範囲

E-408〜E-411/E-413/E-414はPROVED-LEAN。特にE-414はBlockWord全実prefixの後の**二A-run**尾部について、元0/pのzero/全positive不足と実target供給から`j+1<=先行実free数`を全長で供給した。
一般の三run以上、C1/Q/H/SL、r4分類は未解決。E-412のr4測定は削減0で方法STOPPED。E-415はlocal供給clock<=2/修理<=3という**補助案**の反例で、C1/free-gapの反例ではない。

## 平易にいうと何が進んだか

Aは加算、Sは減算。ここで「供給されたA」は、同じ研究の基点から過去を調べたときにP2窓があるAで、free Aはその窓がないA。後から基点を変えて数え直さない。
今日閉じたのは、加算が連続する区間が二つまでなら、次の供給Aを待つ直前に減算が何個続けられるかを、先行free A数で制限できる、という部分問題。
たとえば先行free Aが2個なら、そのS-gapは1個まで。既知の`SAAA | S4 A4 S A`はその等号例で、新しい反例として数えていない。

この範囲ではrunの長さもfree数も無制限でよい。有限の試行件数を増やした結果ではなく、形の条件の下での証明に変わった点が進展。
一方、加算区間が三つ以上になると別の古い窓を再利用でき、実際に供給clock4つの例がある。二runの小さい供給予算をそのまま帰納する道は使えない。
C1全体にはこの再利用を制御する新しい一般入力とrankが残るため、全体が何割完成したという数値は付けない。

## E-408〜E-414の依存chain

`P(v)=2area(v)-mass(v)(mass(v)+1)`はA appendで保存される。任意前置語uのsuffix vがA^r S^j後のP2を供給する必要十分条件は同じvの`mass(v)+r=j+1`かつ`P(v)=-2(j+1)^2`（E-408）。別suffixのmass/areaを混ぜない。
二A-runは全suffixを三源に分解し、平方因子から初期S長に依存しない鋭いrun長上界を得る（E-409）。
定符号run内のP=-2 suffixは高々1、同じsuffixは一つのA-ray clockを供給するため、全historyをR runで表せばA-only未来Kの実供給count<=R（E-410）。Sを挟んだ新しいA-runでsourceを再利用しないとは主張しない。

同じBlockWord prefixの全prefixでP>=-8、負massならP<=0（E-411）。二つのnested suffixで同じseparator profile値なら、S>=3ではmassが等しく、同じA-rayのold供給clockは高々1となる。start自体の重複は残す。元0の実Winへ接続し、自由old tagを仮定しない。
S-only separatorのsmall h0/1/2も別途old不可能を証明。local側の供給は第3Aだけなので、単一A-run供給count<=2、最初のAは非供給。E-407の2j+2<=全Aと合わせて単一runの全free-gapを閉じる（E-413）。

二A-runでは第2A-ray前のlocal Sh AM Smの供給は高々2。中A-runからのrootは1=m(m-2a),a>=1に反し、初/末Sから各一つだけ。共通oldは一つなので両A-runの実供給合計<=5（先行S>=3）。先行S<=2は全positive不足から実供給<=1。
既存r3 simulationの**新count射影**A<=2free+1を全3324行でkernel検証。r3分類やQを再実行して成果数に足したのではない。free<=3をこの新射影、free>=4を5供給予算で処理し、E-407と合成してE-414の全free数を得る。
全元0/相対positive/実zero/Int元pのstatementをG5で逐語監査。定義した結論PropやA<=2freeを入力にしない。

## E-415: 第三A-rayで小さいlocal定数は失敗

local語`v=S A^5 S^6 A^4 S^6`のA-rayにはclock2,4,5の三つがある。さらに
`v=S^10 A^24 S^21 A^3 S^4`にはclock2,3,9,11の四つがある。
`localSupply(v A^i)`はすべてtrue。独立なliteral-window replayが各始点/mass1/area0を記録し、後者の4clockはLeanでもdecide確認してAuditへ登録。
最初はlocal word countermodelとして発見し、その後literalな実EndNを全prefixで監査した。後者の`v A^12`は空BlockWord/元0のzeroと全正不足を満たし、第三A-run内の実供給clockも2/3/9/11（COMPUTED、詳細ledger保存）。Leanで確認したのは四clockのlocal判定であり、実historyのzero/positive監査は計算として区別する。最初の<=2案と一回の修理<=3案をREFUTEDとし、その小定数方法はSTOPPED。さらに定数だけを変える修理を続けない。
二A-runの証明で供給源を独立に数えすぎているのではなく、第三runで実際に新しい源が発生することを示す。

## E-416 PROVED-PAPER: 三A-run free-gapの残余はfree4〜9に限る

**全量化子。** 任意f:Nat→Bool、n,h,M,m,L,s,T,j:Nat、BlockWord wとする。seg f0n=w、以後の実符号はSh AM Sm AL Ss AT、長さB=h+M+m+L+s+T>0。全0<k<=Bで`cN(EndN f0) n k+1<=cN(S) n k`。続くj個はS、EndN f0(n+B+j)とする。同じ元0のtail内の全A数A、供給数E、非供給A数rを数える。各run長、総長、r,jに上限を置かない。

**完全な紙上chain。**

1. 最初の二A-run終了までをB2=h+M+m+Lとする。h+m>=3ならE-414のtwo_A_run_supply_budgetでその実供給E2<=5。h+m<=2なら、B2>0では全positive不足のk=B2とS count=h+mからE2+1<=2、B2=0ならE2=0。したがって全場合でE2<=5。E2は第3S-run中も増えない（SではEndN=false）。
2. 第三A-run開始までのtailの総S=h+m+s。これが<=2なら、全positive不足k=Bより全供給E<=1。target供給にE-407を適用すると2j+2<=A=E+r<=r+1、従ってj+1<=r。この場合に反例はない。
3. 総S>=3なら、同じBlockWord old prefixは第三A-run中に高々1供給（E-411）。local tail Sh AM Sm AL Ssは**5個の定符号run**で、E-410からlocal供給count<=5。zero長を含むrun列でもE-410は成立する。したがって第三A-run供給E3<=1+5=6。old/localの重複clockは和集合上界で数えるので、独立tagの実現可能性を仮定しない。
4. 実cN加法とS区間供給0により全E=E2+E3<=11。実A partitionからA=E+r<=r+11。
5. r<=3ならE-414内のpositive_r3_free_gap（一般tail/同じ元0、endpoint d1不要）をそのまま適用してj+1<=r。
6. r>=10ならA<=r+11<=2r+1。E-407の2j+2<=Aと合わせてj+1<=r。
7. 従ってfree-gapの反例があれば**4<=r<=9、A<=20、j<=9**。全S長/全word長はまだ無制限であり、これを有限history全分類やC1の証明と呼ばない。

元p版はf(i)=e(p+i)とendableCount/subtractionCount/nonsupplied_count_shiftでそのまま移る。元zeroと全positive不足はcN加法から上のrelative条件を供給する。一般rankや全A<=2rは仮定しない。
このreduction全体は**PROVED-PAPER（未Lean・人間レビュー未）**。引用した部品はPROVED-LEANだが、三run実count接着と残余結論はまだLean定理として登録していない。
11は既存run-budgetによる安全な上界であり、失敗したlocal<=2/3案をさらに修理して得た定数ではない。第三A-rayのlocal4反例を保持する。

## 有限検査と失敗

- H01: 二run discovery5000/holdout405、違反なし。一般仮説はCONJECTURED、直接方法STOPPED。
- E412: old-only credit付きr4 graph12837states/40024edges、射影削減0/0、16terminal不変。kernel<=3000 gate不通過。時間/メモリ追加なし。
- 三run actual target: discovery16384（positive14208/target7384）、独立holdout192（positive192/target28）。free-gapと「次供給可能ならA<=2r+1」に違反なしだが、両一般三run命題はCONJECTURED。known A10/r4 terminal対照は次供給0であり独立holdoutではない。
- local source discovery1048576組で3clock562/4clock2を発見。独立48 tuple holdoutは最大1（反例なしは受理根拠にならない）。発見反例のliteral再照合は独立実装だがfresh holdoutと呼ばない。

## 次の一問

三runの一般探索を繰り返さず、まずE416の実count接着/reductionをLeanへ移し、残余r4〜9/A<=20/j<=9で**次供給条件**がsourceの再利用を制限する新不等式を供給できるか。
古いr4大表の時間/メモリ追加、単なる範囲延長、全prefix線形上界（known A10/r4で偽）へ戻らない。
