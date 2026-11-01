# Run数別予算の派生検算

## 結論と位置づけ

PROVED-PAPER（未Lean・人間レビュー未）。[H-20261029-07](HYPOTHESIS_CARD_2026-10-29_RUN_COUNT_BUDGET.md)の領域で、k>=3個の非空A-runの実供給数は `E<=k(k+1)-1`。既存E410/E411/E416のcountを加えた派生評価で、新しい源再利用機構やC1証明ではない。四runではE<=19。四run free-gapの反例候補はfree4..17、全A<=36、j4..17に限るが、全S長とold prefixは依然無限である。

## 完全な紙上chain

1. `f:Nat->Bool`、`n:Nat`、`w:BlockWord`、`seg f 0 n=w` を固定する。全countは同じ `EndN f 0`。n以降は `S^h A^a1 S^s1 A^a2 ... S^s(k-1) A^ak`、k>=3、h>=0、全ai>=1、全si>=1、長さB。全0<t<=Bで相対正不足 `cN(EndN f 0)n t+1<=cN(S)n t` を仮定する。元p版では同じpのzeroと全positiveからcN加法でこの条件を供給する。pをnへ変更しない。
2. 最初の三runの末尾までの相対正不足は1の条件の制限。E416 `ThreeRunSupplyBudget.three_run_supply_budget` により、最初の三runの実供給数は11以下。第三separator以降をこの区間へ含めず、供給のendpointは左閉右開countに従う。
3. 第t A-run (t>=4) の直前のtail vを、初期Sとt-1組のA/Sから成る2t-1個の定符号blockへ分ける。初期h=0でも空blockを数えるだけで上界は保たれる。t-1>=3個の非空separatorがあるので `cntF v>=3`。全語は同じ `w++v` であり、wを別の自由tagへ置き換えない。
4. E411 `BlockOldRay.block_rayCount_append` は、このA-rayの実old供給clockを高々1に抑える。E410 `RunSupplyBudget.rayCount_runWord` はlocal供給clockを高々2t-1に抑える。`endable_A_run_count` が両方を同じ元0の実EndNへ接続する。old/localが同じclockに重なる場合はOR上界で過大計上するだけなので、実供給総数は高々2t。old sourceのmassやprefix長は切らない。
5. A-run間のS区間は符号falseなのでEndNを持たない。cN加法で互いに重ならない各A区間の実供給数を足す。従って
   `E <= 11 + sum_(t=4..k) 2t = k(k+1)-1`。
   k=3では和が空で11、k=4では11+8=19。一般kは11を基底として、末尾A-run追加で2(k+1)を足す帰納法で同じ式となる。
6. 次の実EndNがS^jの後にあるとする。B>0なのでE407 `PrefixMassBarrier.supplied_after_S_gap_half_bound` が `2j+2<=A` を供給する。実A数をA、実非供給A数をrとすれば、元0の実分割により `A=E+r`。将来のtarget自身をこのA/E/rへ数えない。
7. free-gapの反例 `r<j+1` がある場合、r<=3は既存 `BlockOldRay.positive_r3_free_gap` で排除される。r>=4。反例条件と6から `2r+2<=2j+2<=A<=r+k(k+1)-1`、故に `r<=k(k+1)-3`。更に `A<=2k(k+1)-4`、`j<=k(k+1)-3`。下限r>=4とr<=jからj>=4。

## 反証・境界pass

- k3の11とr4..9/A20/j9は既存E416と一致する。これはE451で三run全体を閉じた後に、その古い反例領域を再探索する指示ではない。
- k4/h0/s1=s2=s3=1では第四ray前のS数はちょうど3であり、old一時計の適用下限を満たす。h0が正不足と両立しない場合も、暗黙の追加h下限へ変えない。
- E415の第三ray local4clockはlocal上界5に含まれる。小定数2/3への修理はしない。
- allmass old sourceを残し、old/localのsupplier選択を独立に最適化して実在モデルと呼ばない。再使用はray間であり得るので、全rayでoldが1個という主張はしていない。
- 固定kでもS長/historyの上界は出していない。A36は「有限history全分類」ではなく、CPU大表再開の根拠にもならない。
- kが無制限では予算が二次に増え、free-gapに必要なfreeによる一様課金は未供給。この派生countだけで一般Q/C1を閉じない。

## C1への接続と残るedge

E451は三runに限った連続S-gap制約である。Qは完成設定Dの全対象clockで累積面積を評価し、Pと結合してold P2を排除する主張である。連続gapを抑えただけで、何度もS/Aを交互に通る全excursionの面積や単調rankを供給したわけではない。E451から一般Qへの完了したLean edgeはない。

次は四run old-targetを一つの機構テストとして、同じsource prefixのkey/massと実供給countを結合する。E452/E454が与える「local source以前のA>=j+1」をfreeへ直置換する案はE453で反証済み。源以前で不足するfreeを、その後の別区間で支払う必要がある。区間を重複計上しないsource依存の課金か、再使用できない源pairを示すことが次の有用なedge。上の二次予算を新しい単射やrankと呼ばない。

## 07:35 k4だけのkernel接続

一般kはPROVED-PAPERのまま。k4はE456 `FourRunSupplyBudget.four_run_supply_budget/four_run_free_gap_residual/four_run_bounds_int` で全長Lean化した。元pのzero/全positive/padded BlockWord prefixを実countへ接続。A区間は空も許可、三separatorは非空。数値残余の不在や四run free-gapの証明ではない。
