# 10/30: 四run old targetと最終S源

R-20261030-01/H01、初回gateは06:03:13〜06:18:13。数学CPU探索0。元のfull-tail free-gapはCONJECTURED。既存E452の単なるA>=R代入は成果にしない。

## 提案: 交差項を残した新target予算

固定u:非空BlockWord、C=massu>=1、R=j+1、tail `Sh AM Sm AL Ss AU Sv AT Sj`。全M,m,L,s,U,v>=1（T>=0）、old targetのmass1/area0。H=M+L+U、A=H+T、Q=h+m+s+v、I=M(m+s+v)+L(s+v)+U v。

runKeyの連結則から、同じold suffixに対する厳密identityは
`2area(u)+C(C-1)=2A(A-2R)-4I`。
BlockWord下界から`C²+2I<=A(A-2R)+1`。最終separatorのlocal源はSq AiのP2なのでq1/i2。final bandならT<=j+2=R+1。

このときI>=H+2M+L>=H+3。A<=2Rなら右辺<=1でC²+2I>=7と矛盾。A=2R+1ならH=A-T>=R、左辺>=2R+7、右辺2R+2と矛盾。従って **A>=2R+2**。自由なfreeへの置換なし。E456と実A=supply+freeを結ぶと、この部分枝の反例はfree4..15/A34/j15へ縮む（形式化前は候補）。S長/old historyの全包含や反例不在はまだ出していない。

## 反証/境界pass（形式化前）

- j0/1は上のR>=1だけの議論で扱える。T<jを切っていない。
- E453の源12はAであり、本unitの最終S源ではない。反証済みhelperを再修理しない。
- 条件T<=R+1を落とせない: 全R>=6でu=A、h5/M1/m(R-5)/L1/s1/U1/v1/T(2R-2)/j(R-1)はraw P2の候補でA=2R+1。Tはband外。これは実free/C1反例とは主張しない。
- +2のsharp raw対照候補: u=AA、h5/M1/m1/L1/s1/U3/v1/T5/j3、R4/A10。両窓はtarget mass1/area0と最終S A2、T=j+2の境界。old mass1に勝手に固定しない。
- 空oldやゼロhead Aは意図したold/genuine領域の外。どこで正性を使ったか残す。高mass他supplierは切らない。

## 最小未知edge

今回の候補はsame-source key/areaによるstrict必要条件。実free-gapへの未知edgeはまだsource前/後の供給を重複なく課金すること。数値領域削減だけでC1を閉じない。紙上chainとfalsifierを固定してから、同じ量化子のLeanへ移す。新Leanはlint/G5/Audit/check、per-process10CPU/512MB/20wall validation（tree累積上限ではない）。

## H01 gate / H02 scope decision

06:07:06にraw +2 budget、06:09:55に同じ元0の実old/local窓の接続をkernel確認。最初15分gateは新しいstrict必要条件で通過。仮説free-gap全体は未解決。

H02でword/countの19予算残余15へのprojectionを同じsourceへ追加すると512MB kernel memoryで失敗。未検証combined sourceはpacketの.lean.txtへ隔離し、単体確認済みのarea/source moduleへ戻した。同じcombined jobへ時間/メモリを足さず、そのレイアウトはSTOPPED。残余free4..15/A34/j15は既存E456と新しい+2 boundの完全な紙上corollaryで、ここではPROVED-PAPER、未Lean。次は直前A源の除外という独立した数学的pruningにより供給予算そのものを小さくする。定数の盲目的修理や旧H06/旧r4 job再開ではない。

検証記録: 初回full checkはG5問3のyes/no回答欠落で拒否された。逐語statementを変えず、回答を明示して再検査する。誤って旧packetへ保存した当日check3ファイルは新規ファイルだけ当日packetへ移動し、旧記録は改変していない。

## 最終的な同日更新（上の途中数値を置換する現在の判断）

E458の新しい直前A源pruningは実供給17を供給し、同sourceの13残余を元pへ接着。E461 small-MLは最後band clock2だけから供給13/残余9、E462 large-MLは同じold mass1 parityを使い+3全Aとし、合成したH01最終S源全域は反例必要条件free4..12/A29/j12。いずれも不在は未証明。

E459はS-sourceでもhead-only free課金を反証。全tail17を保持する実例なのでH01/C1反例ではない。H14 full-tail small falsifier反例0やH15 charge random反例0は有限sampleに過ぎず、同workerの時間追加はSTOP。既知terminal seedへsource二次式を適用し、E464で固定headの全長四run族charge3/free-gapまで証明した。一般four-run charge3は未証明。

E463のtarget mass/幅はNat相対positive coreだけがkernel済みで、追加p adapter combinedは512MB STOP。E464の別命題（固定族free-gap）のIntp adapterはkernel済みであり、両者を混同しない。E465のmoment oldclockとE466のlocal反例、E467の未Lean二caseは別ノートを正本にする。

作業手順ミス: H10境界制御の下書き生成で未完了placeholderを一度書き込んだ。直後にその未証明部を採用sourceから除去してから検証し、後で完全な通常証明として書き直した。採用source/検証対象frozen bytes/axiom監査に残っていない。禁止placeholderを一時的にも生成しないという手順を守れなかった点を記録する。
