# 深さ6/j4の長さ7内部窓に残る正確なprefix

2026-11-16、H-20261116-03。E724 PROVED-LEAN（個別512MB受理、全体checkは日末）。元padded BlockWord前史、全prefix正不足、深さ6、最後4Sの元actual counter、最後targetの元source n+2という範囲を保持する。d2/internal Win7がある明示枝で、source uの後9時計でgap開始bとなり、その前の元prefixはmass2/area-33。**内部Win7の存在を全counterへ仮定しない**。一般C1やj4 fullgapは未証明。

## 新しい厳密な幾何edge

基準rのsigned triangle slackを

    2 areaFromLevel + below(end)-below(start) +2 lowAweights
      -above(end)+above(start)

とする。任意元fの全区間で非負、区間分割で正確に加法的。元S atheight x>=r+1は4(x-r)-2>=2のslackを消費する。他の一歩は0で、highSのない区間はtriangle式の等号を満たす。
E681の内部Win resourceと左辺の差は、窓の前後二つのslackと、内部窓の2 lowAweightsの和に正確に一致する。従ってbudgetが飽和すると、内部窓の外にはrより高いSがない。この事実を元actual counterへ内部接続した点が新しい局所edge。一般恒等式だけをG側進展と数えない。

r=Fw(n)-2。元final source n+2のarea0と最後4Sが、n+2..bのr-area=-10を供給する。E670のW+8H<=36によりW<=36。内部source uの高さFn=r+2、Win7端点qはr+3、bはr+5。E681左辺は6+30-12+28=52、右辺は2W-20<=52となり完全に飽和する。窓外highSは0。q以後の高さはr+3からr+5へ上がるので、Sがなく2歩のAだけ、b=q+2=u+9。
内部7歩のr-areaは14、その後2Aのr-areaは9、suffix合計23。全体r-area-10から、n+2..uの元area=-33。開始高さrからsource高さr+2なのでmass2。元prefixを新しいBlockWordへ置き換えていない。prefixのrunKey=-72はこのmass/areaの紙上系で、全sourceやfreeの再分類が済んだという主張ではない。

## PAPERの追加source選択（E725、未Lean）
同じ元counterで高さFn+2のA qが**actualである枝**を取る。E714のd3 producerは元source xとx+3=qのSAA/H0を内部供給する。q-1は高さFn+1のAでH0からactual。全Win source vは高さFnなので、padded old prefixのstrict walk gapによりv<nは不可能、v>=n。
main r-areaをnから測ると、最初SSのr-area1を加え-9。start triangle6、W<=36なので元全resource<=60。q-1への任意source v>=nにE681を適用すると24+4k<=60、k<=9。既存mod4則k≡3 mod4からk3又7。k3なら外側SAAと同じclockがS/Aとなり矛盾、従ってk7。
外側SAAは内側7窓の末尾S,Aを供給するので既存SevenWindowPrefixFiveが語SASAASAを与える。この語の2文字目Aは初期SSの2文字目Sと矛盾するためv=nも不可能、v=n+1は高さFn-1から不可能。従ってv>=n+2の元Win7が**内部抽出**され、E724がb=v+9、prefixmass2/area-33を供給する。
これは完全PAPERの条件付きsource選択であり、最高Aがfreeの枝は未排除。prefixmass2/area-33の不存在も未証明。E725を深さ6 fullgapや一般化の新しい成功へ昇格しない。

## 実装停止と次の一問

H03-REDUCEは上記source選択の実装で、既存mod4の元Win輸送helperからkernel512MBに達した。初回でSTOPPED、修理0、全bytesはpacket .lean.txtだけ、Recaman/root/Audit未採用。資源・tactic・import・helper splitだけで再開しない。実測CPU .687946秒、未計測扱いではない。
E724のstrict slack/R-area-prefix証明は独立して受理され、failed helperをimportしない。再開には例えば新しい元source/areaによるk<=7のstrict削減など、停止した<=9 spectrumを回避する独立の数学入力が必要。

次の局所一問は、元old mass2 source spectrumとH0/窓外highS0を保ったまま、このprefixmass2/area-33の最初の高い実Aの源を排除できるか。全旧履歴/他mass/元prefixを保持し、旧r4同表や512MB jobを再実行しない。一般化を優先し、local上限を超えない。
