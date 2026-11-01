# H-20261102-10: mass>=2 の strict source-prefix A cut

Status: PROVED-LEAN（末尾の終了時判断を正本とする。以下は開始時の仮説・費用条件）。07:19開始、15分gate07:34。親R-20261102-01。探索CPU0。

問い: 任意共通BlockWord suffix u、任意混合prefix b/suffix x、同local P2 at i/同old target P2 at T+j、j>=2/T<=i+j、mass u>=2から、j+1+(i+j-T)+1<=ones bを導けるか。AS pair/cross>=4/zerohead/run数/area帯/actual free結論を入力しない。actual元0/Intpへのsource接着も同じsourceを保持する。

chain: E460の二source恒等式、全word cross>=0、BlockWord key>=-2。C=mass u>=2、R=j+1>=3、K=i+j-T>=0、X=ones b-KとするとX²>=R²+C²-2、mass bridgeでX+C=cntF b>=0。X負ならX²<=C²でR²>=9に矛盾。X>=0でX<=RならC²>=4に矛盾。X>Rがstrict A cutを供給する。

反証pass: 既知E453のR5/prefixA5/free4はtarget suffix mass1で、新しいC>=2仮定の必要性を示す境界。Cを1へ緩めず、A-prefixをfreeへ置換しない。Kの非負はbandから内部変換。old source前のprefix/高massを切らない。全sourceの単射やfree-rankではない。

受入: 同じ二窓/sourceを保つ一様不等式とactual splice/元p adapter、512MB/10CPU per-process/20wall/G5/Audit/fullcheck。最初15分で供給edgeが無ければSTOPPED、残時間は既存結果の独立意味監査。数学修理一回、資源追加なし。四run全体/C1未解決。

## 終了時判断

E-519 PROVED-LEAN、全mixed source/mass>=2 strict A cut。free cutではない。 全体検証・逐語audit・実績正本は11/02 DAILY/journalを参照。親C1全体は未解決。
