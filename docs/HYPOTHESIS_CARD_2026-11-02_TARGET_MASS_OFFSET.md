# H-20261102-07: 高mass target の separator差

Status: PROVED-LEAN（末尾の終了時判断を正本とする。以下は開始時の仮説・費用条件）。親R-20261102-01、H06後。07:00近傍開始、15分gate07:15。探索CPU追加0。

問い: 任意元Intp/padded BlockWord/元zero-fullpositive/正三run zero-mass head、同old targetmass C>=4、最終S長 v>=C+2 において、元full-tail actual free>=j+1を全C/v/全run長/全old履歴で導けるか。Cは同じtarget suffixの実Int massであり、他supplierのmassを切らない。面積帯、old有無、local band、headfree結論は入力しない。

提案chain: δ=v-Cにより同targetはT=R+δ。local6/old1を保持。δ2ならcounterはr3 actual countからR>=5、同target key下界はC3基準のS5以下なのでheadS>=10/headfree4。no-old last6で払い、old有りは同target順序でclock<=2/mass>=C+1>=5を内部供給しE497又はより強いE491へ。δ>=3ならcounterはheadfree r+δ<=6、r3 headS<=2r+1、R>=r+1。同target key式 ku=-kz-4CS-2C²+2δ²-2R² をC>=3の上界へ比較しH06の平方不等式機構へ。δ5/r1/S3境界も実SASASAを保持。

反証pass: C/vはInt/Nat差を区別しδ>=2を先に供給。old順序はj>=2をcounterから供給し、端点Aを勝手に仮定しない。headfreeは同じ元0/pのcountで、source以前freeへのE453反証済み置換をしない。一般CのBlockWord key上界をmass3の[-2,2]へ切らず下界-2だけを使う。

受入: 最初15分で新しいC>=4の一様不等式又はstrict候補削減。最終は実counter内部接着と元p adapter、-M512/lint/G5/Audit/fullcheck。一回数学修理後失敗ならSTOPPEDとして別source位置/非zerohead仮定監査へ。C3領域/旧表/既知三runを繰り返して進捗にしない。C1全体は未解決。

## 終了時判断

E-516 PROVED-LEAN、C>=4/v>=C+2。 全体検証・逐語audit・実績正本は11/02 DAILY/journalを参照。親C1全体は未解決。
