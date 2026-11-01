# H-20261102-04: mass3/S1-S2の前二source族排除

Status: PROVED-LEAN（末尾の終了時判断を正本とする。以下は開始時の仮説・費用条件）。親R-20261102-01、局所探索25分（06:30近傍〜06:55目安）、初回15分gate06:45。CPU追加探索0。完了したS3/S4を反復しない。

対象: 任意元p/padded BlockWord/zero-fullpositive/正三A-run zerohead/同old targetmass3、最終S長v=1又は2、全run長/T,j。第一問はcounterからR=j+1>=5/M<=R+1を内部供給し、最後A-rayの初期Sと第一Aからのlocal供給が全clockでないことを証明できるか。次の判定を変えるstrict source削減を受入とし、fullgapの未証明を隠さない。

chain（形式化前）: targetkey ku=-kz-12(S+v)+2v²-2R²、T+2=v+j。key下界とword key下界からS>=R+3（v<=4）を得てr3 countによりcounter R5を供給。第一A予算は元first供給2とcounterからM<=R+1。初期S sourceはd+i=v+1、ku=2+4(d-3)(S+v)-2d²-2R²、v<=2ではkey>=-2に反する。第一A sourceは2dA²=2R²+ku+12v-2v²-2+4(i+2-v)S+2(i-1)²、dA<=Rと矛盾。両族除去後のlocalはS1で第二S+0/2の3、S2で第二S/第二A+0/2の4。

同old targetとT<=j、R5からE441が全old sourceも排除する。headfree4だけと上local boundではfullgapに1不足するため、これを解決とは呼ばない。source-cut M>=R又は共有clockの衝突で残余を縮めるのが次のedge。

反証pass: v=0や空A源を追加しない。S3/S4で残るfirstA0/1を今回の排除へ混ぜない。M<=R+1をcounterから供給せず無条件firstA排除にしない。旧M11/firstAclock3は対象のv/Rbudget外。old/firstAの自由tagを作らない。低mass結合は同じtargetに限り、他mass源や源以前prefixは保持。

受入: raw全長排除とactual元pからの内部仮定供給、又は明示反例/strict削減。個別-M512/10CPU per-process/20wallとG5/Audit/全check。進まなければ別機構のcommon-prefix/source再使用課金へ、同じtuple/tableのCPU増加をしない。数学修理一回。全四run/C1/rank/全射性はCONJECTUREDを保持。

## 06:36 継続ゲートと次のbounded edge（未形式化時点）

前二source全clock排除、old無しの内部供給、actual counterのheadfree4/fullfree=j/last飽和v+2/S10..14を個別-M512で供給。fullgap不在はまだ示していない。次は同じcritical counterから第二S sourceが少なくとも一つ必要であることを飽和countから抽出し、E452の実A-before-source cutでM>=Rを供給する。Mはfreeではない。headfree4とfirst供給2からM<=6、従ってR5..6へ。15分gateはこの新edgeに対し06:51、変化がなければsource-reuseの別機構へ。

反証pass: sourceが第二Aや第三Sである可能性を消さず、第二Sの不在時だけ残りの合計がv+1となることを使う。source以前free>=Rへの直置換（E453反例）は使わない。i<Tと同targetのT<=jを保持し、別prefixのold signatureを混ぜない。

## 06:39 S1次の最弱edge（形式化前）

Mcutをactualで供給した。S1の飽和local3では第三S-source clock0が必須（それが無ければ第二S+clock2だけで2）。この源のmass/keyはq2/U4を強制しs>=2。criticalのM>=R、headfree4→M<=6とR5からM5/6・R5/6、S10..14を得る。targetkey[-2,2]とhead momentは五tupleへ縮約できる見込み:
(S,M,R,m,s)=(12,5,5,1,2),(13,6,5,2,2),(14,5,6,3,2),(14,5,6,1,3),(14,6,6,1,3)。各tupleの第二S源keyはq<=mの全候補で成立しない。これが通ればS1 fullgap。S2を同時に解決したとは呼ばない。

反証: 第三S源q2/U4をsource無しで仮定しない。Mはfreeではなく元A count cutだけ。五tupleは全counter条件から内部供給し、未知finite-certificate Propを作らない。q=0はsourceでないので入れず、q=mの境界を含める。既知U4以外の履歴はcounterでなくても存在し、その全域を切らない。新しい代数的pruningに基づく小分類であり旧表の時間追加ではない。数学修理一回、失敗時はS2/source-reuseの別入力へ。

06:42 H06五tupleのmonolithic20分岐omegaは200k heartbeat/512MBで失敗。上限を増やさない。一回修理は独立のI>=2S+M-8とR5からS>=12を先に供給し、pure scalar helperの12分岐を明示Or constructorへ分ける。同じstatementの数学的pruningと測定改善でありimport移動ではない。これも失敗したら当該kernel方法をSTOPPEDとしてsource隔離、S1主張はCONJECTUREDを保持する。

06:45 H06 kernel方法は一回修理後も整数Orの自動解決で失敗したためSTOPPED。五tuple案は未採用、sourceはpacketへ隔離、上限追加/通常build/compiled移動で採用しない。U4補助も最終依存に不要なのでpacket保存に留める。次はH-20261102-05の独立したsource-prefix二乗恒等式へ切替。S1/S2 fullgapは引き続きCONJECTURED。

## 終了時判断

E-514 PROVED-LEAN。五tuple methodだけSTOPPED、独立prefix-squareで親限定域を完了。 全体検証・逐語audit・実績正本は11/02 DAILY/journalを参照。親C1全体は未解決。
