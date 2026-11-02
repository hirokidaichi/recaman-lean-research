# H-20261103-06: mass5/最終S1のfullgapと初期run供給の幾何

Status: PROVED-LEAN (E-527, individual/G5/Audit/full check PASS 648jobs/3420 declarations, human review pending)、親R-20261103-01。局所探索unit（source budgetの条件を比較）、最初15分gate、数学探索CPU0。個別-M512/10CPU per-process/20wall、数学修理一回。全体gapは当該枝だけ、一般C1ではない。

Exact question: 元Intp/padded/zero-fullpositive/正三run zerohead/同old targetmass5/最終S1の全T,j/全old履歴でactual fulltail free>=R=j+1を導けるか。E525のcounterはR5..8/S<=16/S>10/M<=R+1、weighted prefixでW=M+Lに対し2S<=W+2R+9、2S<=W+23、K=M(m+s)+Ls>=W+M、same target circle R²+33+2K<=(S-5)²。これらを内部供給し、数値上限/未知Prop/headfree/target-Aを入力しない。

新source入力の提案: M<=2なら第一A供給0（既存first_two_A_not_supplied）、第二A<=3/第三A<=5と正不足のsmallS境界でhead<=8。M=3,m=1なら第二rayの初期S源は(q+1)^2=7を要して不可能、localはclock2のみ・old<=1なのでhead<=8。2M<=h+3ならnegative mass barrierで第一runの実供給clockは2だけ（i0/1は既存free、i>=2は元prefixのmanyS iff）になりhead<=9。全oldmassを保持し、単にsourceを消したtagを仮定しない。

紙上chain: M<=2又は(M3,m1)のhead8はS<=R+7。weighted/KからR²-4R-8<=S²-14Sだが右辺<=R²-49で41<=4R、R8に反する。M3,m>=2はK>=W+6、head9で50<=6R、R8に反する。

M>=4では幾何が2M<=h+3を内部供給する。もしnotlongならq=m+s>=2、2M+q>=S+4。q2ではK>=S+3、M<=R+1からS<=2R、circleとS16から56<=3S(S-16)<=0。q>=3では(M-1)(q-2)>=3によりK>=2M+q+2>=S+6、S<=R+9とcircleから101<=6S<=96。したがってlong条件が必要。head9とweighted/Kは46<=6Rを要してR8を強制。R8のcircle/K3/S16からS16、weightedlastからW>=9、M4からK>=13、一方circleはK<=12で矛盾する。

反証: WinとEndNを同一視しない。既存E524のendpoint補完は今回の実source削減に必要な箇所だけ消費し、現在A符号を仮定しない。long barrierには明示2M<=h+3を実counterから先に供給。q2とq>=3を分け、平方比較は正符号で行う。M3/m1の平方7非成立は整数偶奇/隣接平方で監査し、定数を当てはめたfinite head列挙へ置換しない。初期Sが短い境界h+m<3は実positive countで処理してold1を無断適用しない。

受入は新actual head8/long-first9供給とstrict candidate削減又は全gap、G5/Audit/fullcheck。最初15分でsource edgeなしなら当該method STOPPED、残時間はmass4のsource平方とprefix joint-old constraintsへ。旧表/H06/largeUNKNOWNへの資源追加や単なるsplit/import移動をしない。全run/rank/C1/全射性は未解決。

06:56 result: full Nat0/Intp actual gap checked under -j1 -M512, no area/local-band/endpoint-A/free hypothesis added. Accepted sharp scalar chain is quoted in E-527 audit; the preliminary margins above are superseded, not new assumptions. Source edge passed within first15min. Initial compilation failures were tactic availability, polynomial normalization and alias/cast normalization; no mathematical constant/hypothesis was repaired and no resource cap was increased. Math exploration CPU remains0.

06:57 semantic audit: tiny-S prefix uses actual positive deficit, all old masses retained, no target A required. Registry check first failed because CURRENT_FRONTIER lacked E527 reference; synchronized then full check PASS. No Lean gate disabled. Combined with E525/E526, short counters C>=5 are absent in this explicit zerohead/same-old-target family; formal combined coverage is not counted as a new edge.
