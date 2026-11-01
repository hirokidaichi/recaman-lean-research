# 同じ全old prefixでfull-tailの問いを攻撃

- ID H-20261030-08 / R-20261030-01/H14、Status CONJECTURED（親命題）。sample methodはSTOPPED（事前CPU予算終了）。
- One question: H01最終S-sourceのfull-tail free>=Rそのものに、同じwhole old prefix/元0 zero/全positive/実targetとlocal窓を満たす反例があるか。E459のhead-onlyでは止めず、full actual freeを目的にする。新しいE461/E462/E463の源条件/数値pruningを使う小さいfalsifierで、旧r4大表/UNKNOWN/N32延長は再開しない。
- Discovery seed20261130: old語はBlockWord atom A/SAAA/SSAAAASAAAのランダム連結、whole mass3..12、len<=70。全old prefixを保持し、その内部tをランダム選択。target suffix C1..13、R5..8。全Aは[2R+2,min(29,R+16)]、T3..R+1、M/L/Uは残りを正に分配、s,v1..10。同じtarget suffix areaからm/hを整数として解き、m>=1/h>=1。ML>=RならA>=2R+3、ML<RならA<=R+12。future長<=64。最大200000 sample。
- Independent holdout seed20261131: whole mass13..28（discoveryとdisjoint）、len<=70、R9..13（disjoint）、他の事前範囲は同じ。独立後退literal実EndN、discoveryはforward累積mass/area。両方とも全old窓/元zero/全positive/targetold/localSとactual fullfreeを検査し、最初のfull反例なら停止。それ以外は最小marginと正確件数を保存し、sample passを証明と呼ばない。
- 数学CPU既使用0.513758秒。未使用4CPU総予算から追加各worker上限1CPU、cooperative0.8CPU/wall3秒を割当（2CPU最大、合計実測<=4）。single-Python/no-child契約はH06で当日検証済み。source/revision/dirty hash/argv/input仕様を実行前freezeする。CPU/件数終了は不完全sample、counter witness replayはfresh holdoutとは別。
- 受入: exact H01-domain counterexampleか、候補がどこで失敗するかのstrict情報。反例がなくてもH01はCONJECTURED。15分で追加情報がなく予算終了ならSTOP、同じworkerへ時間を足さず、source joint/free課金の紙上へ戻る。新しい定数修理なし。

## 07:08:11 結果 / 停止

Discovery119204sample/594整数P2/zero594/全positive582、C>5は113、wholemass>targetCは481。Holdout96430sample/24整数P2/全positive24、C>5は4、wholemass>targetCは24。全free<R反例0、最小marginは各5（R5/free10）/9（R9/free18）。両方0.8CPUのcooperative期限で停止し200000sample未完走、全領域の反例不在の証拠ではない。低頻度holdoutを網羅したと呼ばない。Status STOPPED（sample method予算終了）、親H01はCONJECTURED。

worker CPU discovery0.832447/holdout0.835327、合計1.667774、H06含む数学全実測2.181532CPU。controller/guard/Lean検証は別。source/argv/正確stdoutはH14-PREFLIGHT.json/H14-*.log/-result.json。source以前のold prefixを消さずに検査し、同じworkerの時間追加はしない。sample中のmarginを一様2R等の証明に昇格しない。
