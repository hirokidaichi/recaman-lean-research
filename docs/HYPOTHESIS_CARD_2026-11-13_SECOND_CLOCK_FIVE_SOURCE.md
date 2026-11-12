# Hypothesis card: second-clock gap-five actual source

- ID H-20261113-01
- Status PROVED-LEAN (E701/E705/E706, individual512MB, Audit and full check passed; human review pending)
- Work state unstarted; secondary local-completion unit, at most 30 minutes
- Priority updated by user instruction 2026-11-12; main card H-20261113-02
- Owner Codex; created 2026-11-12
- Parent 11/12 DAILY final; nested-source-area note E701

## Bounded question and exact scope
任意元f:Nat→Bool/n,a,b/w。BlockWord w、seg f0n=w++A^a、n<b、元全n..bでFw n−6<=Fw i、全非空prefixでEndN0供給数+1<=S数、最後5S、元EndN0(b+5)、元free<=5。source n+2のWinはE697/E700と旧source fullgapから内部供給する（producer単体ではそのactual Win条件を明記して限定可能）。元高source d>=3はd*(k−1)+5H<=9を得られるか。Hは元区間n..bの高さ>=Fw n−4にある元free件数。d=Fw(source)−(Fw n−2)、kは当該Winの正長、対象A qはn<=q<b。全旧履歴/他supplier mass/源前prefixを保持、上excursion無制限。

## Acceptance
局所枠開始後15分で同元actual anchorから新source edge/strict候補削減/反例を判定し、総枠は30分以内。
一日の最初15分の一般化判定は[H-20261113-02](HYPOTHESIS_CARD_2026-11-13_DEPTH_INDEPENDENT_CHARGING.md)で行う。E681式自体の再証明、E701/H0/bandを新Prop入力したadapterは進展でない。d>=3 source窓を内部抽出→元n+2 area0/最後5S area15→duration+5H<=9をkernel化し、最高二AのactualとSAA衝突へ。個別512MB/10CPU/20wall、一修理だけ、lint/全check/Audit/逐語署名。探索worker予算0から。

## Connection to arbitrary depth

このstatementは深さ6/j5/source n+2に限定される。成功は局所側として保存し、単独では
一般化側の進展にしない。独立した任意Dの新辺も得た場合だけ、その署名・元actual仮定・
重複請求/境界補正と次のconsumerを別に示す。PAPERからLeanへの昇格だけで一般化の停滞をリセットしない。

## Falsifier and boundaries
旧sourceとn/n+1を元高さで除外。d2を含めない。H1/d3/k3は11>9、H0/d4/k3は8<=9なので単体では残り二実sourceが必要。k7/d3は18>9。u=n+2境界を残す。元prefixをBlockWordへresetしない。E701は未Lean/人間レビュー未、一般深さ/C1未。

## Stop and allocation

局所枠の15分で新edge/strict削減がなければ同実装を延長せず、残り15分は必要仮定/署名の監査又は別局所候補へ。
30分を超えて一般化枠を借りない。H-20261113-02の別機構へ続け、unit停止で日次を終えない。
j4残余でd2/k7境界を消さず、H49/Rの二修理禁止・採用外、H21/H25/H30/H32と過去全STOPを継承する。
資源/tactic/import/splitだけの再開は不可。11/12の旧局所無変化0という実績は保持するが、
新設一般化指標の過去値に転用しない。旧r4二回0/0停止は別保持。

## 2026-11-13 local unit: new producer
局所開始06:35:53（最初一般化実28分06秒、余剰1分54秒を後半一般化へ移し総60分維持。以前checkpointの27分52秒は概算で確定phase値ではない）。局所上限07:05:53。
H01-Pはr=r+0のglobal rewrite誤り、一回だけH01-P-Rで局所元source n+2から高sourceのduration+5H<=9を個別512MB受理。初期二時計を高さで除き、area anchorを内部供給。H0や結論を仮定しない。これは旧H49/Rを追加修理したものではない。新budget9を使う独立classification subunitを開始し、全高実窓k3/H0/d<=4を受入に固定。

## Local result
H01-P/R producer、独立H01-S classification、H01-C collision、H01-F/R全source consumerを512MBで個別受理。H01-Fの一修理はdestructで消えるheを保存するもの。新bound9でstrict pruning後の新bytesであり旧H49/R不採用を維持。lint全substantive。E701の未証明仮定を入力していない。root/Audit/G5を登録し、日末全check待ち。局所枠残余は固定深さj4探索に自動使用せず一般化へ再配分する。
