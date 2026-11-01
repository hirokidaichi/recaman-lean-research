# Hypothesis card: 実履歴のsurplusと次供給条件

- ID: H-20261027-02
- Status: CONJECTURED
- Parent: R-20261027-01 / E-416。Mode: 局所探索（新しいcharge候補）、最初15分gate。

## 一問・全量化子

元0/pの同じ実EndN、BlockWord全prefix w後の三A-run Sh AM Sm AL Ss AT、元zero/全positive不足とする。
A=tailの全A、E=tailの実供給A、r=tailの実free A。charge C=A-2r=2E-A。
候補V1: 全run長/free数でC<=2、かつC=2なら任意S-gap j後に実供給Aを置けない。
後者はfuture自由tagでなく、本当のEndNを要求。『次供給ありならA<=2r+1』を導く十分条件で、E416/親C1の結論を入力にしない。
既知A10/r4 terminalはC2の等号controlで、unconditional C<=1の反例を新成果と呼ばない。
三run反例と一般run反例、V1の反例と親free-gapの反例を区別する。

## 価値と紙上chain

AごとにCは供給なら+1、freeなら-1。Sでは変わらないので、源の再使用がCを増やせるのはどこかを全historyで同時に照合する。
C<=2かつ等号terminalなら、次供給時はA<=2r+1、E407の2j+2<=Aからfree-gap。
最弱edgeは実P2窓がCの大きい状態で同時に成立できるか。各窓を別のold代表にして供給しない。
E415のlocal定数<=2/修理<=3は停止済みのまま。これはlocal定数の追加修理ではなく、実freeへの課金と次供給可能性を結ぶ別の対象。

## 反証・受入・停止

紙上境界: B0除外、zero run、C2 known terminal、free3/4、local/oldの同clock重複。
弱化tagモデルはCをいくらでも増やせるので、実元基点の全P2 ledgerで反証する。
受入: cutoff非依存charge入力/残余候補の実削減、または元zero/全positive不足の全EndN ledger付き反例。
15分で一般edge/実反例/候補削減なしならcharge方法STOPPED、命題CONJECTUREDとして共通prefix十分条件の別passへ切替。単なる探索範囲拡張なし。
数学的修理1回まで。CPU探索0から、必要なら契約/予算/argv/source hash/discoveryと独立holdoutを固定して再配分する。

## 06:12 probe判定と切替

discovery203125組（positive177775）、独立holdout252（positive252）でV1/親gapの違反0。ただしdiscoveryのC最大1、fresh holdout最大-9で、C2の本質的境界にはknown terminal対照しか入っていない。このprobeをV1の有力な根拠とせず、範囲拡張はしない。命題CONJECTURED、有限probe方法STOPPED。
worker CPU4.306000秒、guard1.124193秒、controller別計上。次は共通prefixの実供給位置から第一runのcharge<=0/二runのcharge<=1を供給できるか。local定数の修理は行わない。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-02/explore/charge-terminal-input: 3分59.322秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
