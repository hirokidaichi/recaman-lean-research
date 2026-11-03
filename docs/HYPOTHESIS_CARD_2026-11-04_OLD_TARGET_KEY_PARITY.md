# H-20261104-09: mass2 target / oldmass3 sourceの一様R偶奇

Owner Codex。Parent R-20261104-01。Status CONJECTURED、work active。探索CPU0、最初15分gate、数学修理1回。

Exact domain: 同zerohead/同old targetmass2/同prefix old suppliermass3、最終v>=1の任意run長・任意履歴。R=j+1が奇数の実二source共存をprimitive key spectrumとhead parityで排除できるか。v3/4や四候補を仮定せず、R/headfree/結論を入力しない。まず具体語のkey/質量恒等式、次にactual counterへ接着する。

新数学chain: E=S+v、target key ku in{-2,0}、old3 key ks in{-2,0,2}、同prefixの(-2,-2) pairは非共存。sourceはks=2E-2+4Zとなる（S²-Sとv²-vの偶数性、実head cross保持）、二source差ku-ks=4E+2-2R²。R oddならR²=8Q+1、従って差4E-16Q。ku/ks六組では差0又は-4だけ。差0のku=ks=0はE divisible4だがksの偶奇に矛盾、差-4のku=-2/ks2はE=4Q-1でks偶奇に矛盾。残る(-2,-2) pairは同prefixで排除済み。R odd不可能を全vで供給できればH08とは独立のstrict pruningとなる。

Falsifier: S² parityは定理として供給し数値観察で済ませない。mass2/3 primitive key以外のoldmassを切らない。(-2,-2) pairの禁止は同prefix由来を必須にし、独立mass/area modelでは結論を主張しない。K/headfree/tableを入力しない。

受入: 明示整数恒等式と具体語keyからR odd排除、可能なら元actual same-target edge。H08の四tuple jobはSTOPPEDのまま。新parity edge受理前に四tuple classifierを分割/importして再開しない。Lean-j1-M512/per-process10CPU/wall20、受理時のCPU/wallを測定。capなら新方法もSTOPPED、別mass1 mechanismへ。

## Gate result

06:52:55 raw two-word theorem、06:53:25 actual Win transportが同-M512受理。新source edgeは全vのR evenであり、H08の四tuple分類とは独立。raw0.860wall/0.748986CPU、actual0.491wall/0.340225CPU。H08 classifierは未検証のままSTOPPED、再実行なし。E544として全checkへ。

## 当日最終判断（2026-11-04）

PROVED-LEAN E544。source R偶数、fullgapでない。
完全な実時計・commands・失敗receipt・次の入口は[DAILY](RESEARCH_HANDOFF_2026-11-04_DAILY.md)と当日packetを参照。
