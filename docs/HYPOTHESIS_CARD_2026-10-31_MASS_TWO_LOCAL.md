# H-20261031-14: mass2九群のv1/2局所予算3/4

Status PROVED-LEAN、R-20261031-01活用。H13でactual counterから供給したS/B三対を使い、v1/T4ではlocal<=3、v2/T5ではlocal<=4を全head/run長と同じsourceから供給できるか。v3/T6はまだ別残余として保持。

新pruning: 第一A源のmass/keyと同じzero-mass head momentから B-h²+v²-1=2(v+1-i)(S-h+v)。v1/T4のi1/3は(h-1)²=2S+26/27又は(h+1)²=6S+30/31となりS12..14で非平方。v2/T5のi1/3/4も同じS/B三対で27/28、79/84/87、108/115/120の非平方へ。よってfirstAも0/2。v1第二Aはclock2、thirdSは0/2、initialS v1なし/v2clock0。v1はbaseline0/2+middleS1=3、v2はbaseline0/2+middleS1+secondA1=4。

sourceAtは具体word mass/key/非空kであり自由tagではない。parameter三対/全last old排除/実headfree4はH13/既存r3から元counter内で供給し、仮定として元C1を包装しない。新CPU探索0、10CPU/512MB/20wall。非平方の境界を紙上反証passで確認し、目標mass2全域やv3不在へ未検証昇格しない。

## 日次の保存判断（保存時の監査）
E477
親cycleはR-20261031-01のみ。実時計/commands/CPU/変更sourceの正本は当日DAILY、journal、`data/ten_head_20261031/SOURCE_VALIDATION_INDEX.json`と`CPU_SUMMARY.json`。元0/pと全old prefixを維持。
当card IDで確認された閉区間 1 件、合計 298.944 秒（他unit/親cycleへ二重加算しない）。個別start/end/unit/phaseはjournalの同IDを参照。open区間を含めない。
