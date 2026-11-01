# H-20261031-10: 最終S長1/2のmoment local予算4/5

Status PROVED-LEAN、R-20261031-01活用unit。任意正整数三A-run head z=Sh AM Sm AL Ss AU、mass0、S=cntFz>=3、area=-B、4S+6<=B<=6S+4、全KについてrayCount(z S)K<=4およびrayCount(z SS)K<=5を問う。old target/R/S16を入力せず全S/Kを量化する。

新しい数学的pruning: 初期Sをd個除いたsourceのmass/keyからd+i=v+1、B=2d(S+v)-d²-v²+1。v1はmoment下端と両立せず初期S源ゼロ、v2はi0/B6Sのみ、v3はi1/B6S+1のみ（S>=3）。第三S sourceはv1..3でclock0/2。v1の第二A sourceはE472でclock2。したがってv1はclock0/2の2枠+firstA1+middleS1=4、v2はclock0/2の2枠+firstA1+middleS1+secondA1=5。各source族1は既存constant_run_root_uniqueで供給し、重複を二重計上しない。

反証pass: e0は実sourceに含めない。S12/C2/v3 raw境界は依然残す。v2初期Sのclock0と第三Sclock0を別々の2供給に数えない。Kや各runに有限上限を置かず、COMPUTED local3を仮定しない。CPU探索追加0、10CPU/512MB/20wallでordinary kernel証明。受入はraw全長4/5とactual接着の最小残余、又は正確な反例。失敗tableへの資源追加ではない。

## 日次の保存判断（保存時の監査）
E474
親cycleはR-20261031-01のみ。実時計/commands/CPU/変更sourceの正本は当日DAILY、journal、`data/ten_head_20261031/SOURCE_VALIDATION_INDEX.json`と`CPU_SUMMARY.json`。元0/pと全old prefixを維持。
当card IDで確認された閉区間 1 件、合計 256.161 秒（他unit/親cycleへ二重加算しない）。個別start/end/unit/phaseはjournalの同IDを参照。open区間を含めない。
