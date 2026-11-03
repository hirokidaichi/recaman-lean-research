# H-20261104-16: AS cross0のsource境界

Owner Codex、R-20261104-01。CONJECTURED。07:15:34開始、worker未起動/CPU0。

任意同old target suffixA、prefix b=S^h A^M、任意後続word x（cntF x>=1）、source/target窓がfinalbandで、j>=2/M<=j+2。全h/M/x/clock/gapを量化。二窓からM=j+1/h=j+2/i+j=Tを導けるか。

紙上: R=j+1、δ=i+j-T>=0、X=M-δ=h-1>=-1。key0/cross0よりX²=R²+2δ cntF(x)。M<=R+1からδ<=1、δ1はX<=Rかつ正項で矛盾、δ0はX=R。source以前のfree/R結論を仮定しない。actual counterのM<=R+1へ接着すればfirstA/第二S先頭境界のstrict削減になる。

Falsifier: suffix S数>=1を外すとδ1/M=R+1/X=Rの例外があるため保持。j>=2を外すX=-1境界も保持。cross0を任意mixed prefixへ広げない。受入は具体word/sourceの新equality、単なるkey wrapperでない。15分gate/M512 capはSTOPPED、紙上と未Lean接着を区別する。

07:16:13 concrete word/source boundary passed -j1 -M512 (0.824255 validation CPU), fullcheck/Audit pending. Actual counter/source classification remains a separate step. The equality is compatible with a first-A source; h=R+1 does not by itself give a long-first count1 bound.

## 当日最終判断（2026-11-04）

PROVED-LEAN E549。word/source exact境界、freegapでない。
完全な実時計・commands・失敗receipt・次の入口は[DAILY](RESEARCH_HANDOFF_2026-11-04_DAILY.md)と当日packetを参照。
