# Hypothesis card: 共通prefixのmass4面積pair

ID H-20261024-11。Parent R-20261024-01 / E-394。Status PROVED-LEAN。
Mode 局所探索、最初10分、CPU探索0。r4大規模tableを再開しない別機構。

## 一問・量化子・受入

任意BlockWordのmass4 suffixは、AAAA/AASAAA/ASAAAA/SAAAAA/SAAASAAA/SSAAAASAAAの6語か。
その面積は順に10/13/11/9/12/9。任意長の同じpadded BlockWord実prefixでmass4となる
二つのsuffix面積x,yは、x=yまたは無順序pair{9,10}/{10,11}/{9,13}/{12,13}に限られるか。
上の必要条件を任意実f/任意prefix長へ接続するLean証明と、4つの許可pairの明示実現を受入とする。
同じ面積でもsuffix語が同じと主張せず、一般massやC1の解決とも呼ばない。

## 反証pass（形式化前）・chain

mass3の両極値排除をmass4へ丸ごと延長すると偽。具体trip語SSAAAASAAAは全体mass4/area9で、
suffix AASAAAもmass4/area13。文法を守る既知のtrip語が両極値を同時供給する。
したがって「全massで両極値排除」は候補から除く。新しい発見語ではない。
6語の全36pairをsuffix包含で検査する。SAAAAAのsuffixAAAAで9/10、ASAAAAで11/10、
tripで9/13、SAAASAAAで12/13を正対照にする。等長で異なる6文字語は共存しない。

BlockWordの先頭atom質量1/2/4から残りmass3/2/0に分解し、E-394のmass3分類と既存mass2分類を使う。
任意二suffixは長い方/短い方が比較可能なので、有限6語間の必要pair検査を実prefixへ持ち上げる。
受入まで10分、新しい分類/候補削減がなければSTOPPED。修理は一回、単なるcutoff延長なし。
実績は当日journalとDAILYに包含し、子カードの予定分を加算しない。

## 07:23以降の別pass判断

E-398。408jobs/2776宣言の全体Lean/公理監査成功。mass4の許可pair制約と既知trip語の両極値併存を含む。
親C1/r4分類は未解決。実績は当日journalを正本とし、親cycleと二重計上しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **146.421秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
