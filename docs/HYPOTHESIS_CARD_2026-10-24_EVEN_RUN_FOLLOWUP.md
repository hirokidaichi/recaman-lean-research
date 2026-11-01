# Hypothesis card: 偶数A-runの最初の供給後に再供給はあるか

ID H-20261024-10。Parent R-20261024-01 / E-393。Status PROVED-LEAN。
Mode 局所探索（意味監査で新しく識別した記号的入力）。実時計開始から15分、延長なし。

## 一問・全量化子・受入

任意k≥1,m≥4k+1,j≥0、任意padded BlockWord prefix後の実tailを
S^m A^(2k) S^(k−1) A S^jとすると、元0基点で末端はEndableでないか。
全パラメータ・tail長・prefix長に上限を置かない。実fのEndable排除をLeanで証明すれば受入。
S^m A^(2k)後のfree予算0なら追加全A≤1という接続は、上の入力とE-393を用いる別義務とし、
未Leanならその旨を残す。一般r4分類/C1の解決とはしない。

## 提案・反証pass（形式化前）

先頭S内からのsuffix S^s A^(2k) S^(k−1) A S^jがmass1ならs=k+1−j。
そのareaは(4k+2)j−4k+1で、j=0なら負、j≥1なら≥3。整数jで0にはならない。
最初のA-run内からのsuffix A^l S^(k−1) A S^jならmass1からl=k−1+j、
area=(k−1)^2+2kj+j²+1≥1。後半S内からは奇数A1の三run、最後A以後は単峰として排除。
old始点は全S=m+k−1+j≥5k、全A=2k+1なのでE-385のS≤4kに反する。

小例/境界: k1はS^m A3という奇数族、k2/j0の先頭S署名area−7、j1なら3。
弱化: mの長いS条件を外すとold供給を排除できない。prefix文法なしの旧反例も保持。
CPU探索0（紙上代数とLean検査のみ）。誤式/余計なsuffixの場合は1回だけ修理、
15分で実fの新しいedgeを得られなければSTOPPEDとして診断を保存し監査へ戻る。

## 07:18の判定（個別Lean成功、全体検証前）

no_endable_even_followup、no_additions_even_followup、one_addition_after_manyS_evenAが個別Lean検査成功。
最初の15分gate内で新しい実fのedgeを供給した。結論は任意k≥1,m≥4k+1、任意future長Kで追加全A≤1。
m≥4k+1は十分条件で、最良閾値とは主張しない。一般r4/rankは未解決。
未知のQやrankを仮定しない。全体check/Audit/逐語auditが終わるまで登録しない。

## 07:23以降の別pass判断

E-397。408jobs/2776宣言の全体Lean/公理監査成功。無制限even runの追加A≤1を含む。最良閾値ではない。
親C1/r4分類は未解決。実績は当日journalを正本とし、親cycleと二重計上しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **306.671秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
