# Hypothesis card: 一つのA-runについて元C1のfree-gapを閉じる

- ID: H-20261026-07
- Status: PROVED-LEAN（E-413、全体checkの確定はpacket参照）
- Parent: R-20261026-01、E407/E411。直接H01の未供給edgeに、新しいold clock一意性を使う活用unit。

## 全量化子・一問

任意BlockWord実prefix w（β A^aを含む）、その後のtail S^h A^M、さらにS-gap jと実供給A。
同じ元0/pから数えたtail全体の非供給A数rに対して、語長/h/M/j上限なしでj+1<=rが成立するか。
不足0/正不足は追加仮定しない（この形ではより広く問う）。M0も含めて供給不可能なら証明で除く。
一般の多run tail/C1/free-gapを解決したとは主張しない。

## 新しい紙上chain

E411のS-only old clock一意性（small hも含む）と、S^h A-onlyのlocal供給は第3AだけというE393から、
実A-runの供給A個数<=2、M<=そのfree個数+2。
実最初のAはno_window_after_S_runによりfree。E407はtarget供給から2j+2<=Mを供給。
j>=1なら2j+2<=free+2よりj+1<=free。j0は最初のfreeの存在で閉じる。
S-run中のfreeはなく、原基点のcN加法でtail全体へ接続。M0は全Sの後に供給できない既証明で除く。
この新old共同制約を入力とするため、既知r3分類の再実行や全A<=2rの仮定化ではない。

## 受入・停止

一般の実元0/Int元p free-gap、A-run供給<=2/free+2をLeanで検証し、G5/Audit/checkで受入。
既知SAAA|S4 A4にlocal第3/old第4の両供給があり、free2でgap1の等号を達成する境界対照。
新規CPU探索0（既知exact controlと新一般定理の意味監査）。数学的修理1回。
15分で独立edgeが閉じなければ未解決箇所を保存し7:45まで別の最小課題、以降は監査/保存。

## 07:22 結果と別pass監査

E-413 PROVED-LEAN（直接Lean・G5・全体check416 jobs/2845公理宣言成功）。statementは上記の元0/Int元pそのもの。全h/M/j、最初A/free、M0/j0を落とさず検証。数学的statement修理0、syntax/lemma名/tactic修正のみ。既知等号対照を強い新反例と呼ばない。

一般多run H01はCONJECTURED、直接方法STOPPEDのまま。単一runで供給最多2という新edgeが閉じ、全Aをfreeへ無条件置換したものではない。

## 当日journal確定実績
親cycle R-20261026-01: 06:02:22.120877〜07:59:56.352321、確認済み117分34.231秒、不足2分25.769秒。
このcardは同じcycleの一部で、別cycle/CPUとして追加加算しない。unit別実績/commands/再配分/失敗/残課題は[当日DAILY](RESEARCH_HANDOFF_2026-10-26_DAILY.md)と[journal](data/daily_research/2026-10-26.json)を参照。待機/未確認/前日分の加算なし。
