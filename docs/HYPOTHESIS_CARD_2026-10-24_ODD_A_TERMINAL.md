# Hypothesis card: 多数Sの後の奇数長A-runは供給を再開できない

ID H-20261024-05。Parent R-20261024-01 / E-385,E-389。Status PROVED-LEAN。
Mode 局所探索。最初15分、成功なら上限なしの入力として監査・形式化へ。
CPU探索0、紙上の任意パラメータを扱う。親cycleと時間二重計上なし。

## 一問・量化子（実装前）

任意r,m,j≥0でr奇数、m≥2r−1とする。任意のpadded BlockWord prefix後に
実tail S^m A^r S^jがあるなら、その末端は元0基点のEndableではないか。
従ってS^m A^rの後、追加非Endable A予算0なら任意長futureの全Aは0か。
固定r上限・固定A数上限・固定future長を置かない。

## 紙上chain・最弱edge

old始点はE-385が総S≤2r−2を要求するがm+j≥2r−1で不可能。
local始点をleading S内、A-run内、最後のS内で分ける。
leading S内からなら窓はS^s A^r S^jで全A個数が奇数、P2のA個数偶数に反する。
A-run以後からはA^a S^jまたは全Sで、mass1なら面積>0、P2の面積0に反する。
最弱edgeはこの実際の全始点分類と、窓A個数の偶数性との接続。

## 反証pass（実装前）

r1/m1、r3/m5、j0/1/境界を手計算。奇数性を外すr2/m3ではlocal SAAが供給し失敗。
r4/m7ではj1のSSAAAASがP2。mを1だけ下げるr3/m4はSAAA|SSSSAAAのold供給が反例。
より一般にr≥3でprefix=S A^r、tail=S^(2r−2) A^rは全語mass1/area0となる計算を得た。
prefixはSAAAにA^(r−3)を付けたpadded BlockWord。閾値のsharpness候補だが未証明。
前日の全prefix指数上限反例や自由Endable tagモデルを、この命題の反例とは扱わない。

## 受入・停止

任意fと実tailのLean排除、または全仮定を満たす具体例。必要ならsharpnessの一様語族も証明する。
有限r検査を無制限の証明にしない。15分で新しい全始点排除edgeがなければ停止し、既存shape-Qの意味監査へ戻る。
これは高不足のterminal族の排除であり、C1全体やr4全分類の解決とは呼ばない。

## 検証済み判定

PROVED-LEAN: E-393。full checkとAuditの成功ログを当日packetへ保存。
親C1/Q全体とr4全分類は未解決、個々の条件を省略しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **553.983秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
