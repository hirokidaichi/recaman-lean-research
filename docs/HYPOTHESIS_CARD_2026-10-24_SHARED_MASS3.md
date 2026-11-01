# Hypothesis card: 共通prefixはmass3の面積5/7を同時供給できない

ID H-20261024-06。Parent R-20261024-01 / E-381。Status PROVED-LEAN。
Mode 局所探索、最初15分。大規模BFSを続けず、同じprefixを共有する新しい制約を調べる。
探索CPU0、紙上・Leanの記号的分類のみ。親cycleの実時間を二重計上しない。

## 一問と全量化子

任意padded BlockWord prefix f[0,n)、任意のt1,t2<nについて、
Fn−Ft1=Fn−Ft2=3、Ar(t1,n−t1)=5、Ar(t2,n−t2)=7が同時に成立しないか。
個別に可能なold mass/area signatureを、同じprefix上で独立に選べるとは仮定しない。

## 紙上chain・反証pass（実装前）

任意BlockWord suffixでmass3の語はAAA / SAAAA / ASAAAの三つだけ、面積は6 /5 /7。
freeの前はmass2、aasの前はmass1、tripleはmass≥4で帰納分類できる。
面積5/7なら長さ5のsuffixがそれぞれSAAAA / ASAAAとなり、同じprefixの末尾5は両方になれない。

個々のsignatureは実現する: SAAAAはmass3/area5、ASAAAはmass3/area7。
前者はtail S6 A4、後者はtail S A S7 A5を付けると、全語mass1/area0となる。
どちらのtailにもlocal P2はないので、個別にはold supplyが本当に必要になる。
ただし同じprefixを共有できるという主張はしない。この不可能性が受入目標。
仮定から共通prefixを外した上記2例を陰性対照にし、area6と5/7の併存は排除しない。

## 受入・停止と判断価値

実際のfと二つのold始点を量化したLean排除、または同じprefixの反例。
受入は独立signatureモデルにはない非同値なjoint入力。C1そのものやHを仮定しない。
15分で新しいcoupling edgeがなければ停止し、今日の証明の意味監査へ戻る。
成功時はold mass3の極値二択を共通prefixの状態として保つ次unitを提案できる。
一般mass/任意a_zやC1全体の解決にはしない。有限budgetの上限だけを増やす再開は行わない。

追加の弱化対照（実装前手計算）: grammarを外したprefix ASAS SAAAAは、
全体のmass3/area7と末尾SAAAAのmass3/area5を同時に持つ。
従って同じprefixでのarea一意性やgrammarなしの排除は主張しない。

## 検証済み判定

PROVED-LEAN: E-394。full checkとAuditの成功ログを当日packetへ保存。
親C1/Q全体とr4全分類は未解決、個々の条件を省略しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **738.576秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
