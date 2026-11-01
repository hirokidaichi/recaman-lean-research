# Hypothesis card: 任意語の有限供給判定から任意長terminal rayへ

ID H-20261024-03。Parent R-20261024-01 / E-389。Status PROVED-LEAN。
Mode 局所探索、最初の15分。r4証明書の検証と時間を二重計上しない。

## 一問・量化子

任意f、任意padded BlockWord prefix終端n、n≤b、任意の実tail w=[n,b)、任意K。
A=wの全A個数。j=0..2A−1の全有限候補についてw S^jがlocal P2も必要old signatureも持たず、
[b,b+K)の元0基点非Endable A個数が0なら、同区間の全A個数も0と一様に導けるか。
固定A上限・固定depth・固定future長を置かない。有限checkは明示Boolで、結論の別名ではない。

## chain / 受入 / 停止

最初のfuture Aを取ると直前はS-gap j。非供給A予算0により実Endable。
n<bならE-389からj≤2A−2で有限checkに反する。n=bはE-378のS-run後の窓なし。
受入は実際のf/EndN/任意Kを量化したLean証明と、具体tailへの適用・仮定を外す対照。
有限checkが強過ぎること自体は親の反例ではなく適用できないこととして保存する。
空tail/全S/全A、j境界、元pの保持、既知S5A3S4A4SA3とfree1対照を反証passで確認。
紙上専用、追加探索CPU0。15分で新しい有限→無限edgeがなければ一般化を停止する。

## 検証済み判定

PROVED-LEAN: E-391。full checkとAuditの成功ログを当日packetへ保存。
親C1/Q全体とr4全分類は未解決、個々の条件を省略しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **147.795秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
