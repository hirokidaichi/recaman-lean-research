# Hypothesis card: 既知5連供給motifの小さいzero-free証明書

ID H-20261024-09。Parent R-20261024-01 / E-391,E-393,E-394。Status PROVED-LEAN。
C1活用、最初15分（07:05〜07:20目安）。大規模decideを再開せず、具体motifを記号的に切り出す。

## 一問（実行前）

任意padded BlockWord prefix後に実tail w0=S5 A3 S4 A2があり、その後の非Endable A予算0とする。
任意長futureのAは高々5個で、5個に達する経路の供給gapは[0,0,1,0,0]だけか。
6個のword node w0, w0A, w0AA, w0AASA, w0AASAA, w0AASAAA を使う。
各nodeの最初の供給A前はE-389によりj≤2全A−2。有限local/old判定で上記gapを絞る。

## 反証・一回の修理・受入

まず任意prefixの必要old signatureで全jを検査する。余計な枝があればv1を停止する。
一度だけ許すv2は、同じprefixにmass3/area7の実suffixがあるという具体条件を加えるもの。
既知prefix ASAAAはこの条件を供給し、E-394がmass3/area5のold枝を排除する。
これは未証明のQやrankを仮定する修理ではない。v2でも余計な枝があれば今回のmotif証明書法を止める。
既知pathの有限再検算であり、6nodeを未見holdoutとは呼ばない。CPU≤5秒、wall≤10秒、独立kernel照合。
受入は全future長のLean上界（具体word/必要prefix条件を明記）、または余計な供給枝の具体記録。
一般AN4・全r4分類・C1全体の証明に昇格しない。

## 形式化後の別pass判断（実時計07:12 JST以降）

E-396。6node小証明書とfirst-A強帰納により任意future長Kの全A≤5−i。w0の後の追加A≤5。修理v2不要、任意prefixの必要old signatureのまま閉じた。独立有限検算とkernel照合を分け、一般AN4分類へ昇格しない。

実績正本は `docs/data/daily_research/2026-10-24.json`。親R-20261024-01へ包含し二重計上しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **395.875秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
