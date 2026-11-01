# Hypothesis card: 明示16語から任意長futureのQ

ID H-20261024-04。Parent R-20261024-01 / E-388。Status PROVED-LEAN。
C1活用、最初の15分。H02のa_z≤4分類が未供給なので、rootの形を明示した別statementで固定する。

## 一問と全量化子

任意f、任意padded BlockWord prefix終端n、n≤q≤b、元0基点の不足がnで0、(n,b]で正、qで1、
[n,q)の実語が明示16語のいずれか、[q,b)の元0基点非Endable A≤1、Fb≤Fnとする。
全future長/深さ・全古い始点t<nについてZ≥0と¬P2(t,b)をLeanで証明できるか。
16語はE-386の8語にE-388の8候補を加えた実際のリストで、QやHの同値wrapperではない。
この形がa_z≤4の全入力を覆うという命題は未証明のまま。r4全体の解決と数えない。

## chain / 反証 / 受入 / 停止

719状態の全遷移とguard面積をkernelで検査。actual-word simulationで全P2を接続する。
root16語は全て深さ4内を有限検査できる。futureが深さ4を下回ればE-379のfresh-lowへ分ける。
元pのcount/Endableを途中nへrebasingしない。y予算は[q,b)と[q,b+1)の差を監査。
深さ仮定が最終statementへ残ったり、root全包含を未証明のまま仮定して昇格するなら停止。
受入は上の全量化子のLean statementと別passの逐語audit。新探索CPU0、既存入力hash固定。

## 検証済み判定

PROVED-LEAN: E-392（具体16root条件付き）。full checkとAuditの成功ログを当日packetへ保存。
親C1/Q全体とr4全分類は未解決、個々の条件を省略しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **195.149秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
