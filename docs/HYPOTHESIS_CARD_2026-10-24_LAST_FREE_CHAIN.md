# Hypothesis card: 第4のfree A後の供給連鎖は高々2回か

ID H-20261024-07。Parent R-20261024-01 / E-386,E-388,E-391。Status REFUTED。
Mode 局所探索、最初15分。新しい全状態探索やr上限延長ではなく、既存graphの最後のfree A分解を診断する。

## 一問・量化子（実行前）

任意padded BlockWord prefix後の正不足prefixで元基点非Endable A≤4とする。
第4の非Endable Aが現れた後、追加のAは高々2個か、という強い補助案を攻撃する。
終端不足1を要求しない強化なので、反例があっても親C1/Qの反例とはしない。

## 発見・独立検証・費用

保存済みmacro-certificateのAN4層はA個数が必ず増えるDAG。
最後のAN3→AN4 edge後のsupplied-only path最大長を動的計画法で計算する。
max suffix>2の候補をsource index/edge index順に最大64個保存し、前半32をdiscovery、後半32をholdoutとする。
完全graphの値はCOMPUTEDで、kernel未検証。緩和モデルのpathだけでは実際の命題を反証しない。
実prefix候補は既知4語ASAAA/AASAAA/SAAASAAA/SSAAAASAAAを固定し、各新tailと組み合わせる。
同じ元0基点の全始点P2を直接F/Gと独立reverse mass/momentで全検算する。
prefix不足0、全tail不足>0、AN個数4、全tag一致、最後のfree以後A数>2が受入反例条件。
既知prefixだけを新しい未見prefixと呼ばず、今回初めて検査するtailとの組を対象とする。
CPU≤20秒、wall≤25秒をC1残り枠から事前再配分（親の120CPU cap内）。各job≤8CPU/10wall。
source/argv/入力hashを実行前固定。反例が得られなければ上限や候補数を延長せず停止する。

## 判断

実際の反例なら強化案だけREFUTEDとし、zero-free phaseを2段に制限する証明計画を棄却。
緩和だけの反例ならCOMPUTEDに留め、E-394の共通prefix制約で落ちるかを診断する。
一般Q/r4分類・全射性を昇格も反証もせず、最後のfree後の別の小さい証明義務へ移す。

## 形式化後の別pass判断（実時計07:12 JST以降）

E-395。既知E-389語を再解析し、最後のfree後5個の供給Aを独立reverse momentで確認。26候補/88実pair、holdoutは候補不足で0。親Q/C1の反例ではない。2段制限を棄却しH09へ切替。

実績正本は `docs/data/daily_research/2026-10-24.json`。親R-20261024-01へ包含し二重計上しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **261.089秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
