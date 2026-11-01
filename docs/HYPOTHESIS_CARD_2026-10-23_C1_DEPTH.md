# Hypothesis card: a_z≤3の正不足excursionは深さ≤4か

- ID: `H-20261023-01`
- Parent: [C1 Q](HYPOTHESIS_CARD_2026-10-21_C1_AREA.md) / [追加研究](HYPOTHESIS_CARD_2026-10-22_C1_Q_MAKEUP.md)
- Cycle: `R-20261023-01`
- Status: `PROVED-LEAN`（E-386、カードの明示仮定の下で全長の深さ4を証明）
- Work state: 2026-10-23 06:02:46 JSTにjournal開始、06:43:54に次unitへ移行。全体checkは06:44台に通過。
- Owner: Codex。提案・反証・形式化・監査は別pass。
- Handoff: [2026-10-22 MAKEUP](RESEARCH_HANDOFF_2026-10-22_MAKEUP.md)

## 一問・全量化子

任意の有限符号語w（長さL）、任意の0≤n<q≤L、任意のブロック語βと整数a≥0を取る。
σ(i)=+1はA、−1はS。F(0)=0、F(u+1)=F(u)+σ(u)。

```text
P2(t,b) : 0≤t<b<L,
          Σ_[t,b) σ(i)=1 かつ Σ_[t,b) (b−i)σ(i)=0
End_0(b) : σ(b)=+1 かつ ∃t∈[0,b), P2(t,b)
d(u) = #S[0,u) − #End_0[0,u)
a_z = #{i∈[n,q) | σ(i)=+1 かつ ¬End_0(i)}
```

全窓・全clockのEndable基点を元の0に固定し、nへrebasingしない。一般のpは平行移動で同じ問い。
仮定は次の全て。

1. `w.take n = β ++ A^a`、`BlockWord β`（文法A / SAAA / SSAAAASAAA）。
2. 全0≤u≤nでd(u)≥0、d(n)=0。
3. 全n<u≤qでd(u)≥1、d(q)=1。
4. a_z≤3。

結論候補は `∀u∈[n,q], F(u)≥F(n)−4`。
語長、S数、old windowのlagの上限は置かない。全区間H/EqClassW/Qを仮定しない。
これは完成Dを弱めた補助入力であり、反例が出ても完成D版C1/Qを自動的にREFUTEDへ変えない。

## 前回からの独立入力・用途

- E-379 `PROVED-LEAN`: 全tailの最小値をq以後に訪れる場合のQ。
- E-380 `PROVED-LEAN`: suffix閉性、深さからのold context削減、全後半clockを同時保存する適応mass代表。
- E-381 `PROVED-LEAN`: ブロック面積の二次上下界と下界の等号二族。
- E-382 `COMPUTED`: a_z≤3・深さ≤4の全71context、全treeを独立照合済み。
- E-383 `COMPUTED`: 任意長prefix・z長1..32で上記深さ入力を確認。全125181373 nodeを独立照合済み。
- E-384 `PROVED-PAPER`: 全massの面積spectrum。存在方向は未Lean、人間レビュー未。

深さ入力が一様に供給できれば、E-382とE-379の二分でa_z≤3のQを全yへ使える。
COMPUTEDへの依存と、一般Qのa_z≥4、C2/F、TSの未解決部分はそのまま残る。

## 受入・反証・停止

- 受入: 語長に依存しない非循環な紙上証明と最弱の新edge、または全仮定を満たす深さ≥5の具体語。
- 反証pass: a_z=0/1/2/3、n=0、空β、末尾A列、最初の深い谷、q直前、既知4種類のzを攻撃する。
  実反例候補は全始点の直接mass/momentと元0基点の全d/AN/Fを独立再計算する。
- 最初の確認点: 06:10から15分。新しい不等式・候補の削減・反例が出るかを判定する。
- 不通過なら残りの活用45分を新しいjoint-area入力25分とold windowの共通prefix制約20分へ切替。
  単位の停止を一日の終了とせず、新しい問い・受入・停止を先に固定する。
- Az単独非負、自由Endable tag、同じUNKNOWNモデルへの時間追加、語長32の単なる延長はSTOPPEDのまま。
- 修理は一回まで。結論を仮定する定義、同値wrapper、自由整数算術だけを成果にしない。

## 予定と実績（2026-10-23）

開始確認10＋研究・監査100＋引き継ぎ10＝120分。
研究・監査は活用60（本問い）・局所探索30（別機構の入力）・独立passの監査10。
監査超過は研究から差し引き、7:45以降は新規数学探索を始めず、8:00を延長しない。
追加CPU探索は当初0。必要なら実行前に上限・argv・discovery/独立holdout・source hashを固定して再配分する。

| 項目 | 予定 | 実績 |
|---|---|---|
| 実開始・実終了 | 06:00〜08:00 JST（親日次） | setup 06:02:46開始、主unit研究06:05:36〜06:43:54。親日次は継続 |
| 日次journal | `docs/data/daily_research/2026-10-23.json` | 作成済み。最終秒数はDAILYを参照 |
| CPU・commands・証拠 | 必要時に実行前固定 | E-385/E-386、raw logs保存。CPUは親一括で別計上 |
| 継続/切替/停止 | 最初の15分と各unit末で判定 | gate通過後に全長証明、H-20261023-02へ切替 |

## 実行結果（06:46 JST途中保存、当日の研究は継続）

- E-385 / PROVED-LEAN: 実際のold P2窓にはtailのS数≤2×全A数−2が必要。
- E-386 / PROVED-LEAN: 任意長の正不足excursionで非Endable A≤3なら全A≤7。
  終端不足1ならS / SA / SAA / SSAAA / SASAAA / SSAAAA / SSAAAASA / SSSSAAAASAAAの8語に分類され、
  全prefixでF≥F(n)−4。カードの全量化子を保持し、元0基点の全P2を使用した。
- 閉グラフ3,324状態をkernel decideで検査し、actual-word simulationを任意長の帰納で証明。
  global d(n)=0と以後の正不足をn基点のcountへ分割する接続も形式化。
  prefix内部の不足非負性は使わない強い版で、H/EqClassW/Qは仮定していない。
- CPU探索実績はdataのraw JSON/timeを別計上。上限240秒内。検証CPUと実時計journalへ二重加算しない。
- 最初の15分gateは新しい不等式と候補削減で通過。条件付き45分再配分は発動しなかった。
- `./scripts/check.sh`: 405 jobs / 2719宣言、許可した3公理のみ。新規Data moduleのlint通過。
  [E-385](statement_audits/E-385.md) / [E-386](statement_audits/E-386.md)で逐語監査。
- 予定120分全体や未確認open区間を本unitの実績にしない。unit研究は06:05:36〜06:43:54で、
  並行validationは親journalの経過へ一度だけ含める。日次の最終実績はDAILY末尾に保存する。
- 次の一問は[H-20261023-02](HYPOTHESIS_CARD_2026-10-23_C1_Q_THREE.md)。完了した深さの問いを翌日反復しない。
  一般a_z≥4、C1/Q/H/SL全体はこの深さ定理では解決していない。

以後は[日次スケジュール](DAILY_RESEARCH_SCHEDULE.md)のjournalを用い、5分以内を目安に確認点を保存。
30分の予約は復帰と途中保存用。unitを終えても7:45までは次の有用な問いへ続ける。
次の日は当日handoffの最後の判断を読み、完了unitも本問いも最初から反復しない。
