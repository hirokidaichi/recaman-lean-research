# Hypothesis card: C1 の面積不等式 Q

- ID: `H-20261021-04`
- Owner: Codex（計画整理・2026-10-22実行、各役割は別pass）
- Created: 2026-10-21
- Status: `CONJECTURED`
- Research branch: SL d=1 / S1 / C1
- Work state: 2026-10-24、a_z≤3のQはE-387、明示16rootのfuture QはE-392。a_z≤4の分類はE-388 COMPUTEDのまま。E-399の共通低mass代表/実EndN同値を固定代表r4モデルへ使う。一般Q/C1は未解決。
- Parent / cycle: [H-20261020-01](HYPOTHESIS_CARD_2026-10-20_LINE_CAPACITY.md) / [R-20261021-01](RESEARCH_ALLOCATION_2026-10-21.md)

## Exact statement

任意の[完成設定D](RESEARCH_ALLOCATION_2026-10-21.md)で、次を目標にする。

**C1**: 全ての `q0≤b<c` と `p≤t<k1` について、`Endable_p(b) → ¬P2(t,b)`。

**Q v1（十分条件の候補）**: `g=F(k1)` とすると、全ての `q0≤b<c` に対して
`F(b)≤g → Z(b):=Σ_{k1<u≤b}(F(u)−F(b)+1)≥0`。
QはA以外のclockも量化する強化。C1そのものやHをQの仮定に置かない。

Qを使うには、全ての `p≤t<k1` について、別途
`P(t): F(k1)−F(t)≥1 ∧ Σ_{t<u≤k1}(F(u)−F(t))≥1` が必要。
Pはブロック接頭辞とE-378の接尾辞正値性から供給する計画であり、その接頭辞を与える短いEqClassWを確認する。
k1直前がendableでなければ、最後のendableまでの等号区間と残るA列を分ける。`d(k1)=0`だけで
EqClassWの「最後がendable」という仮定を満たしたことにしない。
`k1=p` ならC1は空の範囲で自明だが、それだけを新しい研究成果にしない。

## Why it would matter / dependency chain

```text
短い等号区間のEqClassW → [p,k1)がブロック語 → E-378でP
P2(t,b)とP → F(b)=F(t)+1≤g
P2のmoment = Σ_(t,k1](F−F(t)) + Z(b) = 0
Pの第2不等式とQ → 右辺≥1、矛盾 → C1
```

これはQを証明したchainではない。次の新しい入力はQの一様な評価、またはPの供給不足の解消。
C1はC2と補題Fの再検算と合わせてS1へ使う。C1単独ではSLを閉じない。

## Allocation and decision value

- Mode: 局所探索。問いは「上のchainで未供給のedgeはQだけか」。
- 予定: cycle100分のうち15分、実績は2026-10-22の区間1分45秒（読取・保存込み、共通監査別）。C2から切り替わる場合は35分へ変更して記録する。
- 監査: cycle共通10分の別pass。追加CPU探索0、紙上unitのためdiscovery/holdoutは該当なし。
- 成功時: 仮定供給を確認した一つの不等式へ研究範囲を固定し、次cycleの活用候補にする。
- 失敗時: Qの反例、または接頭辞版と完成版の差を保存し、追加すべき独立入力を識別する。

## Provenance / falsification / acceptance

- 参照: 親カードのc1proof報告、E-378、`experiments/issue73_20261020/c1proof/q.c`。
- 旧報告の `|w|≤32` と「最小1」は新しいholdoutでも証明でもない。今回は再実行しない。
- 反証pass: `k1=p`、`b=q0`、`F(b)=g`、終点直前、整数の負の面積を含む例を照合する。
  `q.c`は完成条件を要求せず、Pの違反を除外せず集計する。`d(b+1)` の境界も別に扱う。
- 接頭辞だけのS1が偽となる `[SSAAAASA|AA` を、完成条件を落とす際の対照として使う。
  これはQ/C1そのものの反例だとは主張しない。
- 合格: PとQからC1への全量化子・符号・区間端点の照合、およびPの供給元を明示し、残る未知edgeを一つにする。
  反例なら該当する全仮定を満たすものを記録する。Qが未証明ならC1も `CONJECTURED` のまま。
- 修理: 強いQの反例がある場合だけ、一回、Endableなbへの制限がC1に十分かをv2で検査する。
  反例を排除するだけの事後的な仮定や、C1の言い換えは追加しない。

## Evidence log / semantic audit

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-10-21 | `CONJECTURED` | cycle基準revision、親カード・q.c・E-378閲覧 | Qの証明なし。供給を検算する依存chainを記載 |

Pの基点とEndableの基点はp。全窓を排除するC1を、最新窓だけの主張へ弱めない。
Pを与えるEqClassWは真部分区間だけに使う。面積identityの包装をQの証明と数えない。
提案・反証・依存chain・監査を順に別passとして記録する。

## Decision / allocation update

- 現判定: C2の確認後に15分の入力診断。数学的主張は `CONJECTURED`。
- 継続: Pの供給を確認し、Qへ独立な下界を与える機構、または候補族を除く反例が得られた場合。
- 切替: Pが未供給ならその不足へ問いを絞り、単なる走査延長は行わない。予算到達で次はTSの診断。
- 停止: Qを仮定したC1のwrapperしか増えない場合、その方法を `STOPPED`。
- 再開: Qに対する新しい面積評価、または不足した接頭辞の供給証明がある場合。
- 配分更新log: 未実行。実績と15→35分の変更の有無をcycleと同期する。

## 2026-10-22 入力診断の結果

[監査ノート§4](RESEARCH_NOTE_2026-10-22_INPUT_AUDIT.md)に完全な紙上chainを記録した。
最後のEndable vまでが短い等号区間で、残りはA列であることをdの非負性から示せる。
従って `[p,k1)=β A^a` となり、既存E-378の `block_suffix_positive_walk` がPを供給する。
この構成は同ファイルの `ts_one` の証明でも使われており、新しい研究定理として登録しない。

- 反証・境界pass: k1=p、Endableなし、末尾Aなしを分けた。非負性を落とした抽象ledgerでは相殺が起き、同じ推論は使えない。
- 依存監査: 真部分区間のEqClassWのみを使い、全区間HやQをPの供給に仮定していない。
- 現判定: 入力診断の一問は終了。C1/Qの数学的labelは`CONJECTURED`のまま。
- 次の研究単位: Dの下のQの一様な面積下界、またはDを満たす明示反例。
  Pの供給確認を最初から繰り返さず、Qを仮定したwrapperを成果にしない。
- 次cycleの予定: 活用60分をQへ。実績と当日の時間不足はhandoff参照。15分や35分を使い切った扱いにしない。

## 2026-10-22 追加研究の結果（朝の実績とは別）

[追加カード](HYPOTHESIS_CARD_2026-10-22_C1_Q_MAKEUP.md)と[引き継ぎ](RESEARCH_HANDOFF_2026-10-22_MAKEUP.md)へ継続。
E-379はfresh-low Q、E-380はold contextと適応mass代表、E-381は二次面積上下界と等号形を形式化。
E-382/E-383は条件付き全treeの独立計算、E-384は全massの面積spectrumの紙上分類（存在方向は未Lean）。
Q/C1全体はCONJECTUREDのまま。次はa_z≤3の深さ4供給を一問にし、Pの入力監査を繰り返さない。
このcycleは新edgeと候補集合の変化があるので、同じ障害で無変化のcycleとして加算しない。
以前の停滞状態を日付変更でリセットしない。Az単独非負・自由tag・UNKNOWN同設定延長は再開しない。

## 2026-10-23 の消費可能な新入力

E-386はa_z≤3の全長z深さ4と8語分類、E-387は任意長/深さのyのQと全t<k1のP2排除を形式化。
`three_nonsupplied_area_int`で元p基点のEndable/countPのまま使える。
完成Dからのprefix供給をやり直す必要はなく、今回は新しいQの仮定がDの具体条件から供給される範囲を照合した。
制限a_z≤3は明示したままで、C1全体やC2/F/TS/SL/Hを閉じたとは言わない。
E-388のa_z≤4は全長COMPUTEDだがkernel未検査。次はE-389を使うevent certificateへ進む。

## 2026-10-24の継続判断

E-390〜394/E-396〜399の条件付き入力をPROVED-LEAN、強い2供給案をE-395 REFUTEDへ。
明示16rootの後半Qはkernel化したが、az≤4からの全包含は未供給。一般Q/C1はCONJECTUREDのまま。
共通prefixのmass3/4を同じ10代表へ保存し実old窓/実EndNの双方向を供給するE-399から、固定代表r4モデルの候補削減評価へ進む。
[DAILY](RESEARCH_HANDOFF_2026-10-24_DAILY.md)、[次カード](HYPOTHESIS_CARD_2026-10-25_JOINT_OLD_SUPPLY.md)。
実績・CPU・再配分は当日journal/DAILY正本。旧P供給監査を繰り返さない。

## 2026-10-29 状態の追記

E451はk=3個の非空A-runに対する元p実free-gapを全r/全長で証明した。E385〜387のr<=3/全runとは別の範囲。一般Qの累積面積評価、四run以上、C1そのものは未解決。このカードのStatusはCONJECTUREDを維持する。次の入口は[四run old-target H-20261030-01](HYPOTHESIS_CARD_2026-10-30_FOUR_RUN_OLD_TARGET.md)。E456の数値残余は有限history分類やQ証明ではない。
