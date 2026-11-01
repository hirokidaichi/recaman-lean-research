# Five approaches to deciding Recamán surjectivity: parallel triage

Started: 2026-09-07 00:57 UTC. Source base: `612fcfa`.

## 結論

**次に掘る候補は④の「周期符号語の供給不足」。全periodへ量化した具体的な組合せ命題へ
縮約できたが、まだ未証明である。非全射性へ直結する新しい不等式は得られていない。**

①②③⑤では、試した限定的な案を止める反例または一般的な不可能性を得た。
5方式そのものを不可能と判定したのではない。②③に残る時刻順の共同生成、①の適応的な履歴要約、
⑤の補充を制御した資源量は未決だが、直ちに証明を始められる新候補はまだない。

The user explicitly requested parallel investigation of five approaches, followed by
deeper work in order of promise. Both surjectivity and its negation count as success.
This sprint prioritizes finding a noncircular route to non-surjectivity without assuming it.

## Frozen first-pass scope

| Pattern | Owner | Card | First acceptance gate |
|---|---|---|---|
| ① Inductive state condition | entry_barrier | H-20260907-04 | A concrete preserved condition or an explicit indistinguishability obstruction |
| ② Backward first-hit analysis | entry_barrier | H-20260907-05 | A necessary history restriction stronger than the late-landing identity |
| ③ Joint generation cost | joint_generation | H-20260907-06 | A new coexistence constraint, or a counterexample to the frozen candidate |
| ④ Macro induction | macro_induction | H-20260907-07 | One parametric block family that transports its own required history, or an obstruction |
| ⑤ Multi-hole capacity | root | H-20260907-08 | An independent finite capacity, or a general no-go for the hole-only abstraction |

First pass: approximately 20 minutes per worker. Root evaluates the five patterns, then
spends the next pass on the strongest concrete candidates. A lack of a surviving candidate
is a valid outcome; no stopped route is reopened merely to keep a worker busy.

## Ranking rule

Compare evidence, not an invented probability of solving the open problem:

1. Does the candidate remove a genuine unknown edge toward a fixed-cutoff exclusion or
   a strict capacity deficit for a finite set of holes?
2. Does it use a constraint absent from the known seeded countermodels?
3. Is its acceptance decidable by a short paper argument or an exact finite falsifier?
4. Does it survive small cases, equality boundaries, weakened histories, and independent audit?

An identity/reformulation alone fails gate 1. Reusing a known counterexample as a new
positive premise fails gate 2. Finite evidence is not promoted to an all-scale theorem.
Discovery and holdout roles must be fixed in each card before the relevant computation.

## Isolation

Workers own distinct cards and files under `experiments/parallel20260907/` and
`docs/data/parallel20260907/`. Shared Lean entry points, registry, frontier, and GitHub
issues are updated only by root after semantic audit. The user-owned untracked
`recaman-visualizer/` is excluded from all work.

## Results and second pass

| 優先順位 | パターン | 今回の最強の証拠 | 次に掘る対象 / 判定 |
|---|---|---|---|
| 1 | ④ 区間単位の帰納 | `PROVED-PAPER`：固定周期の実更新は有限lagの供給恒等式を要求する。period≤18の229,045語は必要条件を全加算phaseで満たせない（`COMPUTED`） | 全periodの供給不足を証明または反証する具体的な一問が残る。可変長blockを排除したとは言わない |
| 2 | ② 初出からの逆算 | `PROVED-PAPER`：必要なsmall blockerはchain開始前に存在。1Mの286,261件を分類。追加のbirth時刻制約は5@129で`REFUTED` | SS入口のold算術級数とfresh帯の共存を扱う新しい不等式が必要。今回の時刻制約は停止 |
| 3 | ③ 履歴の共同生成 | `PROVED-PAPER`：E-056反例を隣接gap≤clockへ補強しても、freshnessとsurvival違反が残る | 静的な連結性への圧縮は停止。birth時刻・runの順序・付随値を保持する候補が出た場合だけ再開 |
| 4 | ① 保存される状態条件 | `PROVED-PAPER`：同じlow membership・個数・最大・総和・剰余個数でも2step先のtarget到達が異なる履歴対 | この集計による決定的予測は停止。candidate membershipを適応的に持つsoundな抽象は未排除 |
| 5 | ⑤ 複数の穴の保存 | `PROVED-PAPER`：任意entry・無制限bandの抽象では、どんな有限穴集合も空にできる | 穴集合だけの保存則は停止。実際のentry/survivalや補充不能資源の独立上界が必要 |

これは問題を解ける確率の順位ではなく、**次の独立した数学的入力がどれほど具体化したか**の順位である。
2位以下には、まだ直ちに形式化すべき候補がない。④も固定block反復の可否を判定する構造研究であり、
その成功から永久欠損が直接出るわけではない。

## ④を優先して掘った結果

有限の履歴からexactなRecamán更新を続け、ある時点以降の符号が周期pの±1語になると仮定する。
符号和S≤0は非負性に反する。S>0なら各phaseの値は共通の正の二次係数を持つため、古い有限履歴は
将来の加算候補を塞げなくなり、供給者とのclock差は有界になる。

step into tが加算である各phaseについて、あるdが次を満たす必要がある：

```text
1 ≤ d ≤ p(p+1),
Σ(i=1..d) ε(t−i) = 1,
Σ(i=1..d) i·ε(t−i) = 0.                 (P2)
```

この縮約は`PROVED-PAPER`で、二人の独立監査を通した。全periodで「少なくとも一つの加算phaseには
P2を満たすdがない」と言えれば、固定符号語の永久反復を排除できる。これは`CONJECTURED`である。
P2を全加算phaseで満たす語が見つかっても、減算のfreshness等が別途必要なので実際の周期軌道にはならない。

さらに、供給可能な加算phase集合Uと減算phase集合Dに対する `|U|≤|D|` という強い候補も得た。
これが真ならS>0より全加算の供給は不可能になる。period≤16の56,747語では違反0だが、一般証明はない。

深掘りでは次を実施した。

- 凍結discovery：period1..12、3,458語。凍結holdout：period13..18、225,587語。
  全加算phaseが供給可能な語は0。これは有限語の全列挙で、無限periodの証明ではない。
- 別の固定protocolでperiod19..64を探索。小さい正の符号和を中心に90,640回評価（重複を含む）し、
  反例0。closed-form lag計算を120語で直接総和と照合した。無作為な全語分布や確率評価とは扱わない。
- 最長run、後方lex順、最大weighted sum、放物線の最小値という単純なphase選択則は反例で失敗した。
- 最小供給lagの区間内にある最古のSへ課金する写像も、`SSSSAAAASAAA` の加算phase7/11が
  同じS phase8へ写るため`REFUTED`。その例では他のmatchingは存在するので、一般のHall条件や
  `|U|≤|D|`の反証ではない。単射を仮定して証明を続けてはいけない。

次のissueは、P2の全period命題を証明するか、全加算phaseがP2を満たす明示語で反証するものに絞る。
matchingを使うなら任意部分集合についてのHall条件が未証明義務となる。periodを増やすだけでは完了としない。

## 他のパターンの具体的な反例

①：clock99732の実履歴の2値を交換した履歴は、current199486、low membership `[0,99752]`、
個数74019、最大592216、総和、mod66の全個数を保つ。しかし実履歴は `199486→99753→19`、
交換履歴は `199486→299219→398953` となる（`COMPUTED`）。交換履歴がcanonicalに到達可能とは
主張しない。soundな非決定的抽象なら両方の未来を含められるので、全不変条件のno-goではない。

②：5@129は `377→258→138` のSS入口から4個のAS pairを経る。必要なold blocker
17,14,11,8のうち17@25、14@31、8@16は値より遅く初出する。fresh帯137..134とも同じcanonical履歴で
共存するため、「SS入口ならold blockerは早期に生成済み」という追加候補は破れる。

③：最小E-056例では7個の橋をseedへ加え、最大gapを8247から4094へ減らしても
`SS(AS)^51 S A^10 S^10` と2@4219、survival slack−160が残る。将来の全fresh減算値を避けた
seed追加はその有限continuationを変えない、という一般補題で全パラメータへ拡張した。

⑤：抽象arcのentryを最大穴の剰余類にすれば少なくとも一穴が消えるので、有限帰納で全穴を消せる。
canonicalの負の対照でも、128まで未出の `{4,5,19}` は99734までに全て出現する。
ある特別な穴集合が永久保護される可能性は残るが、穴の個数や剰余類だけでは証拠にならない。

## 証拠と再現

- [①カード](HYPOTHESIS_CARD_2026-09-07_INDUCTIVE_BARRIER.md)
- [②カード](HYPOTHESIS_CARD_2026-09-07_FIRST_HIT_BACKWARD.md)
- [③カード](HYPOTHESIS_CARD_2026-09-07_JOINT_GENERATION_COST.md)
- [④カード](HYPOTHESIS_CARD_2026-09-07_MACRO_INDUCTION.md)
- [⑤カード](HYPOTHESIS_CARD_2026-09-07_MULTI_HOLE_CAPACITY.md)
- [実行一覧・exact出力・source hash](data/parallel20260907/README.md)
- [独立した範囲監査](data/parallel20260907/scope_independent_audit.md)
- [④の独立した数学監査](data/parallel20260907/periodic_independent_audit.md)

今回はLean sourceを増やさず、紙上証明・有限計算・未証明命題を区別して記録した。
最強の新規部分成果は有限lag供給への紙上縮約と、各限定classの明示的な反例である。
既存のLean定理を越える一様な非全射性の十分条件はまだ得られていない。

## 次の判断

④の全period組合せ命題を次のbounded [issue #73](https://github.com/hirokidaichi/recaman-lean-research/issues/73)へ登録した。他の案は、表に記した独立入力が
具体化するまで追加の列挙・係数調整・wrapper実装をしない。否定側で今後も必要なのは、
同じ検証済みcutoff以後の到達排除、または特別な有限穴集合の厳密な容量不足である。
周期性を排除できても、その接続は別途必要である。
