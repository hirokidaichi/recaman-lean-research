# Recamán 全域性研究 — 現況レポート

最終更新: 2026-08-31

## 結論

標準 Recamán 数列の全域性

```text
∀ m : Nat, ∃ t : Nat, a t = m
```

は、まだ証明できていない。いま止めるべきなのは研究そのものではなく、既存の局所不等式を
細分化して全域性へ直接つなぐ路線である。2026-08-30 の二段階監査により、直前まで有望だった
low-quotient minimum、Hall congestion、H6 affine chord はすべて直接証明としての停止条件に
到達した。

現在の判断は次の通り。

- **直接証明のactive branch:** 0
- **独立部分定理として残す候補:** `TailHall₃`
- **active exploratory branch:** target-comb間のupward resetを生成遷移のprovenanceへ戻す
- **再開条件:** permanent-above tail と線形成長・正の減算密度を矛盾させる新しい大域入力、または
  old blocker / nonpositive reset を一様に償却する定理

2026-08-31 の一次文献調査では、Binary Enots Wolley の全射性証明にある
「target opportunity の再来 + 妨害候補の有限消費 + 同一event集合への相反する二側計数」が、現在の
Hall / blocker 路線に最も近い成功機構だと判定した。EKG の frontier-window entry/exit balance を
組み合わせ、run-level gap flow を target-relative な `01/10` crossing episodeへ組み替える。
詳細は [類似 greedy 数列の文献レビュー](./LITERATURE_REVIEW_2026-08-31.md) を参照。

この移植の最初の部品は得られた。targetより低いcandidateは永久上側tailで孤立し、そこから始まる
descending combのlow railはすべてfirst occurrenceになる。historical terminal blocker `b`は
fresh successor `b+1`と対になるため、異なる完了combへ再利用できない。これはraw blocker jobでは
偽だった有限消費が、episode圧縮後には真になることを示す。次エポックではさらに、時間順の二episodeが
「次のfresh interval全体を旧blockerより下へ置く」か「新blockerを旧blockerより上へresetする」かの
厳密な二択に入ることを証明した。ただし後者を一様に排除できていないため、全域性の直接枝はまだ0本である。

## 何が確定したか

### Leanで証明済み

least missing target を仮定した正準最小 tail witness について、次を得た。

1. `LeastMissingTarget.exists_leastTailLedgerMinimum`
   - 商座標は `q ≤ 1`
   - gap は `G ≥ -1`
   - ledger corridor

     ```text
     2 * subSum t + (target + 2) ≤ upperTri t
     upperTri t < 2 * subSum t + 2 * t
     ```

2. `LeastMissingTarget.exists_leastTailLedgerMinimum_lowCoordinates`
   - `a_t < t + target`
   - `q = 0 ∨ (q = 1 ∧ r < target)`

3. `positiveEarlierOccurrence_sharpC3`
   - 正の earlier occurrence が後の clock `+1` で増加を生成するなら `earlier + 3 ≤ time`
   - blocker の正確な ledger payment が成立
   - `time + 1 ≤ (subSum time - subSum earlier) + 3`

2 により、正準 least-missing witness で有望に見えた high-blocker 分岐は実は空である。3 は
一般の renewed / strict tail には有効だが、正準点を反復させる主線にはならない。

4. `TargetCandidateTransitions`
   - below-target candidateは永久上側tailでforced additionになる
   - target omissionにより、その次のcandidateはtargetを厳密に上回る
   - target-relative candidate wordに連続low状態はない
   - fresh comb episodeの全low railはfirst occurrenceで、別episodeのlow railと交わらない
   - terminal blocker `b`は異なる完了combへ再利用できない
   - 後続fresh intervalは旧terminal blockerの下に全包含されるか、新blockerが旧blockerを厳密に越える
   - terminal blockerはcomb entryより前に初出し、減算起源ならそのpredecessorはentryより厳密に上

5. `TargetHighCandidateExcursion`, `TargetCombMacro`
   - signed excessは加算で`+n`、減算で`-(n+2)`だけ変化する
   - maximal high excursionの出口はlegal subtractionで、直前余剰は`0 < excess < finish+2`
   - 全prefixのstrict ledger corridorと、最初のlowで反転するfirst-passage不等式
   - 正のterminal blockerは「entryより上のpredecessorを持つ減算起源」または
     「より小さいpredecessorを持つforced-addition起源」の二択。後者は既存`EarlierSmaller` rankへ直結

4 は類似問題から移植した「妨害資源の有限消費」を、Recamánで初めて非自明なepisode単位に
実現したものである。

### 計算で強く支持される事実

- unrestricted interval Hall probe は 20,000,000 項まで sharp `C*=9`
- 唯一の最悪区間は `[2,6]`、demand `13`、subtraction mass `4`、subtraction count `1`
- 初期 release を除き `p ≥ 7` とした all-job tail interval は 5,000,000 項まで sharp `C*=3`
- tail 側の最悪例は `[16,18]`, `[111,113]`, `[1227,1229]` などの単一-job `-++` window
- `q ≥ 6 → G ≥ 0` は 1,000,000,000 項まで成立
- 追加のcausal probeでは1,000,000,000項まで最長加算runは6で、最初の区間は
  `[5026070,5026075]`。7連続加算は未観測
- 連続加算対が使うpredecessor-saturation sourceは1,000,000,000項まで同じ値の再利用が最大2。
  ただし異なるsourceを使えるため、これだけでは償却potentialにならない
- 最大加算runはvisited setの左隣を走査し、出口の減算で最初の未訪問左隣を埋める。さらに
  `subtraction, addition, addition, subtraction`は不可能なので、最大加算runの長さは1または3以上
- target-relative exact probeでは20,000,000項まで5,779,960個のlow state、2,661本のdescending
  comb episodeを観測。protocol違反は0、historical terminal blocker 2,660個のepisode間再利用は最大1
- 最長combは159,583個の連続fresh landingを持つ。terminal blocker 2,660個のうち2,657個は
  終端利用時まで出現回数1だが、このsingleton性は未証明であり主仮説にはしない
- 同じ20M scanの連続historical comb 2,655辺では、blocker下降2,635、上向きreset 20、等値0。
  fresh intervalが旧blockerを跨ぐ例は0
- terminal blocker 2,660個のうち減算起源は1,260。全件でpredecessorがcomb entryより上にあり、
  違反0、最小lift 37。20件の上向きresetはすべてforced-addition起源で、減算起源0
- high-to-low出口5,779,954件でsigned window違反0。ただし最小slackは1、最大window利用率は
  99.9999%で、一様な加法・比例marginは期待できない

これらは経験的事実であり証明ではない。とくに候補 `TailHall₃` は、証明できれば
`liminf a_n / n ≤ 3` という非自明な部分定理を与える見込みがある一方、permanent-above tail と
論理的に両立するため、単独では全域性を導かない。

### no-goとして確定した知見

- H6 の 21 residue class は、mod 4、parity、ledger、legal/forced 初出生成では一つも消えない。
- 21本すべてを満たす抽象 suffix が構成でき、local arithmetic だけでは blocker provenance を
  復元できない。
- static / free-history model は多数の局所不変量を満たしながら偽の blocker を生成できる。
- 欠けている情報は「履歴全体が同じ Recamán 遷移から共同生成された」という因果制約である。
- terminal blocker列の単純単調減少は偽で、20Mまでに20個の上向きresetがある。
- high excursionのendpoint総和は既存`ledger_interval_balance`の言い換えで、新しい大域不変量ではない。
- exit windowは整数slack 1まで実際に飽和するため、uniform marginを仮定する枝は停止する。

## 分岐の現在地

| 分岐 | 得られたもの | 直接証明の見込み | 判定 |
|---|---|---:|---|
| low-quotient tail minimum | `q≤1`, `G≥-1`, low coordinates | 15/100 | 直接枝停止、構造定理として保存 |
| tail interval Hall | 500万項で sharp `C=3` | 25/100 | 直接枝停止、部分定理候補 |
| H6 affine chord | 10億項の経験則と21-class no-go | 15/100 | 停止、反例ベンチとして保存 |
| generic blocker provenance | sharp `C=3` payment | 20/100 | noncanonical部分定理として保存 |
| arbitrary-history model | 局所条件の不十分性を可視化 | 20/100 | 戦略フィルタとして常設 |
| fixed budget / reset injection | 高再利用 blocker が破る | 5/100 | 棄却 |
| target-relative transition charging | interval-order二分法、first-passage corridor、reset origin二分法 | 55/100 | endpoint balance枝は停止、reset provenanceへ継続 |

## なぜ直接攻略を止めるのか

証明探索は次の funnel まで進んだ。

```text
least missing target
  → canonical permanent-above tail
  → least tail minimum
  → q ≤ 1, G ≥ -1
  → q = 0 または (q = 1 かつ r < target)
  → high-blocker branch は空
  → local ledger / congruence を増やしても大域矛盾が出ない
```

Hall側も同様である。

```text
blocker interval congestion
  → 初期例 [2,6] を分離
  → tail で sharp C=3 候補
  → liminf a_n/n ≤ 3 の見込み
  ↛ 固定 missing target との矛盾
```

つまり、現在の障害は計算量やLean実装量ではない。局所の符号列・合同類・ledger identity と、
履歴の大域的な因果生成を結ぶ数学が欠けている。

## 次の研究ロードマップ

### 0. target-relative transition charging

clock `n` の符号付き減算候補を整数上で `c_n = (a_(n-1):ℤ)-n` と置く。未出目標`m`について`c_n=m`が一度でも起これば
そのclockで`m`が選ばれるので、反例tailではこのlevelが常にjumpで飛び越される。

`χ_m(n)=1[c_n>m]`の`10→01→10→…`を、fresh landingが1ずつ下降する最大comb episodeへ圧縮する。
第1gateの有限消費は通過した。各episodeのlow railはfirst occurrenceの連続区間で、historical terminal
blocker `b`はfresh landing `b+1`に注入されるため一回しか終端資源になれない。

high-only excursionの第2gateも評価した。signed excessのstep則、全prefixのstrict corridor、出口windowは
Lean化できたが、endpoint総和は既存ledgerの望遠和であり、windowはslack 1まで飽和した。従って
「総balanceに一様余裕を足す」枝は停止する。

残った第3gateはupward resetのprovenanceである。時間順のepisodeは、次fresh interval全体が旧blockerより
下へ移る下降辺か、新blockerが旧blockerを越えるreset辺に限られる。reset blockerの初出が減算なら、
その生成元predecessorは新entryより上へstrict liftする。forced additionならpredecessorは新blockerより
strictに小さい。20Mのreset 20件は全て後者だった。次は「upward resetで減算起源が不可能」または
「subtraction liftを初出時刻下降と組にしたwell-founded macro rank」のどちらか一つだけを試す。

### 1. causal blocker graph / multiscale flow

forced addition の時刻から、その原因となった blocker の過去出現へ辺を張る。単純な単射は偽なので、
辺の再利用回数ではなく、時間差、値差、介在する reset、subtraction mass を複数スケールで償却する。

最初の成功条件は、実軌道でのみ成立し、free-history countermodel では破れる不等式を一つ得ること。

### 2. visited-set gap dynamics

個々の blocker ではなく、未訪問集合の gap の生成・移動・消滅を状態変数にする。permanent-above 仮定が
固定 target 周辺の gap flux にどんな一方向性を課すかを調べる。

最初の成功条件は、gap count または gap mass に target 非依存のdriftを得ること。

### 3. computational invariant synthesis

既存のexact probesを、候補不等式の発見・反例生成・holdout検証に使う。学習対象は時刻ごとの値ではなく、
causal graph と gap dynamics の局所特徴に限定する。

最初の成功条件は、既存ledger恒等式の線形結合ではない候補を発見し、別horizonで再現すること。

## 再開条件と停止規則

全域性の直接形式化を再開するのは、次のいずれかを紙上または独立計算で得たときだけとする。

1. permanent-above tail と linear height / positive subtraction density を矛盾させる定理
2. old blocker の無限再利用を一様に償却する定理
3. nonpositive reset を漏れなく同じpotentialへ組み込む定理
4. free-history model と実軌道を分離する causal invariant

逆に、次は再開理由にしない。

- 新しい outcome 型、certificate、rank wrapper の追加
- q / parity / mod 4 の追加有限分類
- fixed horizon のtrace、mex、replay拡張
- target出現と同値な仮説の言い換え
- 既存identityだけから自動的に出る評価

## 再現性

- Lean全体検証: `scripts/check.sh`
- 検証済み: 218 Lean jobs、993 audited declarations
- 監査済み公理: `{propext, Classical.choice, Quot.sound}` のみ
- 禁止事項: `sorry`, `admit`, `native_decide`, user axiom は0
- exact probes:
  - `experiments/blocker_interval_hall.cpp`
  - `experiments/blocker_interval_tail.cpp`
  - `experiments/target_transition_probe.cpp`

## 関連資料

- [証明ロードマップ](./ROADMAP.md)
- [研究ポートフォリオ](./RESEARCH_PORTFOLIO.md)
- [2026-08-30 並列監査](./PARALLEL_RESEARCH_2026-08-30.md)
- [Causal invariant sprint 1](./CAUSAL_INVARIANT_SPRINT_2026-08-30.md)
- [Causal run / gap sprint](./CAUSAL_RUN_GAP_SPRINT_2026-08-31.md)
- [類似 greedy 数列の文献レビュー](./LITERATURE_REVIEW_2026-08-31.md)
- [開発ログ](./DEVELOPMENT_LOG.md)
- [証明マップ](./PROOF_MAP.md)
