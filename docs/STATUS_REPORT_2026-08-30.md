# Recamán 全域性研究 — 現況レポート

> [!NOTE]
> 本書は2026-09-01までの説明的snapshotであり、現在状態の正本ではない。
> 最新のbranch statusと再開条件は[`CURRENT_FRONTIER.md`](CURRENT_FRONTIER.md)、
> 個々のclaimの証拠は[`EVIDENCE_REGISTRY.tsv`](EVIDENCE_REGISTRY.tsv)を参照する。

最終更新: 2026-09-01

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
- **exact residual kernel:** provenance監査済みのeventual-high corridorまたはfixed-root target-low unbounded terminal stream
- **reset repayment:** exact命題は未反証だが、独立causal bridgeが尽きたため15/100・`STOPPED`
- **A枝 fixed-seed supply:** exact無限no-goは`CONJECTURED`のまま。需要birth分類は
  `PROVED-LEAN`だが、subtraction ancestryの非閉包・parent merge・no strict driftにより
  現proof branchは`STOPPED`
- **periodic schedule:** balanced有限核は`PROVED-LEAN`、eventually-periodic floor+recurrenceの
  排除は`PROVED-PAPER`。非周期scheduleは未排除
- **canonical separator:** 決定的標準軌道の言い換えに退化し5/100で停止
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

その後のcanonical監査では、標準prefixを2Bまで伸ばした28件のupward resetがすべてright recordかつ
forced-addition初出だった。一方、terminal fresh interval由来は0/28で、blockerの26/28、birth candidateの
19/28は対象epoch中に新規生成されていた。さらに自由seedから実際の`Basic.step`を反復すると、target 5で
blocker `16→230`のright-record resetを作れ、230は`326−96`のlegal subtractionで初出する。
従って標準prefixの28/28則は局所macro/history則ではなくcanonical到達可能性固有であり、独立separatorなしには
Lean化しない。

Round 16では、このseparatorを先に仮定せずに残余を再構成した。tail後のfirst occurrenceは既存
`coverageStep_at`で全て処理できるため、有限pre-tail rootが全てterminal entryで左へescapeすれば
`CoverageOracle`からtarget occurrenceが出て矛盾する。従って仮想missing tailは固定finite no-escape rootを持つ。
さらにlow candidateのbounded/unboundedで、eventual-high corridorまたはそのrootの右側を走るunbounded terminal
streamへLeanでexactに二分した。

Round 17では、このB枝の型を意味論的に再監査した。構築時には分かっていたtarget-low start、start clockの
非有界性、全future terminalに対するuniversal fixed-root no-escapeが結論型で失われていたため、三点を
`UnboundedRightTerminalStream`へ戻した。さらにleast later low clockを選ぶことで、任意のtarget-low terminal
からconsecutive `TargetMacroSuccessor`を構成できることをLeanで証明した。

一方、reset repaymentを有限鳩の巣へ落とす最弱候補「返済前の全blockerはreset開始前に初出済み」は、
seeded exact greedy continuationで偽だった。reset `6→14`の後、entryが14未満へ戻る前にblocker 199が
clock 65のforced additionで新規生成される。永久欠落を加えた修正版は返済またはtarget出現の言い換えに
なる。従ってexact repayment自体は`CONJECTURED`のままだが、研究枝は`STOPPED`とした。詳細は
[Round 17 reset-repayment audit](./RESET_REPAYMENT_AUDIT_2026-09-01.md)を参照。

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
   - 任意二つの時間順combのfresh intervalは値軸上で完全に分離・全順序化される
   - terminal blockerはcomb entryより前に初出し、減算起源ならそのpredecessorはentryより厳密に上

5. `TargetHighCandidateExcursion`, `TargetCombMacro`
   - signed excessは加算で`+n`、減算で`-(n+2)`だけ変化する
   - maximal high excursionの出口はlegal subtractionで、直前余剰は`0 < excess < finish+2`
   - 全prefixのstrict ledger corridorと、最初のlowで反転するfirst-passage不等式
   - 正のterminal blockerは「entryより上のpredecessorを持つ減算起源」または
     「より小さいpredecessorを持つforced-addition起源」の二択。後者は既存`EarlierSmaller` rankへ直結

4 は類似問題から移植した「妨害資源の有限消費」を、Recamánで初めて非自明なepisode単位に
実現したものである。

6. `TargetTailResidualKernel`
   - finite `PreTailCoverageOracle`からglobal `CoverageOracle`へ直接接続
   - 全pre-tail rootのterminal escapeはtarget missingと矛盾
   - 全future terminal entryが右側に残る固定pre-tail rootを抽出
   - 仮想missing tailを`EventualHighCandidateTail`または`UnboundedRightTerminalStream`へexactに二分
   - right-streamはuniversal no-escape、任意に遅いtarget-low startを保持
   - least later lowの選択からconsecutive `TargetMacroSuccessor`を構成

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
- 幅広macro監査ではupward ancestry最大60,651 hop、edge再利用7で、短い／一回消費genealogyを棄却。
  interval移動もupward最大2,237本、downward最大71本の既存intervalを飛び越え、stack traversalではない
- upward reset 20件は全て過去全fresh intervalより右のglobal record。record gap mass 17,820,564のうち
  reset時未訪問14,775,263、20Mでも未訪問9,518,181。right-record則は未証明
- 2Bまでのupward reset 28件はすべてglobal right recordかつforced-addition初出。ただしterminal fresh
  interval由来は0/28で、tail内の新規candidate生成を有限課金できない
- 各terminal blocker自身をanchorにした2B監査では21,510件中21,495件が後続entryでstrictに下へ戻る。
  upward reset 28件中26件は次terminalで即時return、残る2件はtarget 4の実出現でepoch終了
- record時未訪問だった200k gap cohortは20Mまでに99.88%、2M cohortは20Mまでに92.06%が後から初出

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
- seeded actual orbitではupward right-record blockerがlegal subtractionで初出する。従って標準prefixの
  addition-origin則をlocal legalityから導く枝は停止する。
- recurrence burstからのlocal `sqrt(6m)` use-gapは偽。「3連以上」を「ちょうど3連」と
  読んでおり、exact seeded `Basic.step`の`m=120 → n=141`で`21²<6·120`。
  `A^(q+1)S^q`族は`gap²/m→4`で、local gap形式化は`STOPPED`。
- subtraction-born supplier ancestryは閉じない。forced use 42はlegal birth clock 20へ戻り、
  distinct children 151/135はparent 261へmergeすることをLean認証。generic ancestry課金も停止する。
- 一つの固定有限seedが内部供給需要つきcandidate 20をclocks 94/286/862の3回まで支える。
  従ってraw demand countによる小さな一様boundは偽。4回目・無限streamは未発見で、これは
  `COMPUTED`有限反例に限る。

## 分岐の現在地

| 分岐 | 得られたもの | 直接証明の見込み | 判定 |
|---|---|---:|---|
| low-quotient tail minimum | `q≤1`, `G≥-1`, low coordinates | 15/100 | 直接枝停止、構造定理として保存 |
| tail interval Hall | 500万項で sharp `C=3` | 25/100 | 直接枝停止、部分定理候補 |
| H6 affine chord | 10億項の経験則と21-class no-go | 15/100 | 停止、反例ベンチとして保存 |
| generic blocker provenance | sharp `C=3` payment | 20/100 | noncanonical部分定理として保存 |
| arbitrary-history model | 局所条件の不十分性を可視化 | 20/100 | 戦略フィルタとして常設 |
| fixed budget / reset injection | 高再利用 blocker が破る | 5/100 | 棄却 |
| residual kernel decomposition | provenanceを保持したA/B二分とsuccessor選択 | 85/100 | architectureとして確定 |
| finite-root/right-terminal no-escape | universal fixed-root target-low streamまでLean化 | 30/100 | 独立residualとして保存 |
| upward reset repayment | exact命題は未反証、local preloadはseeded反例 | 15/100 | `STOPPED`、新global invariant待ち |
| record-gap future consumption | old cohortを20Mで92--99.88%消費 | 20/100 | 診断のみ |
| canonical reachability separator | exact continuationは決定的一意 | 5/100 | 言い換えとして停止 |
| fixed-seed burst supply | demand birth分類、3-use exact seed、ancestry反例 | 10/100 | 命題は`CONJECTURED`、現枝`STOPPED` |
| periodic candidate no-go | finite `-p²` Lean核＋全体paper proof | 70/100 | regression theoremとして保存 |

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

exact residual kernelの型監査とB枝の一回限りのreset-repayment探索は完了した。

1. eventual-high corridorは12/100で保留する。arbitrary finite seeded high corridorが満たせない独立canonical入力が
   紙上で得られるまでLean拡張しない。
2. reset repaymentは15/100・`STOPPED`。post-reset blocker birthを、future return・target occurrence・canonical
   reachabilityを使わずに有限化するglobal invariantが先に得られた場合だけ再開する。
3. residual kernelとsuccessor selectorは、今後別アプローチを接続するための監査済みhandoff theoremとして保守する。

canonical separator、terminal fresh-certificate課金、local addition-origin prohibition、fixed-history preloadは終了した。

以下のtarget-relative各段階は、この停止判断までに評価した履歴である。

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

その後の幅広監査で、任意二episodeのfresh interval全順序をLean化した一方、bounded ancestryとstack traversalを
具体的に棄却した。upward 20件が全てglobal right recordだったため、次はこのrecord則をactual provenanceから
導けるかだけを先に試す。通った場合も、それ単独では不十分なのでrecord gapとhigh predecessor reservoirの
二成分fluxにstrict driftが出たときだけdirect branchを再評価する。詳細は
[macro幅広探索](./BROADENED_MACRO_EXPLORATION_2026-08-31.md)に記録した。

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

1. eventual-high corridorを直接排除するcanonical不変量
2. upward resetに`target occurs ∨ later entry < blocker`を与えるcausal lemma
3. right-ladder countermodelを破り、target occurrenceを仮定しないglobal constraint
4. gap backlogの増加をpermanent missingと矛盾させる非循環なflux定理

逆に、次は再開理由にしない。

- 新しい outcome 型、certificate、rank wrapper の追加
- q / parity / mod 4 の追加有限分類
- fixed horizon のtrace、mex、canonical replay拡張
- fresh tokenやrecord-gap係数の再包装
- target出現と同値な仮説の言い換え
- 既存identityだけから自動的に出る評価

## 再現性

- Lean全体検証: `scripts/check.sh`
- 検証済み: 245 Lean jobs、1,130 audited declarations
- 監査済み公理: `{propext, Classical.choice, Quot.sound}` のみ
- 禁止事項: `sorry`, `admit`, `native_decide`, user axiom は0
- exact probes:
  - `experiments/blocker_interval_hall.cpp`
  - `experiments/blocker_interval_tail.cpp`
  - `experiments/target_transition_probe.cpp`
  - `experiments/target_upward_provenance_probe.cpp`
  - `experiments/seeded_right_record_search.cpp --walk-record-sub`

## 関連資料

- [証明ロードマップ](./ROADMAP.md)
- [研究ポートフォリオ](./RESEARCH_PORTFOLIO.md)
- [2026-08-30 並列監査](./PARALLEL_RESEARCH_2026-08-30.md)
- [Causal invariant sprint 1](./CAUSAL_INVARIANT_SPRINT_2026-08-30.md)
- [Causal run / gap sprint](./CAUSAL_RUN_GAP_SPRINT_2026-08-31.md)
- [Right-record計算監査](./RIGHT_RECORD_COMPUTATIONAL_AUDIT_2026-08-31.md)
- [Round 16 residual decomposition](./PARALLEL_RESIDUAL_DECOMPOSITION_2026-09-01.md)
- [Round 17 reset-repayment audit](./RESET_REPAYMENT_AUDIT_2026-09-01.md)
- [類似 greedy 数列の文献レビュー](./LITERATURE_REVIEW_2026-08-31.md)
- [開発ログ](./DEVELOPMENT_LOG.md)
- [証明マップ](./PROOF_MAP.md)
