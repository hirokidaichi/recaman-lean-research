# Changelog

## Cone excursion census — 2026-09-02

- `experiments/cone_excursion_probe.cpp`: burst use後のstrict-high excursionは全1,252,246件で倍化clock前に
  崩れ（m ≥ 100で`t/m ≤ 1.098`）、preload-free orbitのcone-exterior run約85M本は開始clockの2倍へ届かない
  （registry `E-022`）。excursion boundを独立部分命題`E-023`（`CONJECTURED`）として登録
- 意味監査：strict-high条件はcorridorの固定target床より強く、`E-021`/`E-023`はcorridor streamを排除しない。
  今後のfixed-seed／preload-free unitはuse間条件を固定床型で再定義する

## Preload-free orbit supply census — 2026-09-02

- `H-20260902-04`: 単一初期値のgeneralized orbit（history `{v0}`、exact `Basic.step`）を
  `experiments/generalized_orbit_supply_probe.cpp`で走査。`v0 = 0`はfalsifierのcanonical scanを再現
- 20,001 orbit・内部供給burst use 1,272,765件でstrict-high same-candidate linkは0件、全orbitのchainは1。
  凍結命題H-G3は未反証（`COMPUTED`、registry `E-020`）
- exact命題「generalized orbitにstrict-high linkは存在しない」を`CONJECTURED`（`E-021`）として登録。
  許可されるformalization routeは紙上証明のみ

## Admissible seed density check — 2026-09-02

- `H-20260902-03`: kernel認証済みのhistory density invariant（`valuesThrough_length`, `a_le_upperTri`）を
  `fixed_seed_supply_falsifier`の第3引数`1`で合成seedへ課した。引数なしの出力は2026-09-01記録と
  byte-identical
- 凍結protocolのexact seedは全深度でcanonical densityに違反し、admissible seedは0件（最小超過4値）。
  history densityを再開条件3の最初の拘束的候補として登録（registry `E-019`）

## Window demand provenance falsification — 2026-09-02

- `H-20260902-02`: 異candidate・dyadic window集約の`E ∩ S` collision、減算初出需要の`2t < w`、
  加算初出需要の`2b < w`の3命題を凍結し、`experiments/window_demand_provenance_probe.cpp`で
  canonical 2M/20Mを検査。3命題ともdiscoveryで`REFUTED`
- 20Mまで適用window 17件すべてで`E ∩ S = ∅`。collision型のdebt設計は同一candidate形・集約形とも閉鎖
- 減算初出需要はnear-diagonal（`2t ≥ w`）が多数派、加算初出需要はtruncated birthが約3割であることを
  `COMPUTED`として記録し、`CURRENT_FRONTIER.md`の再開条件1・3を更新（registry `E-016`, `E-017`）
- 最小証人（clock 5のtruncated加算初出、clock 112のnear-diagonal減算初出）を
  `DemandProvenanceCounterexample`でkernel認証（registry `E-018`）。247モジュール、249 jobs

## External blocker collision epoch — 2026-09-02

- `H-20260902-01`: 同一candidateの4回／8回supplied useでの`E_c ∩ S_c ≠ ∅`を凍結し、
  `experiments/external_blocker_collision_probe.cpp`で検査。20Mまで4回use候補が0で評価母集団が空、
  設計を`STOPPED`（registry `E-015`）

## Foundation definition ownership refactor — 2026-09-01

- 23 moduleで共有する`nextSubtractionCandidate`をL3の`TargetCandidateTransitions`から
  L0の`Basic`へ移動。完全修飾名`Recaman.nextSubtractionCandidate`と全statementは不変
- `SupplyAncestryCounterexample`の唯一のdirect importを`History`まで下げ、project dependency
  closureを旧169／暫定82 moduleから5 moduleへ縮小
- module import contractとarchitecture文書を新しいownershipへ同期

## Lean module architecture refactor — 2026-09-01

- root closure、project import解決、重複・self import、acyclic性を検査する
  `scripts/check_module_architecture.sh`を追加し、full checkへ統合
- 最近のfrontier 4 moduleのdirect importを`docs/MODULE_IMPORT_CONTRACTS.tsv`へ固定
- `SupplyAncestryCounterexample`の依存を未使用の`HighCandidateCausalReuse`から
  定義元`TargetCandidateTransitions`へ下げ、`PeriodicCandidateNoGo`の不要な`Std` importを削除
- entry point、依存層、変更規約を`docs/MODULE_ARCHITECTURE.md`へ分離

## Research information architecture refactor — 2026-09-01

- `docs/CURRENT_FRONTIER.md`をcurrent branch statusと再開gateの唯一の正本として新設
- frontier-changing claim 14件を`docs/EVIDENCE_REGISTRY.tsv`へ正規化
- `PROVED-LEAN` rowのAudit symbol、artifact、frontier参照、証拠labelを検査する
  `scripts/check_research_registry.sh`を追加し、`scripts/check.sh`へ統合
- README、STATUS、ROADMAP、PROOF_MAP、RESEARCH_PORTFOLIO、RESEARCH_REPORT、
  DEVELOPMENT_LOGの役割をcurrent truth／dependency atlas／historical snapshot／append-only logへ分離
- exact命題の`CONJECTURED`と、証明ルートの`STOPPED`を別registry rowとして保持する運用を固定

## Sharp residual kernel sprint — 2026-09-01 午後

- B枝: separator rootが全terminal blockerの床であることを証明（`TargetStreamBlockerUnbounded.blocker_floor`）
- B枝: `Classical.choose`の時系列chainとone-use鳩の巣で、streamのblocker/entryが任意の天井を超えることを証明
- B枝: consecutive macro pairのblocker降下をstrong inductionで停止させ、任意cutoff後のupward blocker resetを強制（`TargetStreamUpwardResets`）。大域kernelを「corridor ∨ 無限upward reset」へ精密化
- A枝: canonical軌道が永久のforced addition rayを続けられないことを無条件で証明（`no_perpetual_forcedAddition_ray`）
- A枝: corridorがclock超えのfresh着地とforced additionをともに無限個強制すること、corridor value law、および自給自足供給窓（`corridor_forcedAddition_supplier`）を証明
- 無条件: 合法減算直後の加算2連は3連を強制し、長さ2の加算runが存在しないことを証明（`NoDoubleAdditionRun`）。10億項probeのhistogram（長さ2が0件）と一致
- 両枝の精密化を`SharpCorridor`／`SharpResetStream`へ束ねる`SharpResidualKernel`を追加
- A枝: 供給者を候補値の初出へ強化し、birthステップを「取られた減算」か「加算出力」へ無条件二分（`EventualHighCorridorBirth`）
- A枝: **第二の永久欠損値の強制**を証明——履歴の1時刻1値計数と、corridor value lawによる窓凍結から、欠損値はtargetだけではない（`EventualHighCorridorSecondMissing`）
- A枝: 再訪候補のrigid event（入りは対角fresh減算・出はforced addition・後続値は既訪問強制）と有界再訪からの単一再訪値抽出を証明（`EventualHighCorridorRecurrence`）
- A枝capstone: candidate walkの「発散 ∨ 最小再訪候補でのrigid event stream」二分定理を証明。床は最小性＋帯回避境界から構成（`EventualHighCorridorDichotomy`）
- 発散枝の代償: candidate床は下の値窓を凍結するので、発散walkは任意の限界超えの永久欠損値を残す。A枝最終形は「欠損値非有界 ∨ rigid event stream」（`DivergentCandidateMissing`）
- 紙上分析: A枝を「candidate walk発散 ∨ 最小再訪候補のrigid recurrence」へ縮約（`docs/CORRIDOR_SUPPLY_ANALYSIS_2026-09-01.md`）。B枝のblocker birth分類からは非自由入力が出ず、B枝はGate 3〜5形式化の成果で保存
- 1e9 exact probe `corridor_structure_probe.cpp`を追加: 加算run長最大6、cone-exterior率~43%定常、low-candidate regimeは希薄化しつつ毎decade再入、mexは1355で1e6〜1e9凍結
- 日本語human-proofレポートを新モジュール分追加し、viewer manifestを更新

## Reset-repayment semantic audit — 2026-09-01

- `UnboundedRightTerminalStream`を強化し、universal fixed-root no-escape、任意に遅いterminal start、target-low provenanceを同時に保持
- least later low clockからconsecutive `TargetMacroSuccessor`を構成する定理をLean化
- fixed-history blocker preloadが返済を含意する有限鳩の巣縮約を紙上で確定
- exact greedy seeded continuationでreset後に新blockerが生成される反例を固定し、local preloadとimmediate repaymentを停止
- discovery/holdoutを分けた`target_reset_repayment_probe.rb`と明示seed replayを追加
- exact repaymentは未反証のまま`STOPPED`とし、有望度を40/100から15/100へ更新

## Missing-tail residual kernel and parallel decomposition — 2026-09-01

- finite-root no-escapeを6段へ分解し、terminal stream、fixed-root separator、finite packing、unbounded hull、infinite resetまでは既存APIから到達可能と整理
- `TargetTailResidualKernel`を追加し、finite pre-tail oracleからglobal `CoverageOracle`へ直接接続
- 任意の仮想missing tailから、全future terminal entryが左へ越えられない固定pre-tail rootをLeanで抽出
- 仮想反例をeventual-high candidate corridorまたはfixed-root unbounded right-terminal streamへexactに二分
- terminal-anchor監査を2Bへ拡張し、21,510件中21,495件が後続entryでstrict return、upward reset 28件中26件が次terminalで返済されることを確認
- record-gap cohortのfuture consumptionを追加監査。200k cohortは20Mまでに99.88%、2M cohortは20Mまでに92.06%を消費
- canonical clock-4/kernel separator候補が決定的標準軌道の言い換えに退化すると判定し、separator枝を5/100へ下げて停止
- finite-root/right-streamを30/100、reset repaymentを40/100へ再採点し、詳細を`docs/PARALLEL_RESIDUAL_DECOMPOSITION_2026-09-01.md`へ記録

## Canonical upward-provenance audit — 2026-09-01

- same-target upward terminal resetを2Bまで専用監査し、28/28がterminal right recordかつforced-addition初出であることを確認
- blocker birth candidateは再利用最大1だが、19/28がtarget epoch内生成、terminal fresh interval由来0/28であるためfinite fresh-certificate課金を停止
- ancestry pathは最大1,064,446 edge、subtraction edge最大532,214、pre-epoch root再利用最大8まで増え、単純addition genealogyではないことを確認
- arbitrary signed-walk seedから続く実step orbitで、upward terminal right recordがlegal-subtraction初出になる反例を発見。local macro/history則からaddition-originを導く枝を停止
- canonical generation-vs-reuse chronologyの直接有望度を30/100から20/100へ下げ、標準prefix reachabilityを本質的に使う新不変量がない限りLean化しない方針へ更新

## Two-hour low/terminal and finite-basin audit — 2026-09-01

- 各tail low candidateから有限 maximal fresh comb とhistorical terminal blockerを抽出する一連の定理をLean化
- terminal blockerのhistorical normalをextended/refined/semantic domainへmountし、later-entry-leftとceiling超resetをstrict progressへ接続
- finite historical anchorについて`semantic progress ∨ anchor ≤ future blocker`を証明
- interval order・blocker one-use・unboundednessだけではfinite basinを脱出できないright-ladder countermodelをLean認証し、macro/interval direct branchを停止
- positive forced candidateのearlier `FirstAt` mapとsame-candidate output strictnessを証明する一方、same-candidate reuse・nonfresh output・distinct-candidate output collisionをLean反例で認証
- 20M low-to-terminal extraction probeと2M high-candidate reuse probeで、局所adapterを検証しraw causal chargingを棄却
- terminal fresh intervalの幅`entry-blocker=k+1`とclock durationのexact関係、二episode版fresh-mass hull boundをLean化
- singleton right ladderに5-clock gapを導いたが、gap/parityを満たす無限scheduleもLean化し、clock sparsity単独を停止
- fresh entryが介在episode後にterminal blockerへ戻るtarget-4標準prefix反例をLean認証。候補をimmediate `TargetMacroSuccessor` gated no-returnへ縮約
- same-candidate reuse intervalのexact subtraction balanceをLean化し、5重overlap反例と増大するhigh-block overlapで集約枝を停止
- entry-return residualをhigh-word内のforced reuse balanceまたは全区間avoidanceへLeanで完全二分し、現行causal APIだけのsuccessor no-return枝を停止
- immediate successor slackを20Mで監査し、entry returnのparity compatibilityをLean化。`δ odd ∨ next fresh mass≤δ`の新規残余は4辺だけで共通機構がなく、過適合寄りとして停止
- 任意有限長のhigh forced-addition corridorを実`Basic.step`上のseeded historyからLean構成し、局所符号・ledger・parity・history legalityによるuniform boundをno-go化
- 詳細な停止判断と次のgateを`docs/TWO_HOUR_RESEARCH_REPORT_2026-09-01.md`に集約

## Broadened target-comb macro exploration — 2026-08-31

- 任意二つの時間順history-terminated combのfresh intervalが値軸上で完全に分離する`fresh_intervals_ordered`を証明
- 20M reset ancestryを追加監査。最大60,651 hop、ancestry edge再利用7、threshold-crossing edge再利用4のため、bounded/unique ancestry chargingを停止
- upward reset 20件は全てglobal right recordだが、17件は既存intervalを飛び越え最大2,237本を跨ぐ。単純stack traversalを棄却
- record gap mass 17,820,564のうちreset時未訪問14,775,263、20M時点でも未訪問9,518,181。fresh intervalだけの閉じた収支を停止
- 次の限定枝をglobal right-record則のprovenance証明と、record gap/high predecessor reservoirの二成分fluxへ更新

## Target-comb macro excursion and reset provenance — 2026-08-31

- 時間順のhistory-terminated combについて、次fresh intervalが旧blockerより完全に下へ移るか、新blockerが旧blockerをstrictに越えるinterval-order二分法を証明
- terminal blockerがcomb entryより前の履歴にあること、減算起源なら生成元predecessorがentryより上へstrict liftすることを証明
- signed target-candidate excessのexact step則、high excursionのprefix ledger corridor、legal-subtraction出口、sharp exit windowをLean化（`TargetHighCandidateExcursion`）
- 正のterminal blockerを、older high predecessorを持つ減算起源またはstrictly smaller predecessorを持つforced-addition起源へ完全分類（`TargetCombMacro`）
- 20M macro scanで2,655辺を監査。blocker下降2,635、上向きreset 20、separator違反0。resetは全てaddition起源でsubtraction起源0
- endpoint総和は既存ledgerの望遠和、exit windowはslack 1まで飽和するため、uniform-margin枝を停止。次gateをupward-reset provenance rankへ限定

## Target-relative comb charging — 2026-08-31

- permanent-above tailでbelow-target subtraction candidateがforced additionを起こし、missing仮定下で次candidateがstrict highへ戻ることを証明
- high-to-low transition後のdescending combを既存`CombRun`へ接続
- fresh combの全low railがfirst occurrenceで、時間的に別のepisodeのrailが互いに素であることを証明
- historical terminal blockerをfinal fresh successorへ注入し、異なる完了時刻での再利用を排除
- `target_transition_probe.cpp`を追加。2,000万項で2,661 episode、最長159,583 fresh landings、protocol違反0
- 次の残余をcomb間high-only excursionのclock重み付き二側balanceへ限定

## Low-quotient ledger checkpoint and research branch selection — 2026-08-30

- least missing targetの最小tail minimumを`q≤1`, `G≥-1`とsharp ledger corridorへ置く定理を追加（`LeastTailLedgerMinimum`）
- 一般低商minimumをbounded branchまたはearlier blockerへ分解し、ledger payment・historical outcomeへ接続（`LeastTailLedgerProvenance`）
- canonical least-missing witnessではhigh blocker枝が空で、`q=0 ∨ (q=1 ∧ r<target)`まで縮むことを追加監査・形式化
- positive earlier occurrenceの3-clock gap、exact interval ledger、sharp単一job`C=3` paymentを証明
- positive blocker interval Hall条件のexact probeを追加。2,000万項まで必要最小定数`C_H^*=9`、最悪区間`[2,6]`
- tail restriction probeを追加。500万項まで`p≥7`のall-job Hall定数はsharpに`C=3`、brute-force regression付き
- H6の全21合同類を生存させる一様抽象suffixを構成し、mod 4/parityによる独立攻略を停止
- `TailHall₃`が含意する`liminf a_n/n≤3`はpermanent-above性と両立するため、全域性の直接攻略を停止し部分定理へ移管

## Least-tail canonicalisation and authenticated deep boundaries — 2026-08-29 (深夜)

- permanent-above tailの最小開始時刻を証明書の正準点に選び、coverage境界が`tailStart = coverage + 1`を満たすことを証明（`LeastTailDischarge`）
- 正準境界のanchor比較でexact replayの等号固定点を矛盾にし、well-foundedなdischarge反復からreplay分岐を完全除去
- 最小未出目標の頂点定理を、固定点床なしの「strict history progressまたはcertificate付き`RefinedSemanticEdge`」に縮約
- 最小tail境界の新規low、入射減算、三段の強制加算、直前の欠損budget 1をsource-free certificateとして抽出
- canonical境界時点のbudget 0、直前budget 1、valley equation、permanent-above性から完全な`TerminalHistoryCursor`を構成し、`TerminalChronologyHistoryProgress target coverage (coverage-1)`を無条件化
- canonical lowをfresh landing、同clockを即時first upcrossingとして、history edgeを`PermanentTailTerminalAnchoredOutcome`へ直接搭載
- 同じlanding payloadをcertificate-preservingな`RefinedTerminalAnchoredOutcome`へも直接搭載
- source-preserving `BoundaryCertificate`から元combined parentのready crossingを保つ`RefinedTerminalMountedOutcome.landing_crossing`を構成し、least-tail summitまで伝播
- mounted landingと`BoundaryRankOutcome`を同一canonical boundary上で束ね、summitへ同梱
- balanced trace checkerを深部ソースに対応させ、`a 99734 = 19`と`a 181653 = 61`をLean kernelで認証。最小未出目標に`62 ≤ target`、境界lowに`61 ≤ low`を導出
- balanced treeの成功実行から右端leafの認証checkpointを抽出する汎用APIを追加。61traceの最後10更新を逆算し、別traceを再チェックせず`a 181643 = 76`を証明
- 62〜75の初出がclock 99以内であることをkernel検証し、最小未出目標を`77 ≤ target`へ強化。境界lowは`(coverage, low) = (181653, 61)`または`76 ≤ low`
- balanced trace終端のmexを認証する汎用APIを追加し、clock 181653で0〜878が全て既出・879が未出であることをkernel検証。最小未出目標を`879 ≤ target`へ強化
- 61traceの右端leafをさらに分割して`a 181651 = 363366`、`a 181652 = 181714`と直前減算を証明。唯一のsub-76境界を`target=879`かつ二連続fresh減算の完全固定high枝へpin
- mexの全既出情報とpermanent-above性を合成し、唯一のsub-879境界も同じ固定例外であることを証明。無条件境界分岐を固定例外または`879 ≤ boundaryLow`へ強化
- canonical境界上で固定例外証明書と`target=879`の同値を証明。鋭い無条件summitを「完全固定879例外または`880 ≤ target ∧ 879 ≤ boundaryLow`」へ整理
- `boundaryLow ≥ 879`を後方valley反復へ接続し、非例外枝の879段版（depth<879のhigh／`coverage ≤ low+2637`／budget 880のdepth-879 valley）を証明
- finite chainの到達枝を任意low床からtarget床へ移す一般補題を追加。879段到達なら`1759 ≤ target`
- 正depthの後方stageからcanonical境界cursorへの厳密な`TerminalHistoryBudgetDrop`を証明。879段到達枝を既存のwell-founded履歴関係へ直接接続
- 任意のboundary low床を最大room三択へ移す一般補題を追加。floor 879の非例外枝では終端比率枝が`1758 ≤ target`
- 任意の879出現証明から固定例外を消し、`880 ≤ target`・`879 ≤ boundaryLow`へ直結する条件付きsummitを証明。次の有限認証義務を経験的等式`a 328002 = 879`の一点へ分離
- 正準境界を一段後方へ解析し、「二連続の初出減算着地／`target`と`coverage`の6通りの狭い配置／欠損budget 2を持つ先行valley」の完全分類を証明（`LeastTailBoundaryBackward`）
- 後方valleyを深さ`d`へ反復し、高い減算前値またはclock/low接近が現れない限り、lowは`d`、欠損budgetは`d+1`へ増える鏖を証明。反復roomは正確に`low + coverage - target`で、深部low下界から61段版も導出（`LeastTailBackwardChain`）
- 最大roomの終端stageを数倬freeに読み替え、後方鏖をhigh減算枝、実depth付きnarrow枝、`coverage + 2*low ≤ 2*target`枝の鋭い三択へ圧縮
- 全射性自体は依然未証明。canonical edgeはrefined mountedまで到達したが、その特定landing枝のstrict mounted progress化と等anchor残余の閉包が残る

## Refined summit and structural walls — 2026-08-29 (夕方)

- 頂点定理のsemantic枝が`0 < target`だけから導出でき**情報量ゼロ**だったことを形式的に暴露（`semantic_or_flooredCore_of_pos`）
- 忘却形`RefinedDomainEdge`も`0 < target`から直接導出可能と判明（`probe_refinedDomainEdge_of_pos`）。伝播ペイロードは生成証明書を保持する形へ設計変更
- `blockedFirstOccurrence_impossible_of_regeneration`の仮定が実軌道で偽（`BlockedFirstOccurrence 13 6`）と判明し、「残余義務を型で固定」という位置づけを撤回
- semantic枝のpayloadを捏造不能な形へ強化し（`RefinedSemanticOutcome`）、頂点まで全8段を伝播（`RefinedFixedPointCore`）
- 新左枝の非自明性を証明：`RefinedSemanticEdge`はpermanent-tail証明書を保持するので`¬∃t, a t = target`を単独で含み、`target = 1`で反証できる
- 左枝の`mounted_crossing`経路が`LeastMissingTarget`から無料で出ないことを`installReadyCrossing`によるanchorの無限降下で証明
- 左枝から`TargetTailReturnHypothesis`と`CrossingRefinedStepHypothesis`の両方が反証されることを証明。両枝は同一の一点へ収束する
- landing前置界を`TerminalChronologyHistoryProgress`のsource-freeな強化（`TerminalHistoryCursor`）として輸送し、頂点の固定点枝の床を無条件`32 ≤ clock`・`19 ≤ target`へ（旧`18 ≤ clock ∨ target = 19`）
- crossing readiness橋を無仮定で完成させ、大域残余を`0 < target ∧ TargetTailReturnHypothesis target ⟹ 出現`の一本へ純化（同仮定は全射性と同値であることも明示）
- unready crossingのliteralな非存在は証明不能と確定（target 12の具体反例）。残余は到達不能性でしか閉じない
- `coveredBelowCount`（`missingBelowCount`の補数）と鳩の巣で無条件`target < tailStart`を証明。kernel計算ゼロ
- `tailStart`に上界が存在しないことを構造的に証明（`MissingStrictAboveTail`の全フィールドと証明書のhorizon条件がすべて上方閉）
- validなtail startの最小元を有界帰納法で取り、両側評価`target ≤ least ≤ bound + 1`を既存モジュール無編集で達成。残る自由度はcoverage timeの上界ひとつ
- pinned配置の後方2ステップを完全決定し、混合形2通り（189件・88件）を排除。残りは「両方減算」「両方加算」の二択
- 床上げ機構に構造的天井`clock ≈ 5.4×10⁴`を数値的に確定。kernel射程を無限に伸ばしてもclock 10⁶までの65%は消せない。深部検証への追加投資を打ち切り
- 敵対的健全性監査を実施（`docs/SOUNDNESS_AUDIT.md`）。偽の定理・`sorry`・隠れ公理はゼロ、数値アンカー96件が独立計算と一致。docsの過大主張を訂正
- `scripts/check.sh`に公理集合のassertを追加（従来は印字のみで検証していなかった）
- 本日追加の15モジュールについて日本語証明レポートを整備し、`viewer/`を追跡対象に追加

## Landing recursion and fixed point floors — 2026-08-29

- history edgeのfresh landingにhorizon境界（landing<start、crossing+1≤start<horizon）を事後導出
- 境界付きlandingをready crossing nodeとしてsemantic domainへ搭載
- combined certificateをmounted nodeへtransportし、terminal解析をlanding枝から再入可能化
- landing再入反復をanchor gap強帰納で整礎閉包し、残余をnode不動landing固定点へ縮約
- 二固定点の共通核`TailFixedPointCore`と最終統合定理`unifiedOutcome`を構成
- 統合coreにblocker不要のkernel floor（clock≥6・target≤upperTri包絡）を証明
- replay floorをclock 17まで拡張：例外は深い遅延値19のみ、`18≤clock∨target=19`と無条件`target≥19`
- replay固定点候補の数値走査実験を追加：10¹⁰項でも5,640対が生存、decide全域排除戦略の不成立を定量確認
- 固定点coreの形状API（parent一意決定・同値crossing・異clock同値再帰）を追加
- first upcrossing一般all-below補題で両固定点のbelow corridorを統一
- 統合coreの床もclock 18・target 19へ拡張し、両固定点の床を完全一致
- 最小未出目標からの頂点定理：semantic childまたは床付き固定点core
- `LeastMissingTarget 19 ↔ 19未出`を形式化し、最初の未検証instanceを一値へ確定
- replay床をclock 32へ拡張し、targetを`19∨61∨34以上`へ三分（例外リスト{19,61}、次の壁76）
- comb run閉形式・witness構成・値集合表現・freshness輸送を証明し、圧縮軌道検証の機構を整備
- target 19のreplayをclock 8の唯一cycle（downcross 7→即時return 8・anchor 12・blocker 3初出2）へ完全特定
- 19-反例のtail最小値を21へ固定し、tailStart>131・horizon>132で固定歴史と未知tailへ二分
- 19未出⟹21の遅い再訪、という将来イベント強制を証明
- 既出値の遅い再訪不可能性（一般力学補題`a_succ_ne_of_seen`）でtarget 19のreplayを完全排除
- 無条件`18 ≤ clock`・`32 ≤ clock ∨ target = 61`・`20 ≤ target`へ床を更新
- 同機構でtarget 61のreplayも完全排除（59分岐の全消去）、無条件`32 ≤ clock`・`34 ≤ target`へ確定
- 排除機構を一般テンプレート化し、生存replayのpredecessor直後を即add／二連subへ制限
- replay crossingのrecord性排除を証明し、三種道具の反復でdischarge replay枝の床を無条件`112 ≤ clock`・`114 ≤ target`へ拡張（landing固定点枝の床は据え置き）
- prefix-successor coverageを一般化し、later low witnessとprefix successor既出性からreplayを一括排除するinterval floor theoremを証明
- clock 112の唯一のuncovered successorを371へ固定し、minimum=371・predecessor初出108・downcross 109・`152 < target ≤ 261`まで数値pin
- coverage frontier監査ツールを追加。cutoff 99734の経験的な次の未被覆eligible clockは777（successor 879、初出328002）
- `PermanentAboveCorridorLandingHorizon`、`PermanentAboveCorridorLandingMount`、`PermanentAboveCorridorLandingInstall`、`PermanentAboveCorridorMountedIteration`、`PermanentAboveCorridorFixedPointCore`、`PermanentAboveCorridorFixedPointFloor`、`PermanentAboveCorridorReplayFloorTwo`、`PermanentAboveCorridorFixedPointShape`、`PermanentAboveCorridorFixedPointCorridor`、`PermanentAboveCorridorFixedPointFloorTwo`、`PermanentAboveCorridorLeastMissingSummit`、`PermanentAboveCorridorNineteenBoundary`、`PermanentAboveCorridorReplayFloorThree`、`OrbitComb`、`OrbitCombWitness`、`OrbitCombValues`、`PermanentAboveCorridorNineteenReplay`、`PermanentAboveCorridorNineteenUnique`、`PermanentAboveCorridorNineteenMinimum`、`PermanentAboveCorridorNineteenTail`、`PermanentAboveCorridorNineteenRevisit`、`PermanentAboveCorridorNineteenElimination`、`PermanentAboveCorridorSixtyoneElimination`、`PermanentAboveCorridorMinimumShape`、`PermanentAboveCorridorMinimumFollowUp`、`PermanentAboveCorridorCrossingRecord`、`PermanentAboveCorridorReplayFloorFour`、`PermanentAboveCorridorPrefixSuccessorCoverage`と公理監査を追加

## Successor iteration and replay fixed point — 2026-08-29

- installationが輸送する三成分（horizon budget・anchor gap・old crossing cursor）をdischarge-level iteration rankとして定義
- installed successorをrankのstrict下降またはexact replay固定点へ完全分類
- 三成分lexの整礎性でiteration constructorを再帰消去し、terminal解析を四形へ無条件閉包
- replayで`returnTime = oldCrossingTime = crossingTime`の閉cycleを証明
- ready crossing nodeの形状一意性からinstalled node=parentのnode-level固定点を証明
- successor dischargeを同parent・同cursorへtransportするself-map化を証明
- 固定点の全cursorをtarget未満のbelow corridor帯へ有限化
- 実軌道step検証でclock 3/4/5を排除し、clock≥6・target≥8・target≤upperTri(clock+1)の挟撃を証明
- missing-target下のterminal interfaceをhistory edge／semantic child／replay固定点の三形へ確定
- replay cycleのdischargeごとの一意性を証明
- `PermanentAboveCorridorSuccessorRank`、`PermanentAboveCorridorIterationClosure`、`PermanentAboveCorridorReplayPinning`、`PermanentAboveCorridorReplayCorridor`、`PermanentAboveCorridorReplayFloor`、`PermanentAboveCorridorReplayInterface`と公理監査を追加

## Permanent-tail analysis — 2026-08-29

- strictly-above tailの各状態から高々二遷移で`CoverageStep`を抽出
- below-target履歴被覆から`missingBelowCount = 0`を証明
- 仮想反例からzero-budget・no-future-downcrossのready crossingを構成
- zero-budget crossingのrefined子がcrossingに留まりanchorを厳密下降するrank境界を証明
- 自然数値tailの最小値存在と、直下値のtail以前historical blockerを証明
- tail最小値で二連続forced additionが起きることを証明
- 二連続forced addition上でpotentialが増減両方向に動く実軌道例をkernel検証
- historical predecessorのdowncross／renewed-tail二分法を証明
- renewed-tail minimum下降の強帰納でfinite historical downcrossとstrict budget dropを抽出
- historical downcross後のupcrossingをanchor-drop childまたはgrowth residualへ分類
- 任意crossing選択ではchild=parentのstationary residualが必ず構成可能というno-goを証明
- first future weak upcrossingの存在・一意性を強帰納で証明
- dual-history量`seenBelowCount`とphase／seen／minimum rankを構成
- anchor／one-way cycle phase／seen／minimumの四成分well-founded rankを構成
- dischargeからcrossingへのrank exitがstrict anchor dropと同値であることを証明
- growth residualを新cycle rankのtyped exit obstructionへ接続
- historical downcross／canonical return／旧crossingをtyped discharge証明書へ統合
- `(anchor, crossingTime)` cursorと五成分well-founded cycle rankを構成
- 非進捗をanchor growth／chronology mismatch／literal stationaryの三kernel residualへ完全分類
- canonical return rebaseがtail／horizon／minimumを保存することを証明
- 任意のrebaseがliteral stationary coreとcycle exit不能を生むno-goを証明
- canonical downcross endpointからfirst returnまでのbelow corridorを証明
- 即時corridorのexact valley equationと、全内部stepのbudget drop／target-bounded clock分類を証明
- delayed corridorをinternal subtractionまたはall-forced有限runへ完全分類
- all-forced runのreturn/gap上界、加算trace、strict growth、remaining-clock rankを証明
- first returnのlater below suffix安定性を証明
- legal endpoint移動をhistory-budgetとreturn-distanceの同時下降へ接続し、suffixを完全分類
- legal subtraction直後のforced upcrossがexact targetを打つことを証明
- target-missing下でlegal endpointのreturn着地を排除し、post-legal terminalをall-forcedへ縮約
- all-forced suffixのtraceをfinal return upcrossまで延長
- terminal residualをstrict crossing、target gap／overshoot上界付き有限windowへ縮約
- suffix cursorの強帰納で任意個のlegal endpoint後のall-forced terminal存在を証明
- 全dischargeをimmediate historical valleyまたはfinite crossing windowの二形へ型付き正規化
- terminal二形に共通するgap＋overshoot＝final clockと両差のclock上界を証明
- final fresh endpoint／canonical return／strict balanceの共通interfaceを構成
- final forced additionをdouble-clock数値境界またはstrictly earlier historical blockerへ分類
- historical blockerがfreshより後ならstrict history-budget drop、以前ならouter historyとなる位置分類を証明
- immediate valleyではblockerが必ずfresh endpointより前になることを証明
- terminal解析をmaster residualへ統合し、strict budget progressを除くouter residualを四形へ限定
- finite insufficient枝を`return < target < 2*(return+1)`のclock bandへ縮約
- finite clock bandを長さtarget以下の明示return候補listへ変換
- later candidateで`target-return`が厳密下降するwell-founded rankを構成
- finite candidate枝を除くnon-clock outer residualを三形へ限定
- positive historical blockerの初出直前でstrict missing-drop／seen-gainを証明
- blocker predecessor選択を既存tail-cycle backtrack rank下降へ接続
- blockerをoriginal endpoint以前またはforward budget progressへ分類
- blocker first occurrenceのinitial枝を排除しlegal／forced生成遷移を完全分類
- legal枝のlarger predecessor provenanceとforced枝のtarget-bounded predecessor/clockを抽出
- below-target blocker landingがordinary normal/debt invariantへ直結不能であるno-goを証明
- `PermanentAboveTail`、`PermanentAbovePotential`、`PermanentAboveHistory`、`PermanentAboveCanonical`、`PermanentAboveCycleRank`、`PermanentAboveCycleExit`、`PermanentAboveCycleRebase`、`PermanentAboveCorridor`、`PermanentAboveCorridorRank`、`PermanentAboveCorridorSuffix`、`PermanentAboveCorridorBoundary`、`PermanentAboveCorridorWindow`、`PermanentAboveCorridorTerminal`、`PermanentAboveCorridorBalance`、`PermanentAboveCorridorBlocker`、`PermanentAboveCorridorBlockerPosition`、`PermanentAboveCorridorResidual`、`PermanentAboveCorridorCandidates`、`PermanentAboveCorridorOuterHistory`、`PermanentAboveCorridorBlockerGeneration`と公理監査を追加

## Research baseline — 2026-08-28

- Lean 4.33.1で再現可能な研究リポジトリとして整理
- 座標力学、借用遷移、実軌道上界を形式化
- 実軌道上の多段借りを排除
- 負領域と非負アンダーシュートの有限化
- CoverageStepと履歴探索ランクを構成
- 対角状態の極大後方減算鎖と早期blockerを抽出
- 通常／対角負債の四成分well-foundedランクを構成
- debt crossingと負normal分岐を意味的探索domain内で閉包
- canonical開始点の全符号・低level分岐をsemantic rankへ接続
- quotient-one forced growthを二段先のCoverageStepで回収
- ordinary normal証明書のhorizon不整合境界とorbit-ready代替を形式化
- orbit-ready current normalの全符号・低level局所totalityを証明
- current／historicalを分離するnormal provenance APIと生成箇所監査を追加
- extended-history normalの直接輸送条件と二つの独立残余を形式化
- historical normalの5種類のtyped provenanceとcurrent生成adapterを追加
- current親のCoverage blockerをfuture current／earlier debtへ完全分解
- generic extended-history normalのearly／budget-gap残余をcrossing recoveryで完全閉包
- downcross restartのmechanism-specific total semantic stepを証明
- parent-dropをfuture current／earlier debtへ分解し、debt self-exitを局所戦略から除去
- horizon-ready debtとready current/debt refined domainを追加
- orbit-ready semantic childのrefinement境界をnormal/debt horizon readinessへ限定
- orbit-ready normalの全生成分岐をdirect refined stepへ閉包
- ready debt obstructionとcrossing frontier middle residualをrefined domainへ閉包
- extended-history normalのdirect refined totalityを証明
- refined restricted oracleの残余をcrossing-local stepひとつへ縮約
- crossingから非crossing refined childへの進捗がstrict budget dropを要求するrank境界を証明
- ready crossingの保存horizon以後のfuture downcrossをbudget下降でrefined childへ閉包
- horizon-below ready crossingを次のcrossing進捗またはstable-budget/anchor-growth残余へ完全分類
- target 19の実軌道上にcrossing continuation growth残余が実在することをLeanで検証
- no-future-downcrossをpermanent above-target tailと同値化し、tail-return仮説からready crossing局所totalityを証明
- 研究レポート、証明地図、ロードマップ、再現手順を追加

全射性そのものは未証明である。
