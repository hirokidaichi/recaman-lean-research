# Lean module architecture

この文書は、Lean sourceの**機械的なimport構造**の正本である。数学的な定理依存は
[`PROOF_MAP.md`](PROOF_MAP.md)、研究状態は[`CURRENT_FRONTIER.md`](CURRENT_FRONTIER.md)を参照する。
import到達性と、ある主張が別の主張から数学的に従うことは別物なので、ここでは混同しない。

## Entry points

- `Recaman.lean`はlibrary entry pointであり、`Recaman/Audit.lean`を除く全project moduleへ
  directまたはtransitiveに到達する。
- `Recaman/Audit.lean`は逆に`Recaman.lean`をimportし、主要宣言の公理依存を報告する独立entry pointである。
  rootからAuditをimportすると循環になるため、root closureの対象外とする。
- module graphはacyclicでなければならず、全`import Recaman...`は実在するsourceへ解決されなければならない。

これらは[`scripts/check_module_architecture.sh`](../scripts/check_module_architecture.sh)が検査する。
Lean buildが偶然通るだけでは、rootから到達不能なsourceや重複importを検出できないため、full checkの
最初に構造監査を置く。

## Dependency layers

新規moduleは、使用する最も低い安定層だけを直接importする。

| 層 | 代表module | 責務 |
|---|---|---|
| L0 kernel | `Basic`, `Coordinates`, `Blocker` | recurrence、subtraction candidate、座標、履歴に依存しない証明書 |
| L1 history/orbit | `History`, `ActualDescent`, `OrbitBounds` | canonical orbitと有限履歴の一般API |
| L2 semantic dynamics | `Coverage`, `PhaseSearch`, `PermanentAbove*` | target、tail、recovery、semantic domain |
| L3 residual branches | `TargetCandidateTransitions`, `EventualHighCorridor*`, `TargetStream*` | A/B residualのbranch固有API |
| L4 frontier results | `RecurringCandidateDemandBirth`, `PeriodicCandidateNoGo` | bounded theorem、finite no-go、composition result |
| L5 regressions | `SeededUseGapCounterexample`, `SupplyAncestryCounterexample`, `DemandProvenanceCounterexample` | exact counterexampleと停止判断の回帰証拠 |

これは既存246 sourceを一括移動するための厳密な型階層ではなく、新しい依存を上向きに増やさないための
配置規則である。基礎概念が高い層に埋まっている場合は、利用側からさらに高いconsumerをimportして
回避せず、definition ownershipを別change setで監査する。

## Frontier direct-import contracts

最近追加したfrontier境界は[`MODULE_IMPORT_CONTRACTS.tsv`](MODULE_IMPORT_CONTRACTS.tsv)で固定する。
このmanifestは研究statusを複製せず、sourceごとのdirect importだけを保持する。

| module | direct imports | 理由 |
|---|---|---|
| `RecurringCandidateDemandBirth` | `EventualHighCorridorBirth`; `RecurringCandidateBurst` | birth分類とburst APIの両方をcompositionする |
| `PeriodicCandidateNoGo` | なし | Recamán定義に依存しない純粋な有限整数・list恒等式 |
| `SeededUseGapCounterexample` | `Basic` | arbitrary seed上の`State`、`step`、`CanSubtract`だけを使う |
| `SupplyAncestryCounterexample` | `History` | canonical prefixの`FirstAt`と履歴membershipだけを使う |
| `DemandProvenanceCounterexample` | `History` | canonical prefixのsupplied-demand birth証人。`FirstAt`と履歴membershipだけを使う |
| `MissingDensityDichotomy` | `EventualHighCorridorSecondMissing` | `valuesThrough_length`と`corridor_value_law`だけを使う無条件の二分定理 |
| `DescendingChain` | `History` | step recurrenceと履歴membershipだけを使うchain補題 |
| `HoleHopping` | `DescendingChain` | chain補題だけから導くhole-hopping規則とcomb sweep |
| `PopupLock` | `HoleHopping` | pop-up後のk=3/4固定：入口、1対、反復、clock以上の値のみ、自身のk=2値との同一視 |
| `LevelTwoThree` | `PopupLock` | pop-up後にk=2へ戻る場合、k=2→1の復帰、k=2/3 ping-pongの反復と出口の位置エネルギー |
| `LockResidue` | `PopupLock` | 剰余則（両ステップで(q,r)→(q±1,r−q)、r<qで剰余増加＝弧の終端）、固定の1対で剰余−7、予算t<m+7（comb末端座標でv<13+7K）での弧終了、着地前runによる候補閉塞と固定の持続⌊(J+2)/3⌋対 |
| `PingPongRuns` | `LockResidue` | 任意level p+2/p+1のping-pong：1対で剰余−(2p+3)、K対のrunの上側値a m+k・下側値a m−(m+k+1)（候補の既訪問/未訪問だけで記述、level仮定なし）、既訪問候補は加算を強制・未訪問候補は減算を強制 |

`nextSubtractionCandidate n = a n - (n + 1)`は23 moduleで使われるため、target固有の
`TargetCandidateTransitions`からkernelの`Basic`へownershipを移した。完全修飾名は変わらない。
これにより`SupplyAncestryCounterexample`は`History`だけをimportすればよく、依存closureは
旧`HighCandidateCausalReuse`経由の169 module、暫定`TargetCandidateTransitions`経由の82 moduleから、
5 moduleまで縮小した。`PeriodicCandidateNoGo`の`Std`も削除試験後に不要と確認した。他の契約は
各direct importを一つずつ除いた単体コンパイルが未知識別子で失敗することを確認している。

## Change protocol

1. sourceを追加・移動したらroot closureを更新する。
2. downstreamの便利なumbrellaではなく、使用する宣言のownership moduleをimportする。
3. frontier contractを変更する場合はmanifestとこの説明を同じchange setで更新する。
4. module移動や基礎definitionのownership変更は、数学statementの変更と分ける。
5. 次を順に実行する。

```bash
bash scripts/check_module_architecture.sh
lake build Recaman.ChangedOwner Recaman.ChangedConsumer
lake env lean Recaman/ChangedConsumer.lean
./scripts/check.sh
```

ownership変更時にownerだけを`lake env lean Owner.lean`で検査しても、consumerが読む`Owner.olean`は
更新されない。consumerの未知識別子を本当の依存欠落と誤認しないため、最初に`lake build`で
依存順に再構築する。
