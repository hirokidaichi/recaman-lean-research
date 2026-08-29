# PermanentAboveCorridorReplayBoundary

**役割:** visited list(消費済みkeyの有限リスト)だけからはexact replayの矛盾が導けないというno-goをkernel内で形式化し、残る局所命題を四結果へ限定した`TerminalExactCanonicalReplayResolver`一つに絞る。resolver仮定下ではraw replay constructorを持たないterminal total outcomeが得られる。

## このモジュールの役割

`PermanentAboveCorridorCanonicalStateStep.lean`までの選択状態機構は、terminal dischargeのfinite枝が持つ数値provenance key(window区間・anchor・旧crossing時刻・historical時刻・permanent start・tail startを束ねた`TerminalCanonicalTailHistoryKey`)を有限リストとして列挙し、freshなkeyの消費(`List.erase`)ごとにremaining lengthが厳密下降することを示した。残余は「keyは大域候補には属するがremaining listにはもう無い」というexact revisit(完全再訪)である。ここで重要な注意がある: visited listは停止性のための装置であって、「同じ状態には二度到達しない」という意味論的定理ではない。本モジュールはこの限界を正確に定式化する。すなわち、任意の有効なfinite certificateについて、そのkeyをstateから全除去(`removeAll`)した後に同じcertificateを提示すれば、exact revisit残余とterminal outcomeのrevisit constructorが直ちに構成できる。従ってリストのmembershipだけからFalseは出ない(list-only no-go)。残る数学的義務は「exact revisitをtarget出現、strict history progress、semantic phase progress、installed master progressのいずれかへ変換せよ」という命題であり、これを`TerminalExactCanonicalReplayResolver`として切り出す。resolverを仮定すれば、terminal total outcomeから未解決のraw replay constructorが消える。

## 主要な定義

### `TerminalCanonicalTailHistorySelectionState.removeAll` (L23)

選択状態(remaining keyリストと、その全要素が大域候補リストに属するという証明)から、指定keyの出現をすべてfilterで除去した新しい状態を返す操作。除去はremaining listを縮めるだけなので、候補妥当性の不変条件はそのまま保たれる。

### `TerminalExactCanonicalReplayResolution` (L79)

literal replayを解決するのに十分な進捗の型付き列挙。四constructorを持つ。

- `target_occurs`: targetの実出現witness。
- `history_progress`: `TerminalChronologyHistoryProgress`、すなわち`missingBelowCount`の厳密下降(それ自体でwell-foundedな履歴予算rank)。
- `semantic_progress`: `PhaseSemanticInvariant`を満たすchildと、parentに対する`PhaseSearchProgress`(四成分位相ランクの厳密下降)。
- `installed_master_progress`: `TailInstalledCycleProgress`(七成分installed master rankの厳密辺)。

最後のconstructorが「新しい未検証のrank」ではなく、すでにwell-founded性が証明済みのinstalled-cycle master relationである点が設計上の要点である。

### `TerminalExactCanonicalReplayResolver` (L102)

finite-state no-goの後に残る最小の数学的義務。任意のdischarge証明書`source`、選択状態`state`、finite window certificateとそのexact revisit残余に対して、上記resolutionのいずれかを返す全称命題として定義される`Prop`である。

### `PermanentTailTerminalReplayResolvedOutcome` (L114)

terminal state-step outcomeのexact revisit constructorを、resolverが返した`replay_resolved`(resolution)へ置き換えた帰納型。他の四constructor(history_progress、finite_state_progress、immediate_semantic、historical_complete)は元のまま保持される。

## 定理と証明

### `TerminalCanonicalTailHistorySelectionState.not_mem_removeAll` (L39)

**主張:** `removeAll`の後、そのkeyはremaining listに属さない。

**証明:** filter条件`candidate ≠ key`の直接計算。補助補題である。

### `TerminalFiniteReturnWindowCertificate.exactReplayResidual_after_removeAll` (L48)

**主張:** 同じfinite certificateは、そのkeyを除去した後の状態に対してexact replay(完全再訪残余`TerminalCanonicalTailHistoryExactRevisitResidual`)になる。これがlist-onlyの矛盾に対する形式的no-goである。

**証明:** 残余の二フィールドを直接構成する。keyの大域候補membership はcertificate自身の`canonicalTailHistoryKey_mem`から、remainingへの非所属はL39から従う。すなわち「有効なcertificateが存在する限り、listをどれだけ消費してもrevisit残余は再構成可能」であり、membership情報単独では反例のcertificateを殺せない。

### `TerminalFiniteReturnWindowCertificate.exactReplayTerminalOutcome_after_removeAll` (L64)

**主張:** 同じno-goは、統合されたterminal outcome(`PermanentTailTerminalCanonicalStateStepOutcome`)の`exact_canonical_revisit` constructorをも実際に居住させる。

**証明:** L48の残余をconstructorへ詰めるだけである。terminal outcomeの再訪枝が空虚な場合分けではなく、実際に到達可能であることを示す。

### `PermanentTailDischargeReturnCertificate.terminalReplayResolvedOutcome` (L151)

**主張:** 条件付き閉包定理。resolverは、terminal total stepから最後のraw finite残余を除去するのにちょうど十分である。すなわちresolverを仮定すれば、任意のdischargeと選択状態について`PermanentTailTerminalReplayResolvedOutcome`が成り立つ。

**証明:** `terminalCanonicalStateStepOutcome`(前モジュールの全分類)を場合分けする。history progress、finite-state progress(freshなkey消費)、immediate semantic、historical completeの四枝は情報を失わずそのまま対応するconstructorへ移送する。`exact_canonical_revisit`枝だけは、resolverにsource・state・finite certificate・残余を渡し、返ってきたresolutionを`replay_resolved`として格納する。従ってresolverの強さは、この一枝の除去に必要かつ十分な形で切り出されている。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「exact replay boundary(list-only no-go・条件付き閉包済み)」に対応する。上流は`PermanentAboveCorridorCanonicalMinimum.lean`(canonical tail history keyと選択状態)および`PermanentAboveCorridorCanonicalStateStep.lean`(state付きterminal total outcome)である。本モジュールの時点では`TerminalExactCanonicalReplayResolver`は未証明の仮定だったが、直後の`PermanentAboveCorridorFiniteClosure.lean`が「finite certificateはそもそもFalseである」(all-forced suffixの算術からendpoint = 1、return = 2、target ∈ {4,5}に絞られ、`a(131) = 4`、`a(129) = 5`の実出現がmissing仮定に矛盾)を示すことで、このresolverを無条件かつ空虚に証明した(`terminalExactCanonicalReplayResolver`)。したがって本モジュールの条件付き閉包は現在では無条件化されているが、「visited listは意味論的再訪禁止を与えない」というno-go自体は、有限状態機構の限界を示すkernel内の恒久的な記録として残る。
