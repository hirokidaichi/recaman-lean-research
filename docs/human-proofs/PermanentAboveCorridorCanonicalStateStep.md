# PermanentAboveCorridorCanonicalStateStep

**役割:** canonicalな有限選択stateをterminal dischargeの構成子完全なoutcomeへthreadし、finite枝を「freshなkey消費による厳密なstate進捗」または「exact canonical revisit残余」へ直接分類する、命題的で反復可能なtotal step relationを与える。

## このモジュールの役割

`PermanentAboveCorridorCanonicalMinimum.lean`は、finite return枝の全数値provenance(installed window、down endpoint、historical first time、minimum value、permanent start、tail start)を有限key化し、消費型の選択state(選ぶたびに残余リストが縮む)を構成した。しかしこの選択機構が局所的な補助のままでは、後のwell-founded帰納で使えない。terminal dischargeの総合outcome(`PermanentAboveCorridorImmediateClosure.lean`の`PermanentTailTerminalSemanticallyClosedOutcome`)は`Prop`(命題)であり、そこへ選択の「次のstate」という計算的データを保持する構成子を素朴に足すと、命題から計算データを取り出す不正なelimination(large elimination)が必要になってしまう。本モジュールの設計上の要点は、fresh選択の結果を`∃ nextState, nextState = state.erase key ∧ progress`という存在命題`TerminalCanonicalTailHistoryFreshProgress`として露出することである。存在命題ならProp値のoutcomeに保持でき、しかも後の整礎帰納が必要とするのはまさに「厳密に小さい次のstateが存在する」ことだけなので、情報は失われない。これによりvisited rank(訪問済みkey管理)は局所補助ではなく、terminal反復に直接使える命題的step relationになる。証明地図の「canonical terminal state step」段階に対応する。

## 主要な定義

### `TerminalCanonicalTailHistoryFreshProgress` (L18)

freshなcanonical key選択の命題形:

```text
∃ nextState, nextState = state.erase key ∧
  TerminalCanonicalTailHistorySelectionProgress nextState state
```

次のstateの具体値(erase結果)とその厳密下降を、データではなく存在命題として保持する。

### `TerminalCanonicalTailHistoryExactRevisitResidual` (L36)

固定horizonの全数値provenance keyを消費し尽くした後に残る文字どおりの最終残余。keyの候補リスト所属と、残余リストへの非所属の二成分からなる命題である。

### `PermanentTailTerminalCanonicalStateStepOutcome` (L45)

最終的な有限選択stateをinstallした後の、構成子完全なterminal step。五つの構成子を持つ。

- `history_progress`: 既存のchronology history辺(`missingBelowCount`の厳密下降、`PermanentAboveCorridorChronologyRank.lean`)。
- `finite_state_progress`: finite return window証明書と、そのcanonical keyのfresh進捗(L18)。
- `exact_canonical_revisit`: finite return window証明書と、exact revisit残余(L36)。
- `immediate_semantic`: immediate valleyのinsufficient枝と、その意味的閉包outcome(target出現またはsemantic phase-rank下降、`PermanentAboveCorridorImmediateClosure.lean`)。
- `historical_complete`: outer historical blockerと、そのcomplete step outcome(target出現、early/ready semantic step、below installed master step、`PermanentAboveCorridorAboveClosure.lean`)。

## 定理と証明

### `TerminalCanonicalTailHistoryFreshSelectionCertificate.toProgress` (L26)

**主張:** fresh選択証明書(Type値のデータ、`PermanentAboveCorridorCanonicalMinimum.lean`)は、その命題形`TerminalCanonicalTailHistoryFreshProgress`を与える。

**証明:** 証明書の`next_state`、`next_state_eq`、`progress`の三成分を存在命題に詰め替えるだけである。Type値の証明書からProp値への忘却なので常に可能であり、逆向き(命題からデータの復元)を要求しない設計になっている。

### `PermanentTailDischargeReturnCertificate.terminalCanonicalStateStepOutcome` (L87)

**主張:** すべてのterminal dischargeは、任意の選択state(parent horizon上の`TerminalCanonicalTailHistorySelectionState`)に対して、`PermanentTailTerminalCanonicalStateStepOutcome`のいずれかを与える。すなわち意味的に閉じるか、既存のhistory/master辺を取るか、freshなcanonical有限keyを消費するか、唯一のexact canonical revisit残余を露出するかである。

**証明:** discharge証明書の意味的閉包outcome `terminalSemanticallyClosedOutcome`(`PermanentAboveCorridorImmediateClosure.lean`)で場合分けする。

- `history_progress`、`immediate_semantic`、`historical_complete`の三枝は、provenanceを一切失わずそのまま対応する構成子へ移す。
- `finite_return_candidate`枝だけが新しい処理を受ける。finite return window証明書の`canonicalTailHistorySelection`(`PermanentAboveCorridorCanonicalMinimum.lean` L273)を現在のstateに適用すると、選択結果はfreshかexact revisitの二択である。freshならL26で命題化して`finite_state_progress`へ。exact revisit(keyは候補だが残余リストに無い)なら、その二成分を`TerminalCanonicalTailHistoryExactRevisitResidual`に詰めて`exact_canonical_revisit`へ。

この定理により、従来「finite return candidate」という静的な証明書止まりだった枝が、選択stateに対する動的な二分(消費できるか、再訪か)へ精密化される。同じ有限keyは高々一度しかfresh枝を通れないので、finite枝の反復は選択stateのwell-founded関係で測れるようになる。

### `TerminalCanonicalTailHistoryFreshProgress.strict` (L115)

**主張:** freshなterminal state進捗は、常にすでに証明済みのwell-foundedなcanonical選択関係の厳密な辺を含む: `∃ nextState, TerminalCanonicalTailHistorySelectionProgress nextState state`。

**証明:** 存在命題からerase等式を捨てて進捗成分だけを取り出す射影である。整礎帰納の各段で必要になる形をあらかじめ切り出しておく補助定理である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「canonical terminal state step」(total outcomeへstate統合済み)に対応する。入力は`PermanentAboveCorridorImmediateClosure.lean`の意味的閉包outcome、`PermanentAboveCorridorAboveClosure.lean`のhistorical complete step、および`PermanentAboveCorridorCanonicalMinimum.lean`の選択機構である。出力のstate step outcomeは、corridorファミリーの終端解析の直接の入口となる: `PermanentAboveCorridorReplayBoundary.lean`は`exact_canonical_revisit`構成子が「keyをstateから全除去しても同じ証明書から再構成できる」こと(visited listだけでは矛盾が出ないこと)を示してresolver命題へ縮約し、`PermanentAboveCorridorFiniteClosure.lean`がそのfinite certificateを算術的に不成立とすることで、`PermanentAboveCorridorTerminalProgress.lean`の四progress形(target出現、strict history、semantic phase、installed master)への完全統合が完成する。
