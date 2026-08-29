# OrbitReadyAdapters

**役割:** 既存の各semantic閉包定理が実際には現在軌道状態のnormal子を作っている事実を回収し、broad domainへ忘却される前に `OrbitReadyNormalInvariant` へ持ち上げる保守的なadapter群。

## このモジュールの役割

canonical閉包・負エポック・非負帯・強制成長など多くの既存定理は、実軌道の時刻 `t` における状態 `⟨t, a t, .normal, a t⟩` を子として構成しながら、結果型では `PhaseSemanticInvariant` だけを返すため「現在状態である」という情報を即座に忘れてしまう。orbit-ready normal(現在値が本当に `a time` であり、時刻準備 `target ≤ time + 1`、目標下界、現在座標を併せ持つ状態)には局所epoch定理を常に適用できるので、この忘却は損失である。本モジュールは共通の証明データを `CurrentNormalChildEvidence` として一箇所に集め、各生成源が一様には保持していない唯一の条件 — 絶対時刻の前提 `target ≤ time + 1` — だけを明示的に受け取る変換定理を与える。そのうえで、この条件を局所的に導出できる分岐ごとのadapterを列挙する。

## 主要な定義

### `CurrentNormalChildEvidence` (L24)

絶対時刻条件が供給される前の、現在状態normal子に共通する証拠。目標の正値性、目標下界 `target ≤ a time`、現在座標 `CoordinatesAt time q r`、および親からのランク下降 `PhaseSearchProgress target ⟨time, a time, .normal, a time⟩ parent` を保持する。broadな `NormalSearchInvariant` と違い、nodeは定義上その時刻の実状態である。

## 定理と証明

### `CurrentNormalChildEvidence.orbitReady_and_progress` (L35)

**主張:** 上の証拠に `target ≤ time + 1` を加えると、初出証明書を作り直すことなく、orbit-ready不変量と元のランク下降が同時に得られる。

**証明:** orbit-ready証明書の五フィールドは、証拠の各フィールドと追加条件そのものである。node等式は定義から `rfl` で成立し、progressは保持していたものをそのまま返す。

### `CurrentNormalChildEvidence.time_ready_of_orbitReady` (L53)

**主張:** 追加した条件は正確(過不足なし)である。この実状態nodeがorbit-readyなら、必ず同じ絶対時刻上界 `target ≤ time + 1` が回収できる。

**証明:** orbit-ready不変量の存在量化を開くと、証明書のnode等式のhorizon成分から証言時刻が `time` に一致し、その `time_ready` フィールドが求める不等式である。

### `targetStartInvariant_orbitReadyAdapter` (L67)

**主張:** canonical start不変量は `0 < target` の下でorbit-readyである。

**証明:** canonical start証明書はorbit-readyの全フィールド(時刻準備・値下界・座標)を既に保持しており、既存変換を呼ぶだけである。

### `NormalPhaseInvariantAt.reanchorOrbitReady` (L76)

**主張:** 強い現在normal不変量(負エポック用の `NormalPhaseInvariantAt`、anchorが値より大きくてもよい)を実際の値 `a n` でre-anchorすると、orbit-ready不変量 `OrbitReadyNormalInvariant target ⟨n, a n, .normal, a n⟩` になる。

**証明:** 座標と時刻データはすべて保存され、失われるのは「値より大きいかもしれない探索anchor」だけである。orbit-ready証明書の各フィールドを直接埋める。

### `normalPhaseInvariant_currentProgress_orbitReady` (L95)

**主張:** 強い現在normal不変量と親へのランク下降があれば、re-anchorした子について「orbit-readyかつ同じ親への下降」が成り立つ。

**証明:** `a n ≤ activeParent` で場合分けする。等号なら、re-anchorは何も変えないので与えられた下降がそのまま使える。厳密な不等号なら、horizonを保ちanchorを `activeParent` から `a n` へ厳密に下げるstepがランク下降になるので、それを与えられた下降と推移律でつなぐ。

### `normalEpochExit_above_orbitReadyAdapter` (L123)

**主張:** 負エポックのforward exit(未来時刻 `time` への軌道前進)で `target ≤ a time` なら、`a time` でre-anchorした子はorbit-readyであり、元の親への下降も保たれる。

**証明:** exit証拠は子の座標と時刻準備 `target ≤ time + 1` を保持している。まず `normalProgress_reanchorAtValue` で、raw子(anchorが親のまま)のprogressを、値でre-anchorした子のprogressへ変換する(親のanchorは値以上なのでanchorは増えない)。あとは `CurrentNormalChildEvidence` を組み、L35を適用する。

### `nonnegativeForwardAbove_orbitReadyAdapter` (L148)

**主張:** 非負帯履歴探索のforward-above分岐用の汎用adapter。時刻準備・親上界・目標下界・座標と、その分岐が返す `HistorySearchProgress`(三成分履歴ランクの下降)から、orbit-readyな子と `PhaseSearchProgress` が得られる。

**証明:** 三成分の履歴下降を四成分の位相下降へ持ち上げ(`toNormalPhaseSearchProgress`)、値でre-anchorしてからL35を適用する。仮定の `target ≤ t + 1` がそのまま絶対時刻条件になる。

### `canonicalHistoryFrontier_above_orbitReadyAdapter` (L174)

**主張:** canonical履歴frontierのabove-target前進子はorbit-readyである。旧frontier APIが返さなかった子の時刻条件は、canonical時刻条件 `target ≤ n + 1` と厳密な時刻前進 `n < t` から導出される。

**証明:** `HistoryBudgetProgress`(履歴予算ペアの下降)を位相ランクへ変換し、`target ≤ n + 1 ≤ t + 1` を算術で出してL35を適用する。

### `canonicalLevelZero_future_orbitReadyAdapter` (L196)

**主張:** canonical level 0が公開するfuture-current分岐のadapter。canonical証明書と未来時刻証人 `n < t`、値の厳密下降 `a t < a n` から、orbit-readyな子と `targetStartNode n` への下降が得られる。

**証明:** ランク下降は「horizonが伸びanchorが厳密に下がる」ことから直接作れる。時刻条件はcanonical証明書の `time_ready` と `n < t` の算術による。

### `canonicalLegalSubtraction_above_orbitReadyAdapter` (L219)

**主張:** above-targetの合法減算は実際のfreshな現在子を作る。`target ≤ n + 1` を仮定に加えたのは、それが `canonical_legalSubtraction_phaseSemantic` の公開シグネチャに欠けていた時刻準備データそのものだからである。

**証明:** 減算可能性から `n + 1 < a n` なので `a (n+1) = a n − (n+1) < a n`、すなわち値は厳密に下がる。時刻 `n + 1` は正なので座標が存在する。horizon前進とanchor下降でランクが下がり、時刻条件は `target ≤ n + 1 ≤ (n+1) + 1` で満たされる。L35を適用する。

### `forcedAdditionForwardAbove_orbitReadyAdapter` (L247)

**主張:** 商が2以上の強制加算frontierのforward-above選択肢のadapter。二歩先 `n + 2` のraw履歴エッジは既に正しい親上界を持ち、実際の未来時刻で現在座標を再構成すればorbit-readyになる。

**証明:** 時刻 `n + 2` は正なので座標が存在する。あとは時刻条件 `target ≤ n + 1 ≤ (n+2) + 1` を添えてL148の汎用adapterに帰着する。

### `CanonicalForcedGrowthChamber.nextState_orbitReady` (L268)

**主張:** canonical強制成長chamber(level 1・2の商1状態で減算が塞がれた配置)の直後状態は、canonical親のランク子にはまだならないにもかかわらず、orbit-readyではある。すなわち、ある `n` と `child = ⟨n+1, a (n+1), .normal, a (n+1)⟩` が存在して、orbit-ready不変量が成り立ち、かつ `PhaseSearchProgress target child parent` は成り立たない。

**証明:** chamberの `nextState` 定理は、強制加算後の子が強い現在normal不変量 `NormalPhaseInvariantAt` を満たすこと、および値もanchorも増え履歴予算も不変なのでランクが下がらないことを同時に与える。前者をL76でre-anchorすればorbit-readyが得られ、後者はそのまま非下降の証人になる。これにより「意味的な準備(orbit readiness)」と「意図的な二段先ランク先読み」が分離される: 進捗はここでは測れないが、状態としてはepoch機構を適用できる。

## 全体の中での位置づけ

証明地図の「意味的探索domain」段を支える供給源である。`OrbitReadyComplete.lean` はここで持ち上げた証明書に対して全符号の局所閉包を証明し、`OrbitReadyDirectRefined.lean` の各refined step定理(負エポック・非負帯・強制加算frontier)は本モジュールのadapter(L123、L148、L219、L247)を分岐内で直接呼んで、現在子をorbit-readyのままrefined domainへ送る。`CoverageDebtBridge.lean` のorbit-ready親wrapperも本モジュールの視点(現在状態の証明書を捨てない)に依拠している。
