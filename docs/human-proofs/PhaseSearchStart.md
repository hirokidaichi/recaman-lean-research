# PhaseSearchStart

**役割:** 各目標に対する canonical な探索開始ノードを証明書付きで構成し、意味的 domain に制限されたオラクル(restricted oracle)の完成スキーマを与える。

## このモジュールの役割

`PhaseSearch` の `PhaseSearchOracle` は「数値の組として作れる**すべての** `PhaseSearchNode`」に対して減少する子を要求する。しかし数値 tuple の大半は実軌道と無関係な状態であり、そこでの証明義務は不可能または無意味である。本モジュールは二つの改善を行う。第一に、`InitialRegion` の結果を使って、各正の目標 `m` に対し実軌道上の canonical な開始ノード(時刻・値・座標・初出証明を伴う)を構成する。第二に、オラクルの定義域を任意の述語 `Valid`(意味的 domain)に制限し、「`Valid` を保存しながらランクを下げる」という弱い義務(`RestrictedPhaseSearchOracle`)だけから目標到達が従うことを示す。以後のすべての探索完成の試みはこのスキーマの `Valid` を具体化する形で進む。

## 主要な定義

### `targetStartNode` (L11)

時刻 `n` に付随する canonical な normal ノード `⟨n, a n, normal, a n⟩`。horizon は `n`、アンカー親と局所量はともに現在値 `a n` である。座標や初出証明は数値ノードには入れず、別の証明書に置く。

### `TargetStartCertificate` (L18)

`InitialRegion` が供給する、canonical な開始の意味的証拠。時刻 `n` について

* `near_target`: `n = m−1` または `n = m`(開始時刻は目標のすぐそば)、
* `time_ready`: `m ≤ n+1`(目標時刻条件)、
* `value_ready`: `m ≤ a n`(目標下界)、
* `witnesses`: 時刻 `n` の座標 `CoordinatesAt n q r` と、現在値 `a n` の初出時刻 `f ≤ n` の初出証明 `FirstAt a (a n) f`

を保持する。初出時刻は数値ノードの成分ではないが、のちの normal/debt 遷移が自分の意味的不変量を組み立てる際に必要になるため保持する。

### `TargetStartInvariant` (L40)

数値ノードが canonical な目標開始であること: ある軌道時刻 `n` が存在して、ノードが `targetStartNode n` に等しく、`TargetStartCertificate m n` が成り立つ。

### `RestrictedPhaseSearchOracle` (L57)

意味的 domain `Valid` に制限されたオラクル。`Valid` を満たす親ノードに対してのみ、「目標が出現する」か「`Valid` を満たしつつランクが真に小さい子が存在する」ことを要求する。`PhaseSearchOracle` と異なり任意の数値 tuple には何も要求せず、子にも `Valid` の保存を義務付ける。`Valid` には normal 不変量、`DebtInvariant`、crossing データなどを組み合わせて入れられる。

## 定理と証明

### `exists_targetStartCertificate` (L27)

**主張:** すべての正の目標 `m` に対し、`TargetStartCertificate m n` を満たす時刻 `n` が存在する。

**証明:** `InitialRegion` の定理 `exists_targetReady_state_of_pos` がまさにこの形の時刻・座標・初出証明を供給するので、それを構造体に詰め替えるだけである。

### `exists_targetStartNode` (L45)

**主張:** すべての正の目標は、canonical 開始不変量を満たす実際の数値ノードを持つ。

**証明:** 前定理の時刻 `n` に対する `targetStartNode n` が定義により条件を満たす。

### `restrictedPhaseSearchOracle_reaches_from` (L66)

**主張:** `Valid` を保存する制限オラクルがあれば、`Valid` を満たす任意の開始ノードから `∃ t, a t = m` が従う。

**証明:** `phaseSearchProgress_wellFounded` による整礎帰納法。ポイントは、帰納法の各段でオラクルを適用するために親が `Valid` であることが必要だが、オラクル自身が子の `Valid` を返すので、不変量が帰納を通じて維持されることである。整礎性はランク(数値)側だけで成立しているため、`Valid` の整礎性のような追加仮定は不要である。

### `targetStart_reaches_of_restrictedOracle` (L83)

**主張:** 正の目標 `m` に対する開始特化の完成スキーマ。「すべての certified canonical 開始を含む意味的 domain `Valid`」と「`Valid` を保存する制限オラクル」を選べば `∃ t, a t = m` が従う。不正な・到達不能な `PhaseSearchNode` に対する挙動は一切要求されない。

**証明:** `exists_targetStartNode` で開始ノードを取り、仮定によりそれは `Valid` に入るので、前定理を適用する。

### `phaseSearchOracle_to_restricted` (L95)

**主張:** 全域の `PhaseSearchOracle` は、すべての数値ノードを domain に許した制限オラクル(`Valid = fun _ => True`)の特別な場合である。

**証明:** 定義の書き換えのみ。制限スキーマが従来の全域スキーマの真の一般化であることの確認である。

## 全体の中での位置づけ

証明地図では「四成分位相ランク」と「canonical局所オラクル」「意味的探索domain」の間をつなぐ位置にある。入力は `InitialRegion`(各目標のそばに目標到達準備済みの実状態が存在すること)と `PhaseSearch` のランクである。出力の `RestrictedPhaseSearchOracle` スキーマは本プロジェクトの探索完成の標準形式であり、`PhaseSemantic` は `Valid` として `PhaseSemanticInvariant` を選んで `SemanticPhaseSearchOracle` を定義し、`RefinedOracleBoundary` 以降の refined domain もすべてこのスキーマの具体化である。`TargetStartCertificate` が初出時刻を保持する設計は、のちに `NormalSearchCertificate`(`PhaseSemantic`)が canonical 開始を一般の normal ノードとして受け入れる際に効いてくる。
