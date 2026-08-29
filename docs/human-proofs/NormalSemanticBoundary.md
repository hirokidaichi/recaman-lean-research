# NormalSemanticBoundary

**役割:** 通常 normal 証明書 `NormalSearchInvariant` の弱さを具体的反例で確定し、それを補う強化証明書 `OrbitReadyNormalCertificate` を導入して負分岐の完全閉包へ接続する。

## このモジュールの役割

通常の normal 証明書は「anchor 値のある初出が horizon 以前にある」ことしか主張しない。そのため、(1) horizon での実軌道値が anchor と一致するとは限らず、(2) 保持する座標は初出時刻のものであって horizon のものではなく、(3) エポック API が要求する時刻準備 `target ≤ horizon+1` も従わない。本モジュールはこの三点をレカマン数列の具体値で反例として証明し(Lean カーネルの `decide` による検証)、境界を明示する。そのうえで、実軌道状態そのものを保持する orbit-ready(orbit-ready normal: 局所値が実際に `a time` であり、時刻準備・目標下界・現在座標を同時に持つ状態)証明書を定義し、これが旧証明書を再構成できること、負ポテンシャルでは既存のエポック機構へそのまま接続できることを示す。

## 主要な定義

### `OrbitReadyNormalCertificate` (L95)

目標 `target`、ノード `node`、時刻 `time`、座標 `(q,r)` について

- `0 < target`
- `node = ⟨time, a time, normal, a time⟩`(canonical なノード形: anchor も局所量も実軌道値)
- `target ≤ time+1`(時刻準備)
- `target ≤ a time`(目標下界)
- `CoordinatesAt time q r`(現在時刻での座標)

を主張する。初出の証拠は意図的に含めない。現在値は自分の履歴に属するので初出は後から再構成でき、含めると循環した強さになるからである。

### `OrbitReadyNormalInvariant` (L103)

時刻と座標を存在量化した形。「このノードは epoch 定理を適用できる実軌道状態である」ことを表す。

## 定理と証明

### `normalSearchInvariant_allows_horizon_value_mismatch` (L17)

**主張:** `NormalSearchInvariant 1 ⟨2, 1, normal, 1⟩` が成り立つが、`a 2 ≠ 1` である。すなわち通常証明書は「horizon 2 の実軌道値が anchor 1 である」ことを意味しない。

**証明:** 実軌道は `a 0 = 0, a 1 = 1, a 2 = 3` である。値 1 は時刻 1 で初出し(時刻 0 の値は 0)、`firstTime = 1 ≤ 2 = horizon` なので、target 1 に対する証明書の全条件が初出時刻 1 の座標 `(1,0)` で満たされる。一方 `a 2 = 3 ≠ 1` は `decide` による計算で確認される。過去の初出値と後の horizon の組合せが正当な証明書になる、という弱さの実例である。

### `normalSearchCertificate_coordinates_not_at_horizon` (L40)

**主張:** 上の証明書 `NormalSearchCertificate 1 ⟨2,1,normal,1⟩ 1 1 1 0` は成立するが、その座標 `(q,r) = (1,0)` は horizon での表示 `CoordinatesAt 2 1 0` ではない。

**証明:** 前半は同じ構成。後半は、`CoordinatesAt 2 1 0` が成り立てば定義の等式から `a 2 = 2·1+0 = 2` となるが、実際は `a 2 = 3` なので矛盾する。証明書の座標は時刻 1 の表示であって horizon 2 の表示ではない。

### `normalSearchInvariant_does_not_imply_time_ready` (L68)

**主張:** `NormalSearchInvariant 6 ⟨3, a 3, normal, a 3⟩` は成り立つが、`6 ≤ 3+1` は成り立たない。ノードが本当に現在軌道状態であり座標も現在のものであってさえ、時刻準備は従わない。

**証明:** `a 3 = 6` は時刻 3 で初出する(それ以前の値は 0,1,3)。よって target 6 の証明書が座標 `(2,0)`(`6 = 3·2+0`)で成立する。しかし `6 ≤ 4` は偽である。target 6 を時刻 3 で「早すぎる時刻に」証明できてしまう実例であり、エポック API の前提 `target ≤ horizon+1` が別途必要な理由を示す。

### `OrbitReadyNormalCertificate.toNormalSearchInvariant` (L111)

**主張:** orbit-ready 証明書から通常証明書を再構成できる。

**証明:** まず `time > 0` である。`time = 0` なら `a 0 = 0` が `target ≤ a time` と `target > 0` に反するからである。現在値 `a time` は履歴 `valuesThrough time` に属するので、初出時刻 `firstTime ≤ time` と `FirstAt a (a time) firstTime` が存在する。同じ理由で `firstTime > 0` であり、正時刻には座標表示が存在する。これらを組み立てると通常証明書の全フィールドが揃う。この方向の再構成は循環しない。初出は現在の履歴から従う情報だからである。

### `OrbitReadyNormalCertificate.toPhaseSemanticInvariant` (L148) / `OrbitReadyNormalInvariant.toPhaseSemanticInvariant` (L154)

**主張:** 強化証明書(およびその存在量化形)は統合意味的 domain `PhaseSemanticInvariant` に埋め込まれる。

**証明:** 前定理で得た通常証明書を normal 構成子に入れるだけである。強化は保守的な精密化であり、既存 domain と両立する。

### `OrbitReadyNormalCertificate.toNormalPhaseInvariantAt` (L165)

**主張:** 保持する座標のポテンシャルが負(`potential q r < 0`)なら、orbit-ready 証明書は追加の履歴仮定なしに強い負 normal 不変量 `NormalPhaseInvariantAt` の全フィールドを供給する。

**証明:** ノード形・時刻準備・目標下界・座標は証明書がそのまま与える。残る `a time ≤ anchorParent` は、canonical ノード形により anchor が `a time` 自身なので等号で成り立つ。すなわち orbit-ready はまさに、既存の負 normal オラクル定理群に欠けていた橋である。

### `OrbitReadyNormalCertificate.negative_phaseSemanticStep` (L184)

**主張:** 負ポテンシャルの orbit-ready 証明書からは、目標出現または「意味的な子とランク進捗」が常に得られる。

**証明:** 前定理で負 normal 不変量を作り、完全閉包定理 `negativeNormal_phaseSemanticStep`(`NormalComplete`)を適用する。

### `normalSearchInvariant_not_orbitReady` (L199)

**主張:** 通常証明書は強化証明書を含意しない。具体的に、mismatch 例のノード `⟨2, 1, normal, 1⟩` は `NormalSearchInvariant 1` を満たすが `OrbitReadyNormalInvariant 1` を満たさない。

**証明:** orbit-ready なら canonical ノード形により horizon は 2、anchor は `a 2 = 3` でなければならないが、実際の anchor は 1 である。この分離により、「すべての normal 意味的ノードを黙って epoch 状態として扱う」ことが不可能であると確定する。

## 全体の中での位置づけ

証明地図の「現在の一点」で述べられる ordinary normal constructor の弱さを、実例で確定させたモジュールである。ここで示された境界が、current ノードと historical ノードを分離する `NormalProvenance` の設計(実際 `horizonMismatch_provenance_is_historical` は本モジュールの反例を使う)、および代表時刻と history horizon を分離する `TypedNormalProvenance`・`ExtendedHistoryNormal` の設計を直接動機づけている。導入した `OrbitReadyNormalCertificate` は `OrbitReadyComplete` で全符号・全レベルの局所 totality へ拡張され、refined child domain の第一成分となる。
