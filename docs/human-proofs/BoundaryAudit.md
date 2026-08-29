# BoundaryAudit

**役割:** crossing・負normalの残余義務に対する境界監査 — 現行の不変量のフィールドから何が従い、何が従わないかを、小さなインターフェース補題と実軌道上の具体的反例で正確に確定する。

## このモジュールの役割

位相探索(四成分ランクによる大域探索)の本体では、負normal状態やcrossing(target未満から以上への強制横断)の子ノードを生成する定理が、それぞれ固有の「証拠(evidence)」型を返す。本モジュールは、その証拠型が実際に保持している情報の**境界**を監査する。すなわち、(1) 証拠から追加で導ける結論を小さな補題として取り出し、(2) 証拠だけでは導けない結論については実軌道上の反例をカーネル検証付きで構成する。生産用の不変量を一切変更しないことを方針とし、後続モジュール(`TypedNormalProvenance`、`NonnegativeSemantic`、`Canonical*` など)が安全に依存できる正確なインターフェース仕様を確定する。中核成果は、下方横断(downcrossing)が必ず目標出現か履歴予算低下を生むという再利用性の高い定理 `orbit_downcrossing_occurs_or_budgetDrop` である。

## 定理と証明

### `diagonalCrossingCatchup_budget_eq_horizon` (L18)

**主張:** target が `horizon + 1` である対角catch-up証明書 `CrossingCatchup` について、catch-up到達時刻 `catchTime` での履歴予算(`missingBelowCount`: 時刻までに未出であるtarget未満の値の個数)は、記録されたhorizon(履歴を評価する時刻)での履歴予算に等しい:

```
missingBelowCount (horizon+1) catchTime = missingBelowCount (horizon+1) horizon
```

**証明:** 証明書のフィールド `time_eq` により `catchTime` は `target − 1 = horizon` か `target = horizon + 1` のいずれかである。前者なら両辺は同一の式であり自明。後者の場合、時刻が1つだけ進むが、証明書のフィールド `target_le_value` により新しく履歴に加わる値 `a catchTime` は target 以上である。target 以上の値が加わっても「未出のtarget未満の値」は一つも消えないので、予算は変わらない(補題 `missingBelowCount_succ_of_new_ge`)。∎

**意味:** 対角catch-upは記録されたhorizonより一歩先へ進み得るが、その一歩は履歴予算を変えられない。したがってcatch-up履歴を使う子ノードは、古いhorizonのまま履歴を黙って読み替えるのではなく、horizonを `catchTime` に更新して持たなければならない — 予算の帳簿はhorizonに正確でなければならない、というインターフェース上の注意を定理として固定したものである。

### `normalPhase_qOneDebt_already_occurs` (L36)

**主張:** 完全な負normal不変量 `NormalPhaseInvariantAt`(ノードの値が実際に `a n` であり、`target ≤ a n ≤ anchor`、座標が負ポテンシャルを持つ、などをすべて保持する状態)が成り立つとき、その後の時刻 `t ≥ n` で値が `a n` 以下、座標の商が 1、一段借りで非負かつtarget未満のレベルに着地する配置が現れたなら、targetはすでに軌道上に出現している: `∃ u, a u = target`。

**証明:** ランクのみを扱うエポックAPIの定理 `qOneDebt_target_or_diagonalSuccessor` を適用すると、(a) target出現、または (b) 例外分岐として `n = t`、`target = t + 1`、かつ対角条件 `a t = t` が得られる。(b) の場合、不変量の(この定理以外では使われていない)下界 `target ≤ a n` に代入すると `t + 1 ≤ a t = t` となり矛盾する。よって (b) は起こり得ず、常に (a) が成り立つ。∎

**意味:** ランクだけを見るAPIでは消せなかった「商1のdebt(負債: 通常探索へ戻る前に解消すべき局所義務)へ入るかもしれない」という例外分岐が、完全な意味的不変量のもとでは空であることを示す。不変量に含まれる一見冗長な下界フィールドが、この分岐の消去にちょうど必要だったという監査結果である。

### 具体的反例の構成部品 (L56)

L56〜L130は、次の2定理で使う反例を実軌道上に構成するprivate定義・補題群である。目標を `target = 3` とし、時刻3の実状態(`a 3 = 6`、座標 `6 = 3·2 + 0` で `q = 2, r = 0`、ポテンシャル `0 − upperTri(2) = −3 < 0`)を親ノード `⟨3, 7, normal, a 3⟩` とする。親が完全な不変量 `NormalPhaseInvariantAt 3 … 3 2 0` を満たすこと(L72)、値3の初出が時刻2であること(L56)、そして2種類の子ノード — anchorを3へ下げるdrop子 `⟨4, 3, normal, a 4⟩`(L66)と、anchor 7 を保つepoch子 `⟨4, 7, normal, a 4⟩`(L69)— がそれぞれの証拠型を満たすこと(L94, L104)を `decide`(カーネル計算)で検証する。時刻4で `a 4 = 2 < 3` が初出するため履歴予算は 1 から 0 へ真に下がり、どちらの子も探索ランクは正しく低下する(L82, L88)。しかし `a 4 = 2` は target 3 を下回るので、どちらの子も不変量の下界 `target ≤ a n` を満たせない(L114, L123)。

### `normalParentDropEvidence_not_sufficient` (L136)

**主張:** 親が完全な負normal不変量を満たし、子が親低下証拠 `NormalParentDropEvidence`(新anchorがtarget以上の真の初出値で、親のanchorより小さく、ランクが低下する、という証拠)を満たしていても、子が不変量 `NormalPhaseInvariant` を回復するとは限らない。すなわち三つ組

```
親の不変量 ∧ 子のdrop証拠 ∧ ¬(子の不変量)
```

を同時に満たす実例が存在する。

**証明:** 上記の構成部品を束ねるだけである。実軌道の遷移 `a 3 = 6 → a 4 = 2` は履歴予算を下げる正当なランクステップだが、新しい軌道値 2 が target 3 を下回るため、子は `target ≤ a n` を満たせない。∎

### `normalEpochExitEvidence_not_sufficient` (L147)

**主張:** 前方エポック退出証拠 `NormalEpochExitEvidence`(時刻前進・時刻準備条件・座標・ランク低下を保持する証拠)についても同様に、親の不変量と子の証拠が揃っていながら子の不変量が成り立たない実例が存在する。

**証明:** 同じ遷移 `a 3 = 6 → a 4 = 2` を、anchorを保つepoch子に読み替えるだけでよい。前進かつランク低下だが、target下界が失われる。∎

**両定理の意味:** 現行の2つの証拠型は「ランクが下がる正当な探索ステップである」ことは保証するが、「子で意味的不変量を再確立できる」ことまでは保証しない — その隙間は実軌道上に本当に存在する。この監査結果が、証明地図の「現在の一点」で述べられる orbit-ready 証明書・provenance(生成元証明)付きdomainへの精密化の直接の動機である。

### `orbit_downcrossing_occurs_or_budgetDrop` (L160)

**主張:** 軌道区間がtarget以上で始まりtarget未満で終わるなら、区間内でtargetに命中するか、履歴予算が真に減る。正確には `start ≤ finish`、`target ≤ a start`、`a finish < target` のとき、

```
(∃ u, start ≤ u ≤ finish, a u = target)  ∨
missingBelowCount target finish < missingBelowCount target start
```

**証明:** 区間の長さ `d = finish − start` に関する帰納法で、終点 `a (start + d)` がtarget未満であるすべての `d` について主張を示す。

`d = 0` の場合は `target ≤ a start < target` となり前提が矛盾するので自明である。

帰納段階では、一歩手前の値 `a (start + d)` で場合分けする。ちょうどtargetに等しければ第一の選択肢が成り立つ。target未満なら帰納法の仮定を適用し、出現枝はそのまま、予算低下枝は `missingBelowCount` の反単調性(履歴が延びても予算は増えない)と合成して閉じる。

残るのは `a (start + d) > target` かつ `a (start + d + 1) < target` の場合、すなわち**最初の下方横断(downcross)の瞬間**である。ここで力学の分岐を見る。強制加算だったとすると `a (start+d+1) = a (start+d) + (start+d+1) > target` となり、終点がtarget未満であることに反するので、算術的に不可能である。よってこの一歩は合法減算であり、減算可能性 `CanSubtract` の定義そのものにより、着地値 `a (start+d+1)` は直前までの履歴に**未出**(fresh)である。target未満の未出値が新しく履歴に入るので、この一歩で `missingBelowCount` は真に減る(`missingBelowCount_strict_of_new`)。`start` から `start + d` までの反単調性と合わせて、第二の選択肢が得られる。∎

**意味:** 「上から下へ横断する軌道は、その横断点で必ず新しい下側値を発見する」というレカマン力学の基本原理を、探索ランクの言葉(履歴予算の厳密低下)に直訳した定理である。本モジュール内では次の定理に使われるほか、`TypedNormalProvenance`、`EarlyRepresentative`、`NonnegativeSemantic`、`OrbitReadyDirectRefined`、`Canonical*` 系など多数の後続モジュールが、downcross分岐を予算低下へ変換する共通部品として再利用する。

### `NormalEpochSharpObstruction.target_occurs` (L221)

**主張:** sharp障害 `NormalEpochSharpObstruction`(前方エポック退出の残余配置で、新値がtarget未満、旧値がtargetより大きく、anchorが旧値に一致し、履歴予算が変化しない、というフィールドを持つ)が `start ≤ finish` の区間上に成立するなら、targetは軌道上に出現する: `∃ u, a u = target`。

**証明:** フィールド `old_value_above_target`(`target < a start`)と `new_value_below_target`(`a finish < target`)は、前定理の前提そのものである。適用すると、区間内でのtarget出現か、履歴予算の厳密低下が得られる。ところが障害のフィールド `budget_unchanged` は予算が変わらないことを主張しており、後者と矛盾する。よって前者、すなわちtarget出現が成り立つ。∎

**意味:** エポック退出の分類で「ランクが親と完全に同値になってしまう」最も厄介に見えた残余ケースは、実は失敗ではなかった — その配置が現れた時点でtargetはすでに出現しており、探索はそこで終了できる。境界監査が残余義務を一つ消去した例である。

## 全体の中での位置づけ

本モジュールは証明地図の**位相統合**層に属し、`CrossingGap` と `NormalClosure` の直後に置かれる。役割は三方向に効く。第一に、`diagonalCrossingCatchup_budget_eq_horizon` と `normalPhase_qOneDebt_already_occurs` は、既存APIの帳簿規約と例外分岐を完全不変量のもとで整理し、後続の閉包定理が余計な分岐を持ち込まないようにする。第二に、2つの `not_sufficient` 反例定理は、弱いnormal証明書では意味的探索domainを維持できないことを実例で確定し、`NormalSemanticBoundary` とともに orbit-ready / provenance 精密化(証明地図「現在の一点」)への設計根拠となる。第三に、`orbit_downcrossing_occurs_or_budgetDrop` とその帰結 `NormalEpochSharpObstruction.target_occurs` は、downcrossを履歴予算低下へ変換する基本原理として、canonical閉包・extended-history閉包・crossing境界解析(`CrossingDowncrossRefined` 以降)まで広く再利用される。
