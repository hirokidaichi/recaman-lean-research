# 逐語signatureと意味監査

対象はHEAD `08c08565c743f39350c9b959e1df7d30aa1cae5d` の未コミットsource byte。
`ShortTightDonorAvoidance.lean` SHA-256 `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`、
`SS2OldestPattern.lean` SHA-256 `a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de`。
以下はsourceから逐語引用した。登録用G5 auditではなく、週間記載を拘束する監査である。

## H-02

```lean
theorem short_tight_avoids_ss2_window (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat) (hBn : B.Nodup)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p)
    (hBA : ∀ b ∈ B, e (b : Int) = true)
    (hlag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hP : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hmin : ∀ b ∈ B, ∀ d, d < lag b → 0 < d → ¬ P2 ((past e (b : Int) (lag b)).take d))
    (u0 : Int) (hPdon : P2 (past e u0 11))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e u0 11) = 2) :
    phase p (u0 - (oldestOffset (past e u0 11) : Int)) ∉ neighborhood e p B lag := by
```

- bindersは `e`、period p、実窓 `past`、phase、B、lagを明示する。`a`/`stateAt` はなく実軌道定理でない。
- unproved defined Propを仮定しない。`P2` はmass/momentの具体条件、neighborhoodも実sign coverage。
- 結論自身を仮定せずwrapperでない。proofはshort Hall、owner-family、有限donor表を使う。
- donor最小性・current-Aはbinderにない。B member最小性 `hmin` はある。pは任意正、lagは3/7/11限定。
- 9/23判定: 限定意味合格、総合手続き未完了。`CONJECTURED`。

## H-03

```lean
theorem tight_neighborhood_eq_of_p2_prefix (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (m lag : Nat → Nat) (hBn : B.Nodup)
    (hBp : ∀ b ∈ B, b < p) (hBA : ∀ b ∈ B, e (b : Int) = true)
    (hle : ∀ b ∈ B, m b ≤ lag b) (hbound : ∀ b ∈ B, lag b ≤ 11)
    (hP : ∀ b ∈ B, P2 (past e (b : Int) (m b)))
    (htight : (neighborhood e p B lag).length = B.length) :
    neighborhood e p B m = neighborhood e p B lag := by
```

- `e`、period、actual past windows、二つのneighborhoodを量化し、自由Nat/Int算術だけではない。
- full lag windowのP2とmの最小性は仮定しない。元カードは両方を仮定するのでLean文の方が広い。
- 結論を仮定しない。short-window Hallとsublist+length equalityの直接合成で、H-02に依存しない。
- strict `m<lag` は仮定せず `m=lag` を許す。元カードのstrict/full-P2/tight域の非空性は未確認。
- 9/23判定: 元カードからLean文への限定意味合格、総合手続き未完了。`CONJECTURED`。

## H-04

```lean
theorem nonminimal_donor_length15_counterexample :
    (∀ t : Int, donorLength15Stream (t + 16) = donorLength15Stream t) ∧
    Recaman.ShortPeriodicSupply.signSum donorLength15Stream 0 16 = 2 ∧
    donorLength15Stream 15 = true ∧ P2 (past donorLength15Stream 15 15) ∧
    Recaman.OneSSMultiplicity.ssCount (past donorLength15Stream 15 15) = 2 ∧
    P2 (past donorLength15Stream 15 3) ∧
    donorLength15Stream 3 = true ∧ past donorLength15Stream 3 3 = aas ∧
    neighborhood donorLength15Stream 16 [3] (fun _ => 3) = [0] ∧
    phase 16 (15 - (oldestOffset (past donorLength15Stream 15 15) : Int)) = 0 ∧
    Recaman.TwoSSTightDisjoint.deletedNeighborhood donorLength15Stream 16 [3]
      (fun _ => 3) (phase 16 (15 - (oldestOffset (past donorLength15Stream 15 15) : Int))) = [] := by
```

- これは固定literalのconjunction certificateで、falseな普遍延長そのもののsignatureではない。
- sourceのconjunctはperiodicity、positive mass、donor current A、P2/SS2、proper P2 prefix3、
  BのAAS窓、N=[0]、true oldest phase0、deleted N=[]を直接固定する。
- `B.Nodup`、B窓最小性、Hallはsignature外で、9/23独立literal checkerが別に再計算した。
- fixed offset11はphase4。certificateのphase0と置換不可。
- 9/23判定: 一literalと非最小lag15延長のstopだけ合格。最小lag15・一般lag・実軌道は未決。

## H-05 局所3宣言

```lean
theorem moment_ending_A_budget (w : List Bool) (q : Nat)
    (hss : ssCount (w ++ [true]) ≤ q) :
    (q : Int) + 1 ≤ moment (w ++ [true]) + q * (w ++ [true]).length := by
```

```lean
theorem moment_ending_AA_ss2 (w : List Bool)
    (hss : ssCount (w ++ [true, true]) ≤ 2) :
    5 ≤ moment (w ++ [true, true]) + (w ++ [true, true]).length := by
```

```lean
theorem ss2_intervening_prefix (w : List Bool)
    (hm : mass (w ++ [true]) = 0)
    (hM : moment (w ++ [true]) + (w ++ [true]).length ≤ 0)
    (hss : ssCount (w ++ [true]) ≤ 2) :
    ∃ u v : List Bool, w ++ [true] = (u ++ [false]) ++ v ∧
      P2 (u ++ [false]) ∧ v ≠ [] := by
```

- 最初の二つは任意有限Bool listの構造帰納、第三は長さに関するwell-founded recursion。
- 第三はA-ended、mass0、moment+length<=0、SS<=2を全て明示し、`v!=[]` がstrict性。
- period、phase、OwnerFamily、e、a/stateAt、実軌道binderはない。これは局所word lemmaである。
- conclusion-equivalent premiseやunproved defined Propはなく、wrapperでも純自由算術だけでもない。
- 9/23判定: この3宣言と紙§1-2だけ限定意味合格。後半・結合・H-05全体は未監査、総合未完了。

## 双方向・依存・限界

- H-02: 日本語とsignatureはdonor非最小・任意整数clockまで一致。周期語から実軌道への逆方向はない。
- H-03: 元カード `=>` Lean前件は確認済み。Lean前件 `=>` 元カード前件はfull-lag P2/minimal-mがないため不可。
- H-04: conjunction + checker obligations `=>` false universal instance。最小donor問題への逆用不可。
- H-05: 任意A-ended Xはあるwの `w++[A]` と表せ、第三signatureと局所card lemmaは双方向対応。
  しかしそのlemma `=>` 任意長donor avoidanceには、未監査のAAS/w1配置・decomposition・periodic liftが必要。

従って、Lean受理、vacuity/lint通過、局所意味合格のいずれも、H-02/H-03/H-05の総合合格や
一般lag・実軌道を与えない。
