import Recaman.History

namespace Recaman

/-- Number of target-smaller values which have not occurred by time `n`.
The recursive definition avoids any dependence on finite-set libraries: the
new top value `m` contributes one exactly when it is absent from the stored
history. -/
def missingBelowCount : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, n =>
      missingBelowCount m n +
        if m ∈ valuesThrough n then 0 else 1

@[simp] theorem missingBelowCount_zero (n : Nat) :
    missingBelowCount 0 n = 0 := rfl

@[simp] theorem missingBelowCount_succ (m n : Nat) :
    missingBelowCount (m + 1) n =
      missingBelowCount m n +
        if m ∈ valuesThrough n then 0 else 1 := rfl

/-- Stored history membership is monotone in time. -/
theorem valuesThrough_mono {x n t : Nat}
    (hnt : n ≤ t) (hmem : x ∈ valuesThrough n) :
    x ∈ valuesThrough t := by
  induction t generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact hmem
  | succ t ih =>
      rcases Nat.eq_or_lt_of_le hnt with heq | hlt
      · subst n
        exact hmem
      · exact valuesThrough_persist
          (ih (Nat.le_of_lt_succ hlt) hmem)

/-- The missing-level budget can only decrease as the actual history grows. -/
theorem missingBelowCount_antitone {m n t : Nat} (hnt : n ≤ t) :
    missingBelowCount m t ≤ missingBelowCount m n := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hbase := ih
      by_cases hn : m ∈ valuesThrough n
      · have ht : m ∈ valuesThrough t := valuesThrough_mono hnt hn
        simp [missingBelowCount, hn, ht]
        exact hbase
      · by_cases ht : m ∈ valuesThrough t
        · simp [missingBelowCount, hn, ht]
          omega
        · simp [missingBelowCount, hn, ht]
          exact hbase

/-- At most `m` values below `m` can be missing. -/
theorem missingBelowCount_le (m n : Nat) :
    missingBelowCount m n ≤ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [missingBelowCount]
      split <;> omega

/-- If some `g<m` is absent at time `n` but present at a later time `t`, the
finite missing-level budget decreases strictly. -/
theorem missingBelowCount_strict_of_new
    {g m n t : Nat}
    (hg : g < m)
    (hnt : n ≤ t)
    (hnew : g ∉ valuesThrough n)
    (hseen : g ∈ valuesThrough t) :
    missingBelowCount m t < missingBelowCount m n := by
  induction m generalizing g with
  | zero => omega
  | succ m ih =>
      by_cases htop : g = m
      · subst g
        have hbase := missingBelowCount_antitone
          (m := m) hnt
        simp [missingBelowCount, hnew, hseen]
        omega
      · have hglt : g < m := by omega
        have hbase := ih hglt hnew hseen
        by_cases hnTop : m ∈ valuesThrough n
        · have htTop : m ∈ valuesThrough t :=
            valuesThrough_mono hnt hnTop
          simp [missingBelowCount, hnTop, htTop]
          exact hbase
        · by_cases htTop : m ∈ valuesThrough t
          · simp [missingBelowCount, hnTop, htTop]
            omega
          · simp [missingBelowCount, hnTop, htTop]
            exact hbase

/-- A first occurrence after time `n` was absent from the history at `n`. -/
theorem firstAt_not_mem_valuesThrough_before
    {g n t : Nat}
    (hfirst : FirstAt a g t)
    (hnt : n < t) :
    g ∉ valuesThrough n := by
  intro hmem
  rcases mem_valuesThrough_iff.mp hmem with ⟨u, hun, huvalue⟩
  exact hfirst.2 u (by omega) huvalue

/-- Hence a genuinely new target-smaller value strictly consumes the first
component of the proposed proof-search rank. -/
theorem missingBelowCount_strict_of_firstAt
    {g m n t : Nat}
    (hg : g < m)
    (hnt : n < t)
    (hfirst : FirstAt a g t) :
    missingBelowCount m t < missingBelowCount m n := by
  apply missingBelowCount_strict_of_new hg (Nat.le_of_lt hnt)
  · exact firstAt_not_mem_valuesThrough_before hfirst hnt
  · rw [← hfirst.1]
    exact current_mem_valuesThrough t

/-- Proof-search rank: first count how many values below the target are still
missing, then use the ordinary parent value. -/
def historyBudgetRank (m : Nat) (node : Occurrence) : Nat × Nat :=
  (missingBelowCount m node.time, node.value)

/-- Lexicographic progress for the history-aware search.  A child is smaller
when it consumes at least one missing target-smaller value, or when the budget
is unchanged and the ordinary value decreases. -/
def HistoryBudgetProgress (m : Nat)
    (child parent : Occurrence) : Prop :=
  Prod.Lex Nat.lt Nat.lt
    (historyBudgetRank m child) (historyBudgetRank m parent)

/-- Lexicographic order on pairs of natural numbers is well founded. -/
theorem natPairLex_wellFounded :
    WellFounded (Prod.Lex Nat.lt Nat.lt) := by
  apply WellFounded.intro
  intro p
  exact Prod.lexAccessible
    (Nat.lt_wfRel.wf.apply p.1)
    (fun b => Nat.lt_wfRel.wf.apply b)
    p.2

/-- The proposed history-aware proof-search relation is therefore well
founded. -/
theorem historyBudgetProgress_wellFounded (m : Nat) :
    WellFounded (HistoryBudgetProgress m) := by
  apply WellFounded.intro
  intro node
  generalize hx : historyBudgetRank m node = x
  have hacc : Acc (Prod.Lex Nat.lt Nat.lt) x :=
    natPairLex_wellFounded.apply x
  induction hacc generalizing node with
  | intro x _ ih =>
      apply Acc.intro node
      intro child hchild
      have hrank : Prod.Lex Nat.lt Nat.lt
          (historyBudgetRank m child) x := by
        simpa [HistoryBudgetProgress, hx] using hchild
      exact ih (historyBudgetRank m child) hrank child rfl

/-- A newly consumed missing value gives the left lexicographic branch. -/
theorem historyBudgetProgress_of_budgetDrop
    {m childTime childValue parentTime parentValue : Nat}
    (hdrop : missingBelowCount m childTime <
      missingBelowCount m parentTime) :
    HistoryBudgetProgress m
      ⟨childValue, childTime⟩ ⟨parentValue, parentTime⟩ := by
  exact Prod.Lex.left _ _ hdrop

/-- If history only grows and the ordinary value drops, either the budget has
already dropped or the right lexicographic branch applies. -/
theorem historyBudgetProgress_of_valueDrop
    {m childTime childValue parentTime parentValue : Nat}
    (htime : parentTime ≤ childTime)
    (hvalue : childValue < parentValue) :
    HistoryBudgetProgress m
      ⟨childValue, childTime⟩ ⟨parentValue, parentTime⟩ := by
  have hbudget := missingBelowCount_antitone
    (m := m) htime
  rcases Nat.eq_or_lt_of_le hbudget with heq | hlt
  · change Prod.Lex Nat.lt Nat.lt
      (missingBelowCount m childTime, childValue)
      (missingBelowCount m parentTime, parentValue)
    rw [heq]
    exact Prod.Lex.right _ hvalue
  · exact Prod.Lex.left _ _ hlt

/-- Lexicographic strict order on pairs of naturals is transitive. -/
theorem natPairLex_trans {x y z : Nat × Nat}
    (hxy : Prod.Lex Nat.lt Nat.lt x y)
    (hyz : Prod.Lex Nat.lt Nat.lt y z) :
    Prod.Lex Nat.lt Nat.lt x z := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  rcases z with ⟨za, zb⟩
  cases hxy with
  | left _ _ hleftXY =>
      cases hyz with
      | left _ _ hleftYZ =>
          exact Prod.Lex.left _ _ (Nat.lt_trans hleftXY hleftYZ)
      | right _ _ =>
          exact Prod.Lex.left _ _ hleftXY
  | right _ hrightXY =>
      cases hyz with
      | left _ _ hleftYZ =>
          exact Prod.Lex.left _ _ hleftYZ
      | right _ hrightYZ =>
          exact Prod.Lex.right _ (Nat.lt_trans hrightXY hrightYZ)

/-- History-budget progress composes.  This is the transitivity needed when a
regular subtraction prefix is followed by a local low-quotient step. -/
theorem HistoryBudgetProgress.trans {m : Nat} {x y z : Occurrence}
    (hxy : HistoryBudgetProgress m x y)
    (hyz : HistoryBudgetProgress m y z) :
    HistoryBudgetProgress m x z := by
  exact natPairLex_trans hxy hyz

/-- A proof-search state keeps three notions separate:

* `horizon`: how much of the real orbit history is currently available;
* `parentValue`: the active first-occurrence parent which a blocker must lower;
* `orbitValue`: the value of the later dynamic state being explored.

Conflating the first-occurrence time with the forward history horizon would
make blocker steps appear to move history backwards. -/
structure HistorySearchNode where
  horizon : Nat
  parentValue : Nat
  orbitValue : Nat
deriving Repr, DecidableEq

/-- Three-component search rank.  New target-smaller occurrences have highest
priority, blocker parent descent has second priority, and local orbit-value
descent is the final tie breaker. -/
def historySearchRank (m : Nat) (node : HistorySearchNode) :
    Nat × (Nat × Nat) :=
  (missingBelowCount m node.horizon,
    (node.parentValue, node.orbitValue))

def HistorySearchProgress (m : Nat)
    (child parent : HistorySearchNode) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
    (historySearchRank m child) (historySearchRank m parent)

/-- The right-nested lexicographic order on triples of naturals is well
founded. -/
theorem natTripleLex_wellFounded :
    WellFounded (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) := by
  apply WellFounded.intro
  intro p
  exact Prod.lexAccessible
    (Nat.lt_wfRel.wf.apply p.1)
    (fun pair => natPairLex_wellFounded.apply pair)
    p.2

/-- The triple order is also transitive. -/
theorem natTripleLex_trans {x y z : Nat × (Nat × Nat)}
    (hxy : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) x y)
    (hyz : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) y z) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) x z := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  rcases z with ⟨za, zb⟩
  cases hxy with
  | left _ _ hleftXY =>
      cases hyz with
      | left _ _ hleftYZ =>
          exact Prod.Lex.left _ _ (Nat.lt_trans hleftXY hleftYZ)
      | right _ _ =>
          exact Prod.Lex.left _ _ hleftXY
  | right _ hrightXY =>
      cases hyz with
      | left _ _ hleftYZ =>
          exact Prod.Lex.left _ _ hleftYZ
      | right _ hrightYZ =>
          exact Prod.Lex.right _
            (natPairLex_trans hrightXY hrightYZ)

/-- Pulling the triple order back along `historySearchRank` preserves well
foundedness. -/
theorem historySearchProgress_wellFounded (m : Nat) :
    WellFounded (HistorySearchProgress m) := by
  apply WellFounded.intro
  intro node
  generalize hx : historySearchRank m node = x
  have hacc : Acc (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) x :=
    natTripleLex_wellFounded.apply x
  induction hacc generalizing node with
  | intro x _ ih =>
      apply Acc.intro node
      intro child hchild
      have hrank : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
          (historySearchRank m child) x := by
        simpa [HistorySearchProgress, hx] using hchild
      exact ih (historySearchRank m child) hrank child rfl

theorem HistorySearchProgress.trans {m : Nat}
    {x y z : HistorySearchNode}
    (hxy : HistorySearchProgress m x y)
    (hyz : HistorySearchProgress m y z) :
    HistorySearchProgress m x z := by
  exact natTripleLex_trans hxy hyz

/-- Discovering a new value below the target strictly lowers the first rank
component, independently of both value components. -/
theorem historySearchProgress_of_budgetDrop
    {m childHorizon childParent childOrbit
      parentHorizon parentParent parentOrbit : Nat}
    (hdrop : missingBelowCount m childHorizon <
      missingBelowCount m parentHorizon) :
    HistorySearchProgress m
      ⟨childHorizon, childParent, childOrbit⟩
      ⟨parentHorizon, parentParent, parentOrbit⟩ := by
  exact Prod.Lex.left _ _ hdrop

/-- With a nondecreasing history horizon, a blocker lowering the active
parent value strictly lowers the second rank component unless the history
budget has already fallen. -/
theorem historySearchProgress_of_parentDrop
    {m childHorizon childParent childOrbit
      parentHorizon parentParent parentOrbit : Nat}
    (htime : parentHorizon ≤ childHorizon)
    (hparent : childParent < parentParent) :
    HistorySearchProgress m
      ⟨childHorizon, childParent, childOrbit⟩
      ⟨parentHorizon, parentParent, parentOrbit⟩ := by
  have hbudget := missingBelowCount_antitone
    (m := m) htime
  rcases Nat.eq_or_lt_of_le hbudget with heq | hlt
  · change Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
      (missingBelowCount m childHorizon, (childParent, childOrbit))
      (missingBelowCount m parentHorizon, (parentParent, parentOrbit))
    rw [heq]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hparent)
  · exact Prod.Lex.left _ _ hlt

/-- If the parent obligation is unchanged and history only grows, a local
orbit-value decrease strictly lowers the final rank component unless the
history budget has already fallen. -/
theorem historySearchProgress_of_orbitValueDrop
    {m childHorizon parentHorizon parentValue
      childOrbit parentOrbit : Nat}
    (htime : parentHorizon ≤ childHorizon)
    (horbit : childOrbit < parentOrbit) :
    HistorySearchProgress m
      ⟨childHorizon, parentValue, childOrbit⟩
      ⟨parentHorizon, parentValue, parentOrbit⟩ := by
  have hbudget := missingBelowCount_antitone
    (m := m) htime
  rcases Nat.eq_or_lt_of_le hbudget with heq | hlt
  · change Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
      (missingBelowCount m childHorizon, (parentValue, childOrbit))
      (missingBelowCount m parentHorizon, (parentValue, parentOrbit))
    rw [heq]
    exact Prod.Lex.right _ (Prod.Lex.right _ horbit)
  · exact Prod.Lex.left _ _ hlt

/-- Inserting a fixed middle component embeds the two-coordinate local rank
into the three-coordinate search rank. -/
theorem natPairLex_embed_fixedMiddle (middle : Nat)
    {x y : Nat × Nat}
    (hxy : Prod.Lex Nat.lt Nat.lt x y) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
      (x.1, (middle, x.2)) (y.1, (middle, y.2)) := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  cases hxy with
  | left _ _ hleft =>
      exact Prod.Lex.left _ _ hleft
  | right _ hright =>
      exact Prod.Lex.right _ (Prod.Lex.right _ hright)

/-- Consequently every local `HistoryBudgetProgress` step becomes a search
step while an arbitrary active parent value is kept fixed. -/
theorem HistoryBudgetProgress.toHistorySearchProgress
    {m : Nat} {child parent : Occurrence}
    (hprogress : HistoryBudgetProgress m child parent)
    (activeParent : Nat) :
    HistorySearchProgress m
      ⟨child.time, activeParent, child.value⟩
      ⟨parent.time, activeParent, parent.value⟩ := by
  exact natPairLex_embed_fixedMiddle activeParent hprogress

/-- Abstract oracle for the history-aware proof search.  Every node either
already witnesses the fixed target somewhere on the real orbit, or supplies
a strictly smaller node in the three-component rank. -/
def HistorySearchOracle (m : Nat) : Prop :=
  ∀ parent : HistorySearchNode,
    (∃ t, a t = m) ∨
      ∃ child : HistorySearchNode,
        HistorySearchProgress m child parent

/-- Well-founded induction on the triple rank turns a total history-search
oracle into an actual occurrence of the target, from every starting node. -/
theorem historySearchOracle_reaches_from {m : Nat}
    (horacle : HistorySearchOracle m)
    (start : HistorySearchNode) :
    ∃ t, a t = m := by
  apply (historySearchProgress_wellFounded m).induction start
  intro parent ih
  rcases horacle parent with hoccurs | ⟨child, hprogress⟩
  · exact hoccurs
  · exact ih child hprogress

/-- In particular, one total history-search oracle proves occurrence of its
target without needing a separately chosen initial state. -/
theorem historySearchOracle_implies_occurs {m : Nat}
    (horacle : HistorySearchOracle m) :
    ∃ t, a t = m := by
  exact historySearchOracle_reaches_from horacle ⟨0, 0, 0⟩

end Recaman
