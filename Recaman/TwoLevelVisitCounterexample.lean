import Recaman.InitialSPaddingPositive
import Recaman.AdditionRankSlack

namespace Recaman.TwoLevelVisitCounterexample

open Recaman.InitialSPaddingPositive Recaman.AdditionRankSlack
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.ThreeNonsuppliedData
open Recaman.ShortPeriodicSupply (sign)

private def f : Nat → Bool := finiteSign
  [false,false,true,true,true,false,false,false,false,true,true,true,true,false,true]
private def actual (t : Nat) : Prop := t=4 ∨ t=11 ∨ t=12 ∨ t=14

private theorem supplied_iff (t : Nat) (ht : t<15) : EndN f 0 t ↔ actual t := by
  have hc : ∀ q : Fin 15,
      (f q=true ∧ localSupply (seg f 0 q)=true) ↔ actual q := by
    unfold actual f
    decide
  constructor
  · intro he
    exact (hc ⟨t,ht⟩).mp ⟨he.1,(localSupply_seg_iff f 0 t (by omega) he.1).mpr he⟩
  · intro ha
    have hp := (hc ⟨t,ht⟩).mpr ha
    exact (localSupply_seg_iff f 0 t (by omega) hp.1).mp hp.2

/-- An original-positive history of depth three defeats both the
unrestricted two-level recurrence and the resulting all-visit payment. -/
theorem positive_two_level_visit_counter :
    (∀ k, 0<k → k≤15 → cN (EndN f 0) 0 k+1≤cN (fun i => f i=false) 0 k) ∧
    Fw f 15=1 ∧
    cN (fun q => Fw f q=0) 0 15=5 ∧
    cN (fun q => Fw f q= -2) 0 15=3 ∧
    cN (fun q => f q=true ∧ ¬EndN f 0 q ∧ -2<Fw f q ∧ Fw f q≤0) 0 15=1 ∧
    cN (fun q => f q=true ∧ ¬EndN f 0 q ∧ Fw f q≤0) 0 15=4 := by
  have hpositive : ∀ k : Fin 16, 0<k.val →
      cN actual 0 k.val+1≤cN (fun i => f i=false) 0 k.val := by
    intro k hk
    obtain ⟨k,hk16⟩ := k
    change 0<k at hk
    have h : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [cN,actual,f,finiteSign]
  refine ⟨?_,by decide,by simp [cN,f,finiteSign,Fw,sign],by simp [cN,f,finiteSign,Fw,sign],?_,?_⟩
  · intro k hk hk15
    have hE : cN (EndN f 0) 0 k=cN actual 0 k := by
      apply cN_congr
      intro t _ ht
      exact supplied_iff t (by omega)
    rw [hE]
    exact hpositive ⟨k,by omega⟩ hk
  · rw [cN_congr _ (fun q => f q=true ∧ ¬actual q ∧ -2<Fw f q ∧ Fw f q≤0)
      0 15 (fun q _ hq => by rw [supplied_iff q (by omega)])]
    simp [cN,actual,f,finiteSign,Fw,sign]
  · rw [cN_congr _ (fun q => f q=true ∧ ¬actual q ∧ Fw f q≤0)
      0 15 (fun q _ hq => by rw [supplied_iff q (by omega)])]
    simp [cN,actual,f,finiteSign,Fw,sign]

end Recaman.TwoLevelVisitCounterexample
