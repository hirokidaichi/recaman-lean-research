import Recaman.InitialSTargetBounds

namespace Recaman.ThreeHeadFreeCuts

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Both early A-run costs are bounded by the same actual head free
count. The first-two cost uses the original positive walk. -/
theorem head_free_cuts (f : Nat → Bool) (n h M m L s U : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    let r:=cN P n (h+M+m+L+s+U)
    M≤r+2 ∧ M+L≤r+5 := by
  dsimp only
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let Q:=h+M+m+L
  let H:=Q+s+U
  let r:=cN P n H
  change M≤r+2 ∧ M+L≤r+5
  have hfirst : M≤cN P (n+h) M+2 := single_A_run_free_budget f n h M w hw hpre hS hA
  have h1:=cN_add P n h M
  have h2:=cN_add P n (h+M) (m+L)
  rw [show h+M+(m+L)=Q by dsimp [Q]; omega] at h2
  change cN P n Q=cN P n (h+M)+cN P (n+(h+M)) (m+L) at h2
  have h3:=cN_add P n Q (s+U)
  rw [show Q+(s+U)=H by dsimp [H]; omega] at h3
  change r=cN P n Q+cN P (n+Q) (s+U) at h3
  have hsupply : cN (EndN f 0) n Q≤5 :=
    Recaman.ThreeRunSupplyBudget.two_run_supply_of_positive f n h M m L w hw hpre hS hA hS2 hA2
      (fun hk=>hpos _ hk (by omega))
  have hword := Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0 hS hA hS2 hA2
    (by intro x hx hx0; omega) (by intro i hi; omega)
  have hAcount : cN (fun x=>f x=true) n Q=M+L := by
    have ho:=ones_seg_eq_count f n Q
    change seg f n Q=_ at hword
    rw [hword] at ho
    simp only [List.replicate_zero,List.append_nil,ones_append,ones_replicate_A,ones_replicate_S] at ho
    omega
  have hp:=addition_endable_partition f n Q
  change cN (fun x=>f x=true) n Q=cN (EndN f 0) n Q+cN P n Q at hp
  omega

end Recaman.ThreeHeadFreeCuts
