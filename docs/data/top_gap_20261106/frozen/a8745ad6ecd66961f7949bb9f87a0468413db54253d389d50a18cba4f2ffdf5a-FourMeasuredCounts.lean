import Recaman.FourthActualSeven
import Recaman.InitialSTargetBounds

namespace Recaman.FourMeasuredCounts

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Keep the actual head and last-ray counts separate at the same base.
The separator does not add a supplied clock. -/
theorem measured_counts (f : Nat → Bool) (n h M m L s U v T : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    :
    let H:=h+M+m+L+s+U
    let B:=H+v
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    let A:=cN (fun x=>f x=true) n (B+T)
    let F:=cN P n (B+T)
    let EH:=cN (EndN f 0) n H
    let E:=cN (EndN f 0) (n+B) T
    let r:=cN P n H
    EH≤10 ∧ E≤7 ∧ A=EH+E+F ∧ T+r≤F+E ∧ (r≤3 → EH≤r+1) ∧
    seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) := by
  dsimp only
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  have hh : 1≤h := by
    by_cases hz : h=0
    · have ha : f n=true := by simpa only [hz,Nat.add_zero] using hA 0 hM
      have hp:=hpos 1 (by omega) (by omega)
      have hs0 : cN (fun x=>f x=false) n 1=0 := by simp [cN,ha]
      omega
    · omega
  have hhead10 : cN (EndN f 0) n H≤10 :=
    Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
      (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hlast7 : cN (EndN f 0) (n+B) T≤7 := by
    have hl:=Recaman.FourthActualSeven.fourth_actual_seven f n h M m L s U v T w hw hpre hh hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4
    simpa only [B,H,Nat.add_assoc] using hl
  have hsep : cN (EndN f 0) (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxv he
    have ha:=he.1
    rw [hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxv; omega)] at ha
    contradiction
  have hsplit : cN (EndN f 0) n (B+T)=cN (EndN f 0) n H+cN (EndN f 0) (n+B) T := by
    rw [cN_add,cN_add (EndN f 0) n H v,hsep,Nat.add_zero]
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by
    simpa only [B,H,Nat.add_assoc] using hA4
  have hpT:=addition_endable_partition f (n+B) T
  rw [count_A_run f (n+B) T hA4'] at hpT
  change T=cN (EndN f 0) (n+B) T+cN P (n+B) T at hpT
  have hf := cN_add P n B T
  have hfH := cN_add P n H v
  change cN P n B=cN P n H+cN P (n+H) v at hfH
  change F=cN P n B+cN P (n+B) T at hf
  have hpart:=addition_endable_partition f n (B+T)
  rw [hsplit] at hpart
  change A=cN (EndN f 0) n H+cN (EndN f 0) (n+B) T+F at hpart
  have hfree : T+r≤F+cN (EndN f 0) (n+B) T := by omega
  have hrsmall (hr : r≤3) : cN (EndN f 0) n H≤r+1 := by
    have hb:=positive_r3_additions_free_bound f n 0 H hw (by simpa using hpre)
      (fun k hk hkH=>hpos k hk (by omega)) hr
    change cN (fun x=>f x=true) n H≤2*r+1 at hb
    have hp:=addition_endable_partition f n H
    change cN (fun x=>f x=true) n H=cN (EndN f 0) n H+r at hp
    omega
  have hword : seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) := by
    have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U
      hS hA hS2 hA2 hS3 hA3
    rw [show B=H+v by rfl,seg_add,seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
    rw [show H=h+M+m+L+s+U by rfl,hhead]
    simp only [List.append_assoc]
  exact ⟨hhead10,hlast7,hpart,hfree,hrsmall,hword⟩

end Recaman.FourMeasuredCounts
