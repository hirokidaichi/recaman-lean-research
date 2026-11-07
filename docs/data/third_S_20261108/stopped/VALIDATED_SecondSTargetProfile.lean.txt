import Recaman.InitialSTargetBounds
namespace Recaman.SecondSTargetProfile

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse

theorem actual_second_S_target_profile (f : Nat → Bool) (b m L s U v T j t : Nat)
    (hta : b≤t) (htb : t<b+m) (hL : 1≤L) (hs : 1≤s)
    (hS0 : ∀ x, b≤x → x<b+m → f x=false)
    (hA0 : ∀ i, i<L → f (b+m+i)=true)
    (hS : ∀ x, b+m+L≤x → x<b+m+L+s → f x=false)
    (hAU : ∀ i, i<U → f (b+m+L+s+i)=true)
    (hS4 : ∀ x, b+m+L+s+U≤x → x<b+m+L+s+U+v → f x=false)
    (hAT : ∀ i, i<T → f (b+m+L+s+U+v+i)=true)
    (hgap : ∀ x, b+m+L+s+U+v+T≤x → x<b+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (b+m+L+s+U+v+T+j-t)) :
    let q:=b+m-t
    L+U+T=j+1+q+s+v ∧ j+2<q+s+v ∧
      ((q : Int)+(s : Int)+(v : Int))^2-((j : Int)+1)^2=
        2*(L : Int)*((s : Int)+(v : Int))+2*(U : Int)*(v : Int) := by
  dsimp only
  let q:=b+m-t
  have hqe : t+q=b+m := by dsimp [q]; omega
  have hword : seg f t (b+m+L+s+U+v+T+j-t)=
      List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false := by
    have hh:=Recaman.SeparatorSupplyReset.three_run_word f t q L s U v T
      (by intro x hx hxq; exact hS0 x (by omega) (by omega))
      (by simpa only [hqe] using hA0)
      (by simpa only [hqe,Nat.add_assoc] using hS)
      (by simpa only [hqe,Nat.add_assoc] using hAU)
      (by simpa only [hqe,Nat.add_assoc] using hS4)
      (by simpa only [hqe,Nat.add_assoc] using hAT)
    rw [show b+m+L+s+U+v+T+j-t=(q+L+s+U+v+T)+j by omega,seg_add,hh,
      show t+(q+L+s+U+v+T)=b+m+L+s+U+v+T by omega,
      seg_false f (b+m+L+s+U+v+T) j hgap]
  have hm : mass (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=1 := by
    rw [←hword,seg_mass]
    have he:=htarget.2.1
    rw [show t+(b+m+L+s+U+v+T+j-t)=b+m+L+s+U+v+T+j by omega] at he ⊢
    omega
  have ha : areaW (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=0 := by
    rw [←hword,←Ar_areaW]
    exact htarget.2.2
  obtain ⟨hbal,hsq,hstrict,_⟩:=Recaman.InitialSTargetBounds.initial_S_target_equations q L s U v T j hL hs hm ha
  change L+U+T=j+1+q+s+v ∧ _
  exact ⟨by omega,hstrict,hsq⟩

end Recaman.SecondSTargetProfile
