import Recaman.HeadRunCountBounds
import Recaman.HeadUnitPairSupply

namespace Recaman.HeadSaturationCross

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A saturated three-run head forces more AS pairs than the first
two runs' lengths alone. The two unit separators cannot saturate. -/
theorem head_ten_cross_extra_six (f : Nat → Bool) (n h M m L s U : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hhead : 10≤cN (EndN f 0) n (h+M+m+L+s+U)) :
    5≤M+L ∧ M+L+6≤M*(m+s)+L*s := by
  have hh : 1≤h := by
    by_cases hz : h=0
    · have ha : f n=true := by simpa only [hz,Nat.add_zero] using hA 0 hM
      have hp:=hpos 1 (by omega) (by omega)
      have hzS : cN (fun x=>f x=false) n 1=0 := by simp [cN,ha]
      omega
    · omega
  have hM3 : 3≤M := by
    by_cases he : M≤2
    · have h := Recaman.HeadRunCountBounds.head_first_two_eight f n h M m L s U w hw hpre
        hM hm hL hs hU (by omega) hS hA hS2 hA2 hS3 hA3 hpos he
      omega
    · omega
  have hW5 : 5≤M+L := by
    have hp:=addition_endable_partition f n (h+M+m+L)
    have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0
      hS hA hS2 hA2 (by intro x hx hx0; omega) (by intro i hi; omega)
    simp only [Nat.add_zero,List.replicate_zero,List.append_nil] at hword
    have hcount:=ones_seg_eq_count f n (h+M+m+L)
    rw [hword] at hcount
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hcount
    have hbefore : cN (EndN f 0) n (h+M+m+L)≤M+L := by omega
    have he:=Recaman.HeadRunCountBounds.head_from_prefix f n h M m L s U w hw hpre
      hM hm hL hs hU (by omega) hS hA hS2 hA2 hS3 hA3 hpos (M+L) hbefore
    omega
  have hms : 3≤m+s := by
    by_cases he : 3≤m+s
    · exact he
    · have hm1 : m=1 := by omega
      have hs1 : s=1 := by omega
      subst m
      subst s
      have hf:=Recaman.HeadUnitPairSupply.head_unit_pair_eight f n h M L U w hw hpre hh
        hS hA hS2 hA2 hS3 hA3 hpos
      omega
  have hI : M*(m+s)+L*s=M*m+(M+L)*s := by
    rw [Nat.mul_add,Nat.add_mul,Nat.add_assoc]
  refine ⟨hW5,?_⟩
  rw [hI]
  by_cases hm2 : 2≤m
  · have ha : 6≤M*m := Nat.mul_le_mul hM3 hm2
    have hb : M+L≤(M+L)*s := Nat.mul_le_mul (Nat.le_refl _) hs
    omega
  · have hs2 : 2≤s := by omega
    have ha : 3≤M*m := Nat.mul_le_mul hM3 hm
    have hb : (M+L)*2≤(M+L)*s := Nat.mul_le_mul (Nat.le_refl _) hs2
    omega

end Recaman.HeadSaturationCross
