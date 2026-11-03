import Recaman.KFiveHeadSources
import Recaman.NonsquareActualSupply
import Recaman.HeadRunSupplyBudgets

namespace Recaman.KFiveHeadActual

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The symbolic K5 source filter bounds the actual S7 head at all
old histories. No table of heads or actual free conclusion is an input. -/
theorem K_five_head_three (f : Nat → Bool) (n h M m L s U : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hS7 : h+m+s=7)
    (hK : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true) :
    cN (EndN f 0) n (h+M+m+L+s+U)≤3 := by
  have hb:=Recaman.KFiveHeadSources.K_five_bounds M m L s hM hm hL hs hK
  have hfirst:=Recaman.HeadRunSupplyBudgets.first_two_zero f n h M w hw hpre hb.1 hS hA
  have hword2:=Recaman.SeparatorSupplyReset.three_run_word f n h M m 0 0 0 hS hA hS2
    (by intros; omega) (by intros; omega) (by intros; omega)
  have hp2 : seg f 0 (n+h+M+m)=w++(List.replicate h false++List.replicate M true++List.replicate m false) := by
    rw [show n+h+M+m=n+(h+M+m) by omega,seg_add,Nat.zero_add,hpre]
    congr 1
    simpa only [Nat.add_zero,List.replicate_zero,List.append_nil] using hword2
  have he2:=endable_A_run_count f (n+h+M+m) L _ hp2 hA2
  have hl2:=Recaman.KFiveHeadSources.second_ray_one w hw h M m L s hM hm hL hs hS7 hK
  have hsecond : cN (EndN f 0) (n+h+M+m) L≤1 := by omega
  have hword3:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0
    hS hA hS2 hA2 hS3 (by intros; omega)
  have hp3 : seg f 0 (n+h+M+m+L+s)=w++(List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false) := by
    rw [show n+h+M+m+L+s=n+(h+M+m+L+s) by omega,seg_add,Nat.zero_add,hpre]
    congr 1
    simpa only [Nat.add_zero,List.replicate_zero,List.append_nil] using hword3
  have cntA (a : Nat) : cntF (List.replicate a true)=0 := by
    have he:=mass_cntF (List.replicate a true)
    rw [mass_replicate_A,List.length_replicate] at he
    omega
  have hc3 : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) := by
    simp only [cntF_append,cntF_replicate_S,cntA]
    omega
  have ho3:=block_rayCount_append hw _ hc3 U
  have hl3:=Recaman.KFiveHeadSources.third_ray_one h M m L s U hM hm hL hs hK
  have he3:=endable_A_run_count f (n+h+M+m+L+s) U _ hp3 hA3
  have hthird : cN (EndN f 0) (n+h+M+m+L+s) U≤2 := by omega
  have hpref:=Recaman.HeadRunSupplyBudgets.two_prefix_count f n h M m L hS hS2
  have hz : cN (EndN f 0) (n+h+M+m+L) s=0 := by
    apply cN_zero_of
    intro x hx hxB he
    have hf:=hS3 x hx hxB
    have ha:=he.1
    rw [hf] at ha
    contradiction
  have hc1:=cN_add (EndN f 0) n (h+M+m+L) s
  have hc2:=cN_add (EndN f 0) n (h+M+m+L+s) U
  simp only [Nat.add_assoc] at hpref hfirst hsecond hthird hz hc1 hc2 ⊢
  omega

end Recaman.KFiveHeadActual
