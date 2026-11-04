import Recaman.LowOldActualSix
import Recaman.BoundedOldActualFree
import Recaman.ZeroHeadCounterCost
import Recaman.MixedZeroActualCircle
import Recaman.MassOneTargetCounter
import Recaman.NonsquareActualSupply

namespace Recaman.MassThreeSeedGap


open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_three_seed_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : 1≤v)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hC : mass (w.drop t)=1)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (r i : Nat) (hr : r<n) (hi : i<T)
    (hseed : Win f r (n+h+M+m+L+s+U+v+i-r))
    (hD : mass (w.drop r)=3)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let free:=cN P n H
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by simp only [z,H,hword,mass_append,mass_rep_false,mass_replicate_A]; omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  have hlast:=Recaman.LowOldActualSix.low_old_actual_six f n h M m L s U v T w hw hpre
    hh hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hzeroMass r i hr hi hseed (Or.inr hD)
  have hcost:=Recaman.ZeroHeadCounterCost.counter_count_cost f n H t v T j 1 6 w z hpre rfl hmz ht hC
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
    (by simpa only [H,Nat.add_assoc] using hbad)
    (by simpa only [H,Nat.add_assoc] using hlast)
  change T+1=v+j+1 ∧ free+v+1≤7 at hcost
  have hfree1 : 1≤free := Recaman.ZeroHeadCounterCost.zero_head_free_pos f n H hmz
    (hpos H (by dsimp [H]; omega) (by dsimp [H]; omega))
  have hv5 : v≤5 := by omega
  have hfree4:=Recaman.BoundedOldActualFree.bounded_old_head_free_four f n h M m L s U v T w hw hpre
    hh hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hzeroMass r i hr hi hseed
    (Or.inl ⟨by omega,hv5⟩) hM hL hU (fun k hk hkB=>hpos k hk (by omega))
  change 4≤free at hfree4
  have hpseed:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v i 0 w z hpre hr rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (fun k hk=>by simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intros; omega) (by simpa only [H,Nat.add_zero,Nat.add_assoc] using hseed)
  have hv2 : 2≤v := by
    have he:=hpseed.1
    simp only [mass_append,hmz,hD,mass_rep_false,mass_replicate_A] at he
    omega
  have hveq : v=2 := by omega
  have hfreeeq : free=4 := by omega
  have hc:=Recaman.MixedZeroActualCircle.actual_mixed_old_three_circle f n H t r v T j i w z hw hpre
    rfl hmz ht hr hi hC hD
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using hseed)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hc:=ones_seg_eq_count f n H
    change ones z=_ at hc
    rw [show z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true from hword] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  have hpart:=addition_endable_partition f n H
  rw [hAc] at hpart
  change h+m+s=cN (EndN f 0) n H+free at hpart
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega))
  change cN (EndN f 0) n H≤10 at hhead10
  have hE16 : cntF z+v≤16 := by rw [hSz]; omega
  have hR5:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j 1 w hw hpre ht
    hh hM hm hL hs hU hv rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hj4 : 4≤j := by have hh:=hR5.2.1; omega
  have hR8 : (j : Int)+1≤8 := by
    by_cases hx : (j : Int)+1≤8
    · exact hx
    have hp:=Int.mul_nonneg (show 0≤(j : Int)+1-9 by omega) (show 0≤(j : Int)+1+9 by omega)
    have he:=hc.2.1
    have hE : (cntF z : Int)+(v : Int)≤16 := by omega
    grind only
  have hj7 : j=7 := by
    have heven:=hc.1
    have he:=hc.2.1
    have hEeven:=hc.2.2.2
    rcases (show j=5 ∨ j=7 by omega) with h5|h7
    · rw [h5] at he
      have hx : (cntF z : Int)+(v : Int)=9 := by omega
      rw [hx] at hEeven
      omega
    · exact h7
  have hSz14 : cntF z=14 := by
    have he:=hc.2.1
    rw [hj7,hveq] at he
    omega
  have hhead10eq : cN (EndN f 0) n H=10 := by omega
  let K : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hkz : runKey z=4*K-2*(cntF z : Int)^2 := by
    rw [hSz,show z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true from hword]
    rw [runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
    simp only [Int.natCast_add]
    dsimp [K]
    grind only
  have hkseed:=Recaman.ASourceReuse.source_key_before_gap (w.drop r++z++List.replicate v false) i 0
    (by simpa only [List.replicate_zero,List.append_nil,List.append_assoc] using hpseed.1)
    (by simpa only [List.replicate_zero,List.append_nil,List.append_assoc] using hpseed.2)
  have hkseed' : runKey (w.drop r++z++List.replicate v false)= -2 := by simpa using hkseed
  have hku:=hc.2.2.1
  rw [Recaman.TwoRunSupply.runKey_append_S,runKey_append,mass_append,hD,hmz,hkz,hSz14,hveq,hku] at hkseed'
  have hK52 : K=52 := by omega
  have hthird:=Recaman.NonsquareActualSupply.third_actual_four_between f n h M m L s U 10 w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3
    (by change (10 : Int)^2<2*K+1; omega) (by change 2*K+1<((10 : Int)+1)^2; omega)
  have htwo:=two_run_supply_of_positive f n h M m L w hw hpre hS hA hS2 hA2
    (fun k hk hkB=>hpos k hk (by omega))
  have hs0:=endable_S_count_zero f (n+h+M+m+L) s hS3
  have ha:=cN_add (EndN f 0) n (h+M+m+L) s
  have hb:=cN_add (EndN f 0) n (h+M+m+L+s) U
  have hhead9 : cN (EndN f 0) n H≤9 := by
    simp only [H,Nat.add_assoc] at htwo hs0 ha hb hthird ⊢
    omega
  omega

end Recaman.MassThreeSeedGap
