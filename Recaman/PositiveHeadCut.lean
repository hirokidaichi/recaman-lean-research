import Recaman.PositiveHeadCounter
import Recaman.UnitDefectLocalFour
import Recaman.UnitDefectCost
import Recaman.MomentNoOld

namespace Recaman.PositiveHeadCut

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.UnitTargetSASProfile

theorem positive_head_cut (f : Nat → Bool) (n t h M m L s U v T j μ : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hμ : 1≤μ) (hv : v=μ+1)
    (hheadMass : M+L+U=h+m+s+μ)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) : μ≤3 ∧
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)≤4 ∧
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤5 ∧
    ((∀ i, i<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+i-r)) → μ≤2 ∧
      cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)≤3) := by
  have hb:=Recaman.PositiveHeadCounter.positive_head_counter f n t h M m L s U v T j μ w hw hpre ht
    hh hM hm hL hs hU hμ hv hheadMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hzeq : z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true := hword
  have hmz : mass z=(μ : Int) := by rw [hzeq]; simp only [mass_append,mass_rep_false,mass_replicate_A]; omega
  have hSz : cntF z=h+m+s := by rw [hzeq]; simp only [cntF_append,cntF_A,cntF_replicate_S]; omega
  have hAc : cN (fun x=>f x=true) n H=M+L+U := by
    have hc:=ones_seg_eq_count f n H
    change ones z=_ at hc
    rw [hzeq] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hu1 : w.drop t=[true] := block_mass_one hu hC
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hT : T=j+1 := hb.1
  have hR : 5≤j+1 := hb.2.1
  have hlocal:=Recaman.UnitDefectLocalFour.fourth_local_four h M m L s U v T j (by omega)
    (by omega) hM hb.2.2
    (by rw [←hzeq,hmz]; omega)
    (by simpa only [hu1,hzeq,hT,List.append_assoc] using hp.1)
    (by simpa only [hu1,hzeq,hT,List.append_assoc] using hp.2)
  have hlocal4 : rayCount (z++List.replicate v false) T≤4 := by
    simpa only [hzeq,List.append_assoc] using hlocal
  have hshape : seg f 0 (n+H+v)=w++(z++List.replicate v false) := by
    rw [show n+H+v=n+(H+v) by omega,seg_add,Nat.zero_add,hpre,seg_add]
    rw [seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
  have hcount:=endable_A_run_count f (n+H+v) T _ hshape
    (by simpa only [H,Nat.add_assoc] using hA4)
  have hlast5 : cN (EndN f 0) (n+H+v) T≤5 := by
    have hc : 3≤cntF (z++List.replicate v false) := by rw [cntF_append,cntF_replicate_S,hSz]; omega
    have ha:=block_rayCount_append hw (z++List.replicate v false) hc T
    rw [hcount]
    omega
  have hc:=Recaman.UnitDefectCost.counter_cost f n H v T j 5 hT
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hbad) hlast5
  have hf:=Recaman.UnitDefectCost.mass_free_charge f n H (hpos H (by dsimp [H]; omega) (by dsimp [H]; omega))
  change mass z+1≤(cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H : Int) at hf
  rw [hmz] at hf
  refine ⟨by omega,by simpa only [H] using (show cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H≤4 by omega),
    by simpa only [H,Nat.add_assoc] using hlast5,?_⟩
  intro hno
  have he:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hno)
  have hc4:=Recaman.UnitDefectCost.counter_cost f n H v T j 4 hT
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hbad) (by rw [he]; exact hlocal4)
  exact ⟨by omega,by simpa only [H] using (show cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H≤3 by omega)⟩

end Recaman.PositiveHeadCut
