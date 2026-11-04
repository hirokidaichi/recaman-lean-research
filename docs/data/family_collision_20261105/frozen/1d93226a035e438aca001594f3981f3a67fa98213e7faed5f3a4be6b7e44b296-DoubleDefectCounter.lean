import Recaman.MassOneTargetCounter

namespace Recaman.DoubleDefectCounter

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem double_defect_counter (f : Nat → Bool) (n t h M m L s U v T j μ : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hμ : 1≤μ) (hv : v=μ+2)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) : T=j+2 ∧ 5≤j+1 ∧ M≤j+2 := by
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=(μ : Int) := by
    simp only [z,H,hword,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hT : T=j+2 := by
    have he:=hp.1
    simp only [mass_append,hmz,hC,mass_rep_false,mass_replicate_A] at he
    omega
  have hshape : seg f n (H+v+T)=z++List.replicate v false++List.replicate T true := by
    rw [seg_add,seg_add,show seg f n H=z by rfl,
      seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
    congr 1
    apply seg_A
    intro x hx hxT
    have ha:=hA4 (x-(n+H+v)) (by omega)
    rw [show n+h+M+m+L+s+U+v+(x-(n+H+v))=x by dsimp [H]; omega] at ha
    exact ha
  have hAc : cN (fun x=>f x=true) n (H+v+T)=M+L+U+T := by
    have hc:=ones_seg_eq_count f n (H+v+T)
    rw [hshape] at hc
    change ones (seg f n H++List.replicate v false++List.replicate T true)=_ at hc
    dsimp only [H] at hc
    rw [hword] at hc
    simp only [ones_append,ones_replicate_S,ones_replicate_A] at hc
    dsimp only [H]
    omega
  have hR : 5≤j+1 := by
    by_cases he : 5≤j+1
    · exact he
    have hf : cN P n (H+v+T)≤3 := by change cN P n (H+v+T)<j+1 at hbad; omega
    have hb:=positive_r3_additions_free_bound f n 0 (H+v+T) hw (by simpa using hpre)
      (by simpa only [H,Nat.add_assoc] using hpos) hf
    rw [hAc] at hb
    change M+L+U+T≤2*cN P n (H+v+T)+1 at hb
    change cN P n (H+v+T)<j+1 at hbad
    omega
  have hbudget : M≤j+2 := by
    have hb:=single_A_run_free_budget f n h M w hw hpre hS hA
    have ha:=cN_add P n h M
    have hc:=cN_add P n (h+M) (m+L+s+U+v+T)
    change cN P n (H+v+T)<j+1 at hbad
    dsimp only [H] at hbad
    simp only [P,Nat.add_assoc] at ha hc hb hbad
    omega
  exact ⟨hT,hR,hbudget⟩

end Recaman.DoubleDefectCounter
