import Recaman.EvenOldSourceSum
import Recaman.OldThreeActualParity
import Recaman.MassTwoTargetCounter
import Recaman.NonsquareActualSupply
import Recaman.FourthActualSeven

namespace Recaman.MassTwoShortOldSum

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_two_short_old_sum (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=3 ∨ v=4) (hC2 : C=2)
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
    (hC : mass (w.drop t)=(C : Int))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)

    (r i : Nat) (hr : r<n) (hi : i<T)
    (hseed : Win f r (n+h+M+m+L+s+U+v+i-r))
    (hD : mass (w.drop r)=3)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    h+m+s+v=17 ∧ runKey (w.drop r)=0 ∧ cN (EndN f 0) n (h+M+m+L+s+U)≤9 := by
  have hv1 : 1≤v := by rcases hv with hv|hv <;> omega
  have hb:=Recaman.MassTwoTargetCounter.mass_two_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv1 hC2 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have heven:=Recaman.OldThreeActualParity.actual_old_three_target_even f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv1 hC2 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC r i hr hi hseed hD
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let K : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    dsimp [z,H]
    rw [hword]
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl:=seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  have hp1:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v i 0 w z hpre hr rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (fun k hk=>by simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intros; omega) (by simpa only [H,Nat.add_zero,Nat.add_assoc] using hseed)
  have hseedkey : runKey (w.drop r++z++List.replicate v false)= -2 := by
    have he:=Recaman.ASourceReuse.source_key_before_gap (w.drop r++z++List.replicate v false) i 0 hp1.1 hp1.2
    simpa using he
  obtain ⟨Z,hZ⟩:=Recaman.OldThreeKeyParity.mass_three_seed_parity (w.drop r) h M m L s U v hD hzeroMass
    (by simpa only [z,H,hword] using hseedkey)
  have hseedexpanded:=hseedkey
  rw [runKey_append_S,runKey_append,mass_append,hmz,hD,hSz] at hseedexpanded
  simp only [Int.natCast_add] at hseedexpanded
  have htargetkey:=hb.2.2.2
  rw [hC2] at htargetkey
  change runKey (w.drop t)= -runKey z-8*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 at htargetkey
  have hdiff : runKey (w.drop t)-runKey (w.drop r)=4*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2-2*((j : Int)+1)^2 := by grind only
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega))
  have hlast7:=Recaman.FourthActualSeven.fourth_actual_seven f n h M m L s U v T w hw hpre
    hh hm hs hv1 hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hx:=ones_seg_eq_count f n H
    dsimp [H] at hx ⊢
    rw [hword] at hx
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
    omega
  have hpart:=addition_endable_partition f n H
  rw [hAc] at hpart
  change h+m+s=cN (EndN f 0) n H+cN P n H at hpart
  have hf1:=cN_add P n H v
  have hf2:=cN_add P n (H+v) T
  have hlastpart:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hlastpart
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hlastpart
  change cN P n (H+v+T)<j+1 at hbad
  have hT:=hb.1
  have hcost : cN P n H+v≤8 := by
    simp only [H,Nat.add_assoc] at hf1 hf2 hlastpart hlast7 hbad ⊢
    omega
  have hE18 : h+m+s+v≤18 := by
    simp only [H,Nat.add_assoc] at hpart hhead10 hcost
    omega
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hur:=block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have hku:=Recaman.MassTwoThreeKeys.mass_two_keys (w.drop t) hu (by omega)
  have hks:=Recaman.MassTwoThreeKeys.mass_three_keys (w.drop r) hur hD
  have he:=Recaman.EvenOldSourceSum.even_source_sum ((j : Int)+1) ((h : Int)+(m : Int)+(s : Int)+(v : Int))
    (runKey (w.drop t)) (runKey (w.drop r)) Z (by have hx:=hb.2.1; omega) (by omega) heven hku hks hZ hdiff
  have hheadkey : runKey z=4*K-2*((h : Int)+(m : Int)+(s : Int))^2 := by
    dsimp [z,H]
    rw [hword,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
    dsimp [K]
    grind only
  have hkey : runKey (w.drop t)=2*((h : Int)+(m : Int)+(s : Int))^2-4*K-
      8*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-72 := by
    rw [hheadkey] at htargetkey
    have hr6:=he.1
    rw [hr6] at htargetkey
    grind only
  obtain ⟨a,hlo,hhi⟩:=Recaman.EvenOldSourceSum.sum_nonsquare ((h : Int)+(m : Int)+(s : Int)) (v : Int) K
    (runKey (w.drop t)) (by rcases hv with hv|hv <;> omega)
    (by rcases he.2 with h17|h18; exact Or.inl ⟨h17.1,h17.2.1⟩; exact Or.inr ⟨h18.1,h18.2.1⟩) hkey
  have hthird:=Recaman.NonsquareActualSupply.third_actual_four_between f n h M m L s U a w hw hpre hs (by omega)
    hS hA hS2 hA2 hS3 hA3 hlo hhi
  have hpref:=Recaman.ThreeRunSupplyBudget.two_run_supply_of_positive f n h M m L w hw hpre hS hA hS2 hA2
    (fun hp=>hpos (h+M+m+L) hp (by omega))
  have hzS : cN (EndN f 0) (n+h+M+m+L) s=0 := by
    apply cN_zero_of
    intro x hx hxB hE
    have ha:=hE.1
    rw [hS3 x hx hxB] at ha
    contradiction
  have h1:=cN_add (EndN f 0) n (h+M+m+L) s
  have h2:=cN_add (EndN f 0) n (h+M+m+L+s) U
  have hhead9 : cN (EndN f 0) n H≤9 := by
    dsimp [H]
    simp only [Nat.add_assoc] at hpref hthird hzS h1 h2 ⊢
    omega
  have hE17 : h+m+s+v≤17 := by
    simp only [H,Nat.add_assoc] at hpart hcost hhead9
    omega
  refine ⟨?_,?_,hhead9⟩
  · rcases he.2 with h17|h18 <;> omega
  · rcases he.2 with h17|h18 <;> omega

end Recaman.MassTwoShortOldSum
