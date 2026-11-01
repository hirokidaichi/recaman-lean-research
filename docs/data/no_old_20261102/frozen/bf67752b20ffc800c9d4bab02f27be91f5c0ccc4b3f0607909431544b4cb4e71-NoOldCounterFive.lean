import Recaman.NoOldTargetBounds
import Recaman.NoOldLocalFive

namespace Recaman.NoOldCounterFive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Necessary conditions for a hypothetical no-old counter. The initial S
source is removed using internally supplied bounds; the original prefix and
all its old masses are retained. This does not assert counter absence. -/
theorem no_old_counter_five (f : Nat → Bool) (n t h M m L s U T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+3 → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+3+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+3+T≤x → x<n+h+M+m+L+s+U+3+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+3+T+j-t))
    (hC : mass (w.drop t)=3)
    (hno : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+3+k-r))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+3+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+3+T)<j+1) :
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)≤4 ∧
    cN (EndN f 0) (n+h+M+m+L+s+U+3) T≤5 ∧ h+m+s≤14 := by
  have hb:=Recaman.NoOldTargetBounds.no_old_counter_bounds f n t h M m L s U T j w hw hpre ht
    hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hno hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  let B : Int:= -areaW z
  have hB : runKey z= -2*B := by
    unfold runKey
    rw [hmz]
    dsimp [B]
    grind only
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hraw:=Recaman.NoOldLocalFive.target_local_count_five (w.drop t) hu hC h M m L s U (j+1) T
    hb.2.1 hzeroMass hb.2.2.1 (by omega) B (by rw [←hhead]; exact hB)
    (by have hk:=hb.2.2.2.2; change runKey (w.drop t)= -runKey z-12*((h : Int)+(m : Int)+(s : Int))-18-2*((j : Int)+1)^2 at hk
        rw [hB] at hk; simpa only [Int.natCast_add,Int.natCast_one] using hk)
  have heq:=Recaman.MomentNoOld.last_count_eq_local f n H 3 T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hno)
  have hlast : cN (EndN f 0) (n+H+3) T≤5 := by
    rw [heq]
    simpa only [z,H,hhead,List.append_assoc] using hraw
  have hsep : cN P (n+H) 3=0 := by
    apply cN_zero_of
    intro x hx hxe hp
    have hf:=hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxe; omega)
    change f x=true ∧ ¬EndN f 0 x at hp
    rw [hf] at hp
    simp at hp
  have hf1:=cN_add P n H 3
  have hf2:=cN_add P n (H+3) T
  have hp:=addition_endable_partition f (n+H+3) T
  rw [count_A_run f (n+H+3) T (by simpa only [H,Nat.add_assoc] using hA4)] at hp
  change T=cN (EndN f 0) (n+H+3) T+cN P (n+H+3) T at hp
  have hfhead : cN P n H≤4 := by
    have hT:=hb.1
    change cN P n (H+3+T)<j+1 at hbad
    simp only [Nat.add_assoc] at hf1 hf2 hp hlast hbad
    omega
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hAh:=ones_seg_eq_count f n H
  change ones (seg f n (h+M+m+L+s+U))=_ at hAh
  rw [hhead] at hAh
  simp only [ones_append,ones_replicate_A,ones_replicate_S] at hAh
  have hph:=addition_endable_partition f n H
  change cN (fun x=>f x=true) n H=cN (EndN f 0) n H+cN P n H at hph
  have hS14 : h+m+s≤14 := by
    change cN (EndN f 0) n H≤10 at hhead10
    change (M : Int)+(L : Int)+(U : Int)=(cN (fun x=>f x=true) n H : Int) at hAh
    omega
  exact ⟨hfhead,by simpa only [H,Nat.add_assoc] using hlast,hS14⟩

end Recaman.NoOldCounterFive
