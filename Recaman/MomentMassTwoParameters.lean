import Recaman.MomentMassOneBase

namespace Recaman.MomentMassTwoParameters

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentActualTarget Recaman.MomentNoOld Recaman.MomentRunResidual
open Recaman.MomentTargetProfile Recaman.MomentSmallHeadPruning Recaman.MomentMassOneBase

/-- The target key and integer head moment reduce the mass-two
counter parameters to nine groups. These scalar premises are supplied
from the unchanged actual history in the theorem below. -/
theorem mass_two_parameter_numbers (S v T j : Nat) (B I K : Int)
    (hS : S≤16) (hv : 1≤v) (hv3 : v≤3) (hj : 4≤j) (hhead : S≤j+10)
    (hbal : T+1=v+j) (hkey : K=2*B-8*((S : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2)
    (hK : K=0 ∨ K= -2) (hhi : B≤6*(S : Int)+4) (hmom : B=(S : Int)^2-2*I) :
    j=4 ∧ T=v+3 ∧
      ((v=1 ∧ ((S=12 ∧ B=76) ∨ (S=13 ∧ B=79) ∨ (S=14 ∧ B=84))) ∨
       (v=2 ∧ ((S=12 ∧ B=76) ∨ (S=13 ∧ B=81) ∨ (S=14 ∧ B=84))) ∨
       (v=3 ∧ ((S=12 ∧ B=76) ∨ (S=13 ∧ B=79) ∨ (S=14 ∧ B=84)))) := by
  have hvv : v=1 ∨ v=2 ∨ v=3 := by omega
  have hcircle : ((j : Int)+1)^2≤2*(S : Int)+2 := by
    rcases hvv with rfl|rfl|rfl <;> rcases hK with rfl|rfl <;> grind only
  have hj4 : j=4 := by
    by_cases he : j=4
    · exact he
    · have hp:=Int.mul_nonneg (show 0≤(j : Int)-5 by omega) (show 0≤(j : Int)+7 by omega)
      grind only
  have hS14 : S≤14 := by omega
  have hS12 : 12≤S := by
    rcases hvv with rfl|rfl|rfl <;> rcases hK with rfl|rfl <;> rw [hj4] at hkey <;> omega
  have hSv : S=12 ∨ S=13 ∨ S=14 := by omega
  refine ⟨hj4,by omega,?_⟩
  rw [hj4] at hkey
  rcases hvv with rfl|rfl|rfl <;> rcases hSv with rfl|rfl|rfl <;> rcases hK with rfl|rfl <;> omega

theorem moment_counter_mass_two_parameters (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (B : Int) (haz : areaW (seg f n (h+M+m+L+s+U))= -B)
    (hlo : 4*((h+m+s : Nat) : Int)+6≤B) (hhi : B≤6*((h+m+s : Nat) : Int)+4)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hcounter : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    mass (w.drop t)=2 ∧ j=4 ∧
      cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)=4 ∧ T=v+3 ∧
      ((v=1 ∧ ((h+m+s=12 ∧ B=76) ∨ (h+m+s=13 ∧ B=79) ∨ (h+m+s=14 ∧ B=84))) ∨
       (v=2 ∧ ((h+m+s=12 ∧ B=76) ∨ (h+m+s=13 ∧ B=81) ∨ (h+m+s=14 ∧ B=84))) ∨
       (v=3 ∧ ((h+m+s=12 ∧ B=76) ∨ (h+m+s=13 ∧ B=79) ∨ (h+m+s=14 ∧ B=84)))) := by
  let H:=h+M+m+L+s+U
  let S:=h+m+s
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hr:=moment_run_counter_residual f n t h M m L s U v T j q i w hw hpre ht hh hM hm hL hs hU hzeroMass
    hS hA hS2 hA2 hS3 hA3 hS4 hA4 B haz hlo hhi hv hq hqv hi hband hgap htarget hlocal hpos hcounter
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hne : w.drop t≠[] := by
    have hn : w.length=n := by rw [←hpre,seg_length]
    intro he
    have hl : (w.drop t).length=w.length-t := List.length_drop
    rw [he,hn] at hl
    simp only [List.length_nil] at hl
    omega
  have hCpos : 1≤mass (w.drop t) := (sufPos_block hu [] (w.drop t) rfl hne).1
  have hC2 : mass (w.drop t)=2 := by
    by_cases hC1 : mass (w.drop t)=1
    · have hg:=moment_mass_one_gap f n t h M m L s U v T j q i w hw hpre ht hh hM hm hL hs hU hzeroMass
        hS hA hS2 hA2 hS3 hA3 hS4 hA4 B haz hlo hhi hv hq hqv hi hband hgap htarget hlocal hpos hC1
      omega
    · omega
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=S := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H,S] at *
    omega
  have hc:=actual_moment_target_low_mass f n t H v T j q i w z hw hpre ht rfl hmz B haz
    (by rw [hSz]; exact hlo) (by rw [hSz]; exact hhi) hv hq hqv hi hband
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
    (by simpa only [H,Nat.add_assoc] using hlocal) (by omega)
  have hbalance:=hc.2.2.2.2.2
  rw [hC2] at hbalance
  have hkey:=actual_zero_mass_target_key f n t H v T j w z hpre ht rfl hmz B haz
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  rw [hC2,hSz] at hkey
  have hK : runKey (w.drop t)=0 ∨ runKey (w.drop t)= -2 := by
    rcases block_mass_two hu hC2 with he|he <;> rw [he] <;> decide
  let I : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hmom : B=(S : Int)^2-2*I := by
    have he:=three_head_moment h M m L s U hzeroMass B (by rw [←hhead]; exact haz)
    simpa only [I,S,Int.natCast_add] using he
  have hEhead:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hAcount : cN (fun x=>f x=true) n H=S := by
    have ha:=ones_seg_eq_count f n H
    change ones (seg f n (h+M+m+L+s+U))=_ at ha
    rw [hhead] at ha
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at ha
    dsimp [S]
    omega
  have hpart:=addition_endable_partition f n H
  rw [hAcount] at hpart
  change S=cN (EndN f 0) n H+cN P n H at hpart
  have hadd:=cN_add P n H (v+T)
  have hheadcut : S≤j+10 := by
    change cN (EndN f 0) n H≤10 at hEhead
    change cN P n (H+v+T)<j+1 at hcounter
    rw [show H+(v+T)=H+v+T by omega] at hadd
    omega
  have hn:=mass_two_parameter_numbers S v T j B I (runKey (w.drop t)) hr.1 hv hr.2.1 hr.2.2.1
    hheadcut (by omega) (by grind only) hK hhi hmom
  refine ⟨hC2,hn.1,?_,hn.2.1,hn.2.2⟩
  have hF4:=hr.2.2.2.2.2.2.2.1
  change cN P n (H+v+T)<j+1 at hcounter
  change 4≤cN P n (H+v+T) at hF4
  change cN P n (H+v+T)=4
  omega

end Recaman.MomentMassTwoParameters
