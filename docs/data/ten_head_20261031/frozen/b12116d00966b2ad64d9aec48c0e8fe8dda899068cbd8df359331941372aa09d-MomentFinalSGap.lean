import Recaman.MomentMassTwoParameters
import Recaman.MomentMassTwoLocal
import Recaman.MomentMassTwoThreeGap

namespace Recaman.MomentFinalSGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentActualTarget Recaman.MomentNoOld Recaman.MomentMassTwoParameters
open Recaman.MomentMassTwoLocal Recaman.MomentMassTwoThreeGap

/-- Every zero-mass moment-band positive three-run head satisfies the
actual final-S-source free-gap, with unrestricted head/old/future lengths.
The mass-one and mass-two branches are supplied and discharged internally. -/
theorem moment_final_S_free_gap (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
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
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  · have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
    let H:=h+M+m+L+s+U
    let S:=h+m+s
    let z:=seg f n H
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    have hp:=moment_counter_mass_two_parameters f n t h M m L s U v T j q i w hw hpre ht hh hM hm hL hs hU hzeroMass
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 B haz hlo hhi hv hq hqv hi hband hgap htarget hlocal hpos hbad
    have hj4 : j=4 := hp.2.1
    have hT : T=v+3 := hp.2.2.2.1
    have hFfull : cN P n (H+v+T)=4 := hp.2.2.1
    have hrows :
      (v=1 ∧ ((S=12 ∧ B=76) ∨ (S=13 ∧ B=79) ∨ (S=14 ∧ B=84))) ∨
      (v=2 ∧ ((S=12 ∧ B=76) ∨ (S=13 ∧ B=81) ∨ (S=14 ∧ B=84))) ∨
      (v=3 ∧ ((S=12 ∧ B=76) ∨ (S=13 ∧ B=79) ∨ (S=14 ∧ B=84))) := hp.2.2.2.2
    have hS12 : 12≤S := by
      rcases hrows with h|h|h <;> rcases h.2 with h|h|h <;> omega
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
    have hno:=actual_moment_no_old f n H t v T j w z hw hpre ht rfl hmz B haz
      (by rw [hSz]; exact hlo) (by rw [hSz]; exact hhi) hv hc.2.2.1 (by omega)
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4)
      (by simpa only [H,Nat.add_assoc] using hgap)
      (by simpa only [H,Nat.add_assoc] using htarget)
    have heq:=last_count_eq_local f n H v T z rfl
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4) hno
    have hrawarea : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true)= -B := by rw [←hhead]; exact haz
    have hAsum : M+L+U=S := by dsimp [S]; omega
    have hlocalbound : rayCount (z++List.replicate v false) T≤v+2 := by
      rw [hT]
      rcases hrows with ⟨hv1,hSB⟩|⟨hv2,hSB⟩|⟨hv3,hSB⟩
      · subst v
        have hb:=mass_two_short_local_budget h M m L s U S 1 hh hs rfl hAsum B hrawarea hlo hhi
          (Or.inl ⟨rfl,by rcases hSB with h|h|h <;> omega,by rcases hSB with h|h|h <;> omega,
            by rcases hSB with h|h|h <;> omega⟩)
        simpa only [z,H,hhead,List.append_assoc] using hb
      · subst v
        have hb:=mass_two_short_local_budget h M m L s U S 2 hh hs rfl hAsum B hrawarea hlo hhi (Or.inr ⟨rfl,hSB⟩)
        simpa only [z,H,hhead,List.append_assoc] using hb
      · subst v
        have hb:=mass_two_three_local_budget h M m L s U S hh hM hm hL hs hU rfl hAsum B hrawarea hlo hhi hSB
        simpa only [z,H,hhead,List.append_assoc,Nat.reduceAdd] using hb
    have hlast : cN (EndN f 0) (n+H+v) T≤v+2 := by rw [heq]; exact hlocalbound
    have hAcount : cN (fun x=>f x=true) n H=S := by
      have ha:=ones_seg_eq_count f n H
      change ones (seg f n (h+M+m+L+s+U))=_ at ha
      rw [hhead] at ha
      simp only [ones_append,ones_replicate_A,ones_replicate_S] at ha
      dsimp [S]
      omega
    have hFhead : 4≤cN P n H := by
      by_cases hf : cN P n H≤3
      · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
        have hb:=positive_r3_additions_free_bound f n 0 H hw hpre0
          (fun k hk hkH=>hpos k hk (by dsimp [H] at *; omega)) hf
        change cN (fun x=>f x=true) n H≤2*cN P n H+1 at hb
        rw [hAcount] at hb
        omega
      · omega
    have hSzero : cN P (n+H) v=0 := by
      apply cN_zero_of
      intro x hx hxv he
      have hf:=hS4 x (by dsimp [H] at *; omega) (by dsimp [H] at *; omega)
      change f x=true ∧ ¬EndN f 0 x at he
      rw [hf] at he
      simp at he
    have h1:=cN_add P n H v
    have h2:=cN_add P n (H+v) T
    have hpart:=addition_endable_partition f (n+H+v) T
    have hA4' : ∀ k, k<T → f (n+H+v+k)=true := by simpa only [H,Nat.add_assoc] using hA4
    rw [count_A_run f (n+H+v) T hA4'] at hpart
    change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hpart
    simp only [Nat.add_assoc] at h1 h2 hpart hlast hFfull
    omega

end Recaman.MomentFinalSGap
