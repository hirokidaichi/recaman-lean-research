import Recaman.FourRunSupplySeventeen
import Recaman.LocalSourcePrefixBudget

namespace Recaman.FinalBandSupplyClock

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.AdjacentRunSupply Recaman.OldSourceKeyOrder Recaman.LocalSourcePrefixBudget
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- If the actual A count before a chosen AU Sv suffix is too small to
support any final-band local source, all such actual supplied clocks
must come from the last S itself, hence are clock2. Old source mass is
unbounded and old sources are excluded by the same old target. -/
theorem final_band_clock_two (f : Nat → Bool) (n t B0 U v i T j : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hv : 1≤v) (hi : i<T) (hj : 2≤j)
    (hband : T≤i+j)
    (hsmall : cN (fun x=>f x=true) n B0<j+1)
    (hshape : seg f (n+B0) (U+v)=List.replicate U true++List.replicate v false)
    (hA : ∀ k, k<T → f (n+B0+U+v+k)=true)
    (hS : ∀ x, n+B0+U+v+T≤x → x<n+B0+U+v+T+j → f x=false)
    (htarget : Win f t (n+B0+U+v+T+j-t))
    (he : EndN f 0 (n+B0+U+v+i)) : i=2 := by
  let B:=B0+U+v
  have hA' : ∀ k, k<T → f (n+B+k)=true := by simpa only [B,Nat.add_assoc] using hA
  have hS' : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false := by simpa only [B,Nat.add_assoc] using hS
  have hW : Win f t (n+B+T+j-t) := by simpa only [B,Nat.add_assoc] using htarget
  obtain ⟨hAi,z,k,hz0,hzk,hwin⟩:=he
  have hwin' : Win f z (n+B+i-z) := by
    have hk : k=n+B+i-z := by dsimp [B] at *; omega
    simpa only [hk] using hwin
  have hzn : n≤z := by
    by_cases hh : n≤z
    · exact hh
    · have hb:=actual_old_target_prior_clock f n z t B i T j hw (by omega) ht
        (by omega) hj hA' hS' hwin' hW
      omega
  have hzB0 : n+B0≤z := by
    by_cases hh : n+B0≤z
    · exact hh
    · have hzB : z≤n+B := by dsimp [B]; omega
      have hc:=actual_local_source_prefix_A f n t z B i T j hw ht hzn hzB hi hj hband
        hA' hS' hwin' hW
      have hcnt:=cN_add (fun x=>f x=true) n (z-n) (n+B0-z)
      have hlen : z-n+(n+B0-z)=B0 := by omega
      rw [hlen] at hcnt
      omega
  have hloc : EndN f (n+B0) (n+B0+U+v+i) :=
    ⟨hAi,z,k,hzB0,hzk,hwin⟩
  have hb := (localSupply_seg_iff f (n+B0) (n+B0+U+v+i) (by omega) hAi).mpr hloc
  have hword : seg f (n+B0) (n+B0+U+v+i-(n+B0))=
      List.replicate U true++List.replicate v false++List.replicate i true := by
    rw [show n+B0+U+v+i-(n+B0)=(U+v)+i by omega,seg_add,hshape]
    have hAword : seg f (n+B0+(U+v)) i=List.replicate i true := by
      apply seg_A
      intro x hx hxi
      have hh:=hA (x-(n+B0+U+v)) (by omega)
      rw [show n+B0+U+v+(x-(n+B0+U+v))=x by omega] at hh
      exact hh
    rw [hAword]
  rw [hword] at hb
  exact (local_A_S_clock_iff U v i hv).mp hb

/-- The selected final band has at most one real supplied A clock. -/
theorem final_band_count_le_one (f : Nat → Bool) (n t B0 U v T j : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hv : 1≤v) (hj : 2≤j)
    (hsmall : cN (fun x=>f x=true) n B0<j+1)
    (hshape : seg f (n+B0) (U+v)=List.replicate U true++List.replicate v false)
    (hA : ∀ k, k<T → f (n+B0+U+v+k)=true)
    (hS : ∀ x, n+B0+U+v+T≤x → x<n+B0+U+v+T+j → f x=false)
    (htarget : Win f t (n+B0+U+v+T+j-t)) :
    cN (fun i=>EndN f 0 (n+B0+U+v+i) ∧ T≤i+j) 0 T≤1 := by
  apply cN_le_one_of_unique
  intro i hi k hk hei hek
  have hi2:=final_band_clock_two f n t B0 U v i T j hw ht hv hi hj hei.2
    hsmall hshape hA hS htarget hei.1
  have hk2:=final_band_clock_two f n t B0 U v k T j hw ht hv hk hj hek.2
    hsmall hshape hA hS htarget hek.1
  omega

private theorem cN_length_bound (P : Nat → Prop) (n : Nat) : ∀ K, cN P n K≤K
  | 0 => by simp [cN]
  | K+1 => by have ih:=cN_length_bound P n K; have hh:=cN_succ_le P n K; omega

/-- Whole last-ray count, with the early clocks charged by their literal
length and the final band by its unique clock2. -/
theorem last_ray_count_le_three (f : Nat → Bool) (n t B0 U v T j : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hv : 1≤v) (hj : 2≤j)
    (hshort : T≤j+2) (hsmall : cN (fun x=>f x=true) n B0<j+1)
    (hshape : seg f (n+B0) (U+v)=List.replicate U true++List.replicate v false)
    (hA : ∀ k, k<T → f (n+B0+U+v+k)=true)
    (hS : ∀ x, n+B0+U+v+T≤x → x<n+B0+U+v+T+j → f x=false)
    (htarget : Win f t (n+B0+U+v+T+j-t)) :
    cN (EndN f 0) (n+B0+U+v) T≤3 := by
  let D:=n+B0+U+v
  let a:=T-j
  have ha : a≤2 := by dsimp [a]; omega
  have hsplit:=cN_add (EndN f 0) D a (T-a)
  have hea:=cN_length_bound (EndN f 0) D a
  have hlate : cN (EndN f 0) (D+a) (T-a)≤1 := by
    have heq : cN (EndN f 0) (D+a) (T-a)=
        cN (fun k=>EndN f 0 (D+a+k)) 0 (T-a) := by
      induction T-a with
      | zero => rfl
      | succ K ih =>
        by_cases he : EndN f 0 (D+a+K) <;> simp [cN,he,ih]
    rw [heq]
    apply cN_le_one_of_unique
    intro k hk l hl hek hel
    have hk2:=final_band_clock_two f n t B0 U v (a+k) T j hw ht hv (by dsimp [a] at *; omega)
      hj (by dsimp [a]; omega) hsmall hshape hA hS htarget (by simpa only [D,Nat.add_assoc] using hek)
    have hl2:=final_band_clock_two f n t B0 U v (a+l) T j hw ht hv (by dsimp [a] at *; omega)
      hj (by dsimp [a]; omega) hsmall hshape hA hS htarget (by simpa only [D,Nat.add_assoc] using hel)
    omega
  have haT : a≤T := by dsimp [a]; omega
  rw [Nat.add_sub_of_le haT] at hsplit
  dsimp [D] at *
  omega

end Recaman.FinalBandSupplyClock
