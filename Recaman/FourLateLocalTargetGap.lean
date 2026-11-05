import Recaman.FourLongFinalRayGap
import Recaman.AlternatingTargetLengths

namespace Recaman.FourLateLocalTargetGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Every target beginning at or after the start of the third A run
has the full actual free gap. Starts in the final A or the gap are impossible. -/
theorem four_late_local_target_free_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U) (hT : 1≤T) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (hta : n+h+M+m+L+s≤t)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t)) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  let a:=n+h+M+m+L+s
  let b:=a+U
  let c:=b+v
  let d:=c+T
  have hta' : a≤t := hta
  have hW : Win f t (d+j-t) := htarget
  have hS' : ∀ x, b≤x → x<c → f x=false := hS4
  have hA' : ∀ i, i<T → f (c+i)=true := hA4
  have hgap' : ∀ x, d≤x → x<d+j → f x=false := hgap
  have hlength : j+1≤v ∧ 2*(j+1)≤T := by
    by_cases htA : t<b
    · have h:=Recaman.AlternatingTargetLengths.actual_A_S_A_S_target_lengths f a U v T j t
        hta' htA hA3 hS' hA' hgap' hW
      exact ⟨by have hh:=h.1; omega,by have hh:=h.2; omega⟩
    · by_cases htS : t<c
      · have h:=Recaman.FinalSTargetLengths.final_S_target_lengths f b v T j t (by omega) htS
          hS' hA' hgap' hW
        exact ⟨h.2.2,by have hh:=h.2.1; omega⟩
      · exfalso
        by_cases htA4 : t<d
        · have hh:=Recaman.AlternatingTargetLengths.actual_A_S_A_S_target_lengths f c T 0 0 j t
            (by omega) htA4 hA'
            (by intro x hx hxx; omega)
            (by intro i hi; omega)
            (by simpa only [Nat.add_zero] using hgap')
            (by simpa only [Nat.add_zero] using hW)
          have h:=hh.1
          omega
        · have hSword : seg f t (d+j-t)=List.replicate (d+j-t) false := by
            apply seg_false
            intro x hx hxt
            exact hgap' x (by omega) (by omega)
          have hm : mass (seg f t (d+j-t))=1 := by
            rw [seg_mass]
            have hp:=hW.2.1
            omega
          rw [hSword,mass_rep_false] at hm
          omega
  exact Recaman.FourLongFinalRayGap.four_long_final_ray_gap f n h M m L s U v T j w hw hpre
    hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hlength.1 hlength.2

end Recaman.FourLateLocalTargetGap
