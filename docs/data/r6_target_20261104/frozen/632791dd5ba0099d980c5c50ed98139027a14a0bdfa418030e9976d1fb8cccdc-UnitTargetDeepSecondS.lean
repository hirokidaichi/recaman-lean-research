import Recaman.MassOneTargetCounter
import Recaman.UnitTargetActualCut
import Recaman.SingleASPrefixWord

namespace Recaman.UnitTargetDeepSecondS

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem unit_target_deep_second_S_excluded (f : Nat → Bool) (n t h M m L s U v T j C i z : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : 1≤v) (hC1 : C=1)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1)
    (hz : n+h+M<z) (hzB : z<n+h+M+m) (hi : i<T)
    (hlocal : Win f z (n+h+M+m+L+s+U+v+i-z))
    (hband : v≤i) : False := by
  have hb:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC1 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have hCseg : mass ((seg f 0 n).drop t)=1 := by rw [hpre]; omega
  have hword:=Recaman.SingleASPrefixWord.middle_prefix_word f n h M m (z-n) (by omega) (by omega) hS hA hS2
  have hAS:=Recaman.SingleASPrefixWord.S_A_S_has_pair h M (z-n-(h+M)) hM (by omega)
  have hcut:=Recaman.UnitTargetActualCut.actual_unit_source_prefix_two f n t z (h+M+m+L+s+U+v) i T j
    hw' hCseg (List.replicate h false++List.replicate (M-1) true) (List.replicate (z-n-(h+M)-1) false)
    (by rw [hword,hAS]) ht (by omega) (by omega) hi (by have hx:=hb.2.1; omega)
    (by have hx:=hb.1; omega)
    (by simpa only [Nat.add_assoc] using hA4)
    (by simpa only [Nat.add_assoc] using hgap)
    (by simpa only [Nat.add_assoc] using hlocal)
    (by simpa only [Nat.add_assoc] using htarget)
  have hcount:=Recaman.FirstRunPrefixCounts.middle_S_prefix_count f n h M m (z-n)
    (by omega) (by omega) hS hA hS2
  have hMb:=hb.2.2.1
  omega

end Recaman.UnitTargetDeepSecondS
