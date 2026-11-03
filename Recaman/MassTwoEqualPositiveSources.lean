import Recaman.MassTwoMiddleDelay
import Recaman.MassTwoEqualCounter

namespace Recaman.MassTwoEqualPositiveSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_two_equal_positive_sources (f : Nat → Bool) (n t h M m L s U v T j C i z : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=2) (hC2 : C=2)
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
    (hz : n≤z) (hzB : z≤n+h+M+m+L+s+U+v) (hi : i<T)
    (hlocal : Win f z (n+h+M+m+L+s+U+v+i-z))
    (hipos : 1≤i) : n+h+M+m≤z := by
  have hb:=Recaman.MassTwoEqualCounter.mass_two_equal_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC2 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hTj : T=j+1 := by have hx:=hb.1; omega
  have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have hd:=seg_drop f 0 n t (by omega)
  simp only [Nat.zero_add,hpre] at hd
  have hCseg : 2≤mass (seg f t (n-t)) := by rw [←hd]; omega
  have hcut:=Recaman.SourceMassStrictActual.actual_mass_two_strict_A f n t z (h+M+m+L+s+U+v) i T j
    hw' ht hCseg hz (by omega) hi (by have hx:=hb.2.1; omega) (by omega)
    (by simpa only [Nat.add_assoc] using hA4)
    (by simpa only [Nat.add_assoc] using hgap)
    (by simpa only [Nat.add_assoc] using hlocal)
    (by simpa only [Nat.add_assoc] using htarget)
  have hafter : n+h+M≤z := by
    by_cases ha : n+h+M≤z
    · exact ha
    · have hc:=Recaman.FirstRunPrefixCounts.first_run_prefix_count f n h M (z-n) (by omega) hS hA
      have hMb:=hb.2.2.1
      omega
  by_cases hafter2 : n+h+M+m≤z
  · exact hafter2
  have hcount:=Recaman.FirstRunPrefixCounts.middle_S_prefix_count f n h M m (z-n)
    (by omega) (by omega) hS hA hS2
  have hi1 : i=1 := by have hMb:=hb.2.2.1; omega
  have hMcrit : M=j+2 := by have hMb:=hb.2.2.1; omega
  exact False.elim (Recaman.MassTwoMiddleDelay.middle_delay_excluded f n t h M m z
    (n+h+M+m+L+s+U+v) i j w hw hpre ht (by omega)
    (by have hx:=hb.2.1; omega) hMcrit hafter (by omega) hzB hS hA hS2
    (fun k hk=>hA4 k (by omega))
    (fun x hx hxB=>hgap x (by omega) (by omega))
    (by simpa only [show i+j=T by omega,Nat.add_assoc] using htarget)
    (by simpa only [Nat.add_assoc] using hlocal))

end Recaman.MassTwoEqualPositiveSources
