import Recaman.OldFourThirteenActual
import Recaman.FourRunSourceBase

namespace Recaman.OldFourThirteenBase
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.EarlyOldFourResidual

open Classical in
theorem old_four_thirteen_int (e : Int → Bool) (p : Int) (n a h M m L s U v T sOld kOld : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false)
    (hA : ∀ k, k<M → e (p+((n+h+k : Nat) : Int))=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false)
    (hA2 : ∀ k, k<L → e (p+((n+h+M+m+k : Nat) : Int))=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false)
    (hA3 : ∀ k, k<U → e (p+((n+h+M+m+L+s+k : Nat) : Int))=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → e (p+(x : Int))=false)
    (hA4 : ∀ k, k<T → e (p+((n+h+M+m+L+s+U+v+k : Nat) : Int))=true)
    (hsOld : sOld<n) (hkOld : kOld<T)
    (hseed : P2 (past e (p+((n+h+M+m+L+s+U+v+kOld : Nat) : Int)) (n+h+M+m+L+s+U+v+kOld-sOld)))
    (hkTwo : kOld≤2) (hD : mass (segment e (p+(sOld : Int)) (n-sOld))=4) (hThirteen : h+m+s=13)
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ k, n<k → k≤n+h+M+m+L+s+U →
      endableCount e p k+1≤subtractionCount e p k)
     :
    23≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int) ∧
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤25 := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  have hO : Win (fun k=>e (p+(k : Int))) sOld (n+h+M+m+L+s+U+v+kOld-sOld) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p sOld (n+h+M+m+L+s+U+v+kOld-sOld) (by omega)
    simpa only [show sOld+(n+h+M+m+L+s+U+v+kOld-sOld)=n+h+M+m+L+s+U+v+kOld by omega] using hseed
  rw [segment_seg e p (p+(sOld : Int)) sOld rfl] at hD
  have hd:=seg_drop (fun k=>e (p+(k : Int))) 0 n sOld (by omega)
  simp only [Nat.zero_add,hpre] at hd
  rw [←hd] at hD
  exact Recaman.OldFourThirteenActual.actual_old_four_thirteen (fun k=>e (p+(k : Int))) n h M m L s U v T sOld kOld
    (w++List.replicate a true) (block_append hw (block_replicate_A a)) hpre
    hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4
    hsOld hkOld hO hkTwo hD hThirteen


end Recaman.OldFourThirteenBase
