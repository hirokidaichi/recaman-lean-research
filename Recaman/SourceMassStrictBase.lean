import Recaman.SourceMassStrictActual
import Recaman.FourRunSourceBase
import Recaman.CleanWindowCapacity

namespace Recaman.SourceMassStrictBase

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_two_strict_A_int (e : Int → Bool) (p : Int) (n a s z B i T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true)
    (hs : s<n) (hC2 : 2≤mass (segment e (p+(s : Int)) (n-s)))
    (hz : n≤z) (hzB : z≤n+B) (hi : i<T) (hj : 2≤j) (hband : T≤i+j)
    (hA : ∀ k, k<T → e (p+((n+B+k : Nat) : Int))=true)
    (hS : ∀ x, n+B+T≤x → x<n+B+T+j → e (p+(x : Int))=false)
    (hlocal : P2 (past e (p+((n+B+i : Nat) : Int)) (n+B+i-z)))
    (htarget : P2 (past e (p+((n+B+T+j : Nat) : Int)) (n+B+T+j-s))) :
    j+1+(i+j-T)+1≤countP (fun x=>e x=true) (p+(n : Int)) (z-n) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  rw [segment_seg e p (p+(s : Int)) s rfl] at hC2
  rw [countP_cN (fun x=>e x=true) p (p+(n : Int)) n rfl]
  have hlocalPos:=Recaman.CleanWindowCapacity.p2_pos _ hlocal
  simp only [past,List.length_map,List.length_range] at hlocalPos
  have hlocalW : Win (fun k=>e (p+(k : Int))) z (n+B+i-z) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p z (n+B+i-z) hlocalPos
    simpa only [show z+(n+B+i-z)=n+B+i by omega] using hlocal
  have htargetW : Win (fun k=>e (p+(k : Int))) s (n+B+T+j-s) := by
    apply Recaman.FourRunSourceBase.P2_shifted_window e p s (n+B+T+j-s) (by omega)
    simpa only [show s+(n+B+T+j-s)=n+B+T+j by omega] using htarget
  exact Recaman.SourceMassStrictActual.actual_mass_two_strict_A (fun k=>e (p+(k : Int))) n s z B i T j
    (by rw [hpre]; exact block_append hw (block_replicate_A a)) hs hC2 hz hzB hi hj hband hA hS hlocalW htargetW

end Recaman.SourceMassStrictBase
