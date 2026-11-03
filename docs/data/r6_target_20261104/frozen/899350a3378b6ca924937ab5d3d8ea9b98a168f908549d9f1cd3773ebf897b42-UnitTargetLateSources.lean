import Recaman.MassOneTargetCounter
import Recaman.UnitTargetActualCut
import Recaman.SingleASPrefixWord
import Recaman.UnitTargetActualBoundary
import Recaman.UnitTargetDeepSecondS

namespace Recaman.UnitTargetLateSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem unit_target_late_sources (f : Nat → Bool) (n t h M m L s U v T j C i z : Nat)
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
    (hz : n≤z) (hzB : z≤n+h+M+m+L+s+U+v) (hi : i<T)
    (hlocal : Win f z (n+h+M+m+L+s+U+v+i-z))
    (hband : v+1≤i) : n+h+M+m≤z := by
  have hb:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC1 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  by_cases hafter : n+h+M+m≤z
  · exact hafter
  have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have hCseg : mass ((seg f 0 n).drop t)=1 := by rw [hpre]; omega
  let H:=h+M+m+L+s+U
  let b:=n+H+v
  have hsuf : 1≤cntF (seg f z (n+(H+v)-z)) := by
    have he : n+(H+v)-z=(n+H-z)+v := by dsimp [H]; omega
    rw [he,seg_add,show z+(n+H-z)=n+H by dsimp [H]; omega]
    rw [seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4),cntF_append,cntF_replicate_S]
    omega
  have hbnd (a q : Nat) (hpref : seg f n (z-n)=List.replicate a false++List.replicate q true)
      (hq : q≤j+2) : False := by
    have he:=Recaman.UnitTargetActualBoundary.actual_unit_zero_cross f n t z (H+v) i T j hw' hCseg a q hpref hq hsuf
      ht hz (by dsimp [H]; omega) hi (by have hx:=hb.2.1; omega) (by have hx:=hb.1; omega)
      (by simpa only [H,Nat.add_assoc] using hA4)
      (by simpa only [H,Nat.add_assoc] using hgap)
      (by simpa only [H,Nat.add_assoc] using hlocal)
      (by simpa only [H,Nat.add_assoc] using htarget)
    have hiT:=he.2.2
    have hbal:=hb.1
    omega
  by_cases hzS : z≤n+h
  · exact False.elim (hbnd (z-n) 0 (by
      rw [List.replicate_zero,List.append_nil]
      apply seg_false
      intro x hx hxz
      exact hS x hx (by omega)) (by omega))
  by_cases hzA : z≤n+h+M
  · have hpref:=Recaman.SingleASPrefixWord.first_prefix_word f n h M (z-n) (by omega) (by omega) hS hA
    exact False.elim (hbnd h (z-n-h) hpref (by have hx:=hb.2.2.1; omega))
  exact False.elim (Recaman.UnitTargetDeepSecondS.unit_target_deep_second_S_excluded f n t h M m L s U v T j C i z
    w hw hpre ht hh hM hm hL hs hU hv hC1 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
    (by omega) (by omega) hi hlocal (by omega))

end Recaman.UnitTargetLateSources
