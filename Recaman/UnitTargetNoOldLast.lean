import Recaman.UnitTargetLateSources
import Recaman.RayCountFromBase
import Recaman.AdjacentRunSupply

namespace Recaman.UnitTargetNoOldLast

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem unit_target_no_old_last_budget (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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

    (hnoOld : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r)) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤v+4 := by
  have hb:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC1 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let N:=n+h+M+m
  let Htail:=L+s+U
  let b:=n+h+M+m+L+s+U+v
  let z:=seg f N Htail
  have hc:=Recaman.RayCountFromBase.count_with_initial_segment f N b T (v+1) (by
    intro i hi hipos he
    obtain ⟨ha,r,l,hr0,hre,hwin⟩:=he
    have hrl : l=b+i-r := by omega
    rw [hrl] at hwin
    have hNr : N≤r := by
      by_cases hNr : N≤r
      · exact hNr
      by_cases hrn : r<n
      · exact False.elim (hnoOld i hi r hrn (by simpa only [b,Nat.add_assoc] using hwin))
      have hp:=Recaman.UnitTargetLateSources.unit_target_late_sources f n t h M m L s U v T j C i r w hw hpre ht
        hh hM hm hL hs hU hv hC1 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
        (by omega) (by dsimp [N,b] at *; omega) hi (by simpa only [b,Nat.add_assoc] using hwin) (by omega)
      dsimp [N] at *
      omega
    exact ⟨ha,r,l,hNr,hre,by simpa only [hrl] using hwin⟩)
  have hz : z=List.replicate L true++List.replicate s false++List.replicate U true := by
    have he:=Recaman.SeparatorSupplyReset.three_run_word f N 0 L s U 0 0
      (by intros; omega)
      (by simpa only [N,Nat.add_assoc,Nat.add_zero] using hA2)
      (by simpa only [N,Nat.add_assoc,Nat.add_zero] using hS3)
      (by simpa only [N,Nat.add_assoc,Nat.add_zero] using hA3)
      (by intros; omega) (by intros; omega)
    simpa only [z,Htail,Nat.add_zero,Nat.zero_add,List.replicate_zero,List.append_nil,List.nil_append] using he
  have hbaseword : seg f N (b-N)=z++List.replicate v false := by
    rw [show b-N=Htail+v by dsimp [b,N,Htail]; omega,seg_add]
    rw [show N+Htail=n+h+M+m+L+s+U by dsimp [N,Htail]; omega,seg_false f (n+h+M+m+L+s+U) v hS4]
  have he:=Recaman.RayCountFromBase.count_from_base f N b T (z++List.replicate v false)
    (by dsimp [N,b]; omega) hbaseword (by simpa only [b,Nat.add_assoc] using hA4)
  have hp:=Recaman.AdjacentRunSupply.run_prefix_ray_budget [(true,L),(false,s)]
    (List.replicate U true++List.replicate v false) T
  have hl:=Recaman.AdjacentRunSupply.rayCount_A_S_le_one U v T (by omega)
  simp only [runWord,List.length_cons,List.length_nil,List.append_nil,List.append_assoc] at hp
  have hlocal : rayCount (z++List.replicate v false) T≤3 := by
    rw [hz]
    simp only [List.append_assoc] at *
    omega
  change cN (EndN f 0) b T≤v+4
  omega

end Recaman.UnitTargetNoOldLast
