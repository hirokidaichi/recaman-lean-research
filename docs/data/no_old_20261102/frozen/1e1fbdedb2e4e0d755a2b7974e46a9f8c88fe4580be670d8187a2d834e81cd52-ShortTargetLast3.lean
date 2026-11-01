import Recaman.ShortTargetSourcePruning
import Recaman.MomentNoOld
import Recaman.AdjacentRunSupply

namespace Recaman.ShortTargetLast3

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Actual counter source pruning supplies the last-ray budget at the
original base; the auxiliary local boundary does not reset EndN. -/
theorem short_counter_last_3 (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v<C) (hvpos : 1≤v) (hC4 : 4≤C)
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
    (hdeep : v+2≤C) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤3 := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let N:=n+h+M+m
  let Htail:=L+s+U
  let z:=seg f N Htail
  have hno : ∀ k, k<T → ∀ r, r<N → ¬Win f r (N+Htail+v+k-r) := by
    intro k hk r hr hwin
    by_cases hrn : r<n
    · have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
      have ho:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t (h+M+m+L+s+U+v) k T j
        hw' hrn ht (by omega) (by have hR:=hb.2.1; omega)
        (by simpa only [Nat.add_assoc] using hA4)
        (by simpa only [Nat.add_assoc] using hgap)
        (by simpa only [N,Htail,Nat.add_assoc] using hwin)
        (by simpa only [Nat.add_assoc] using htarget)
      have hT:=hb.1
      omega
    have hc:=Recaman.ShortTargetSourcePruning.short_counter_source_pruning f n t h M m L s U v T j C k r w hw hpre ht
      hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
      (by omega) (by dsimp [N] at hr; omega) hk
      (by simpa only [N,Htail,Nat.add_assoc] using hwin)
    have ha:=hc.2.2.2.1
    have hm:=hc.2.2.2.2 (by dsimp [N] at hr; omega)
    omega
  have hz : seg f N Htail=List.replicate 0 false++List.replicate L true++List.replicate s false++List.replicate U true := by
    have he:=Recaman.SeparatorSupplyReset.three_run_word f N 0 L s U 0 0
      (by intros; omega)
      (by simpa only [N,Nat.add_assoc,Nat.add_zero] using hA2)
      (by simpa only [N,Nat.add_assoc,Nat.add_zero] using hS3)
      (by simpa only [N,Nat.add_assoc,Nat.add_zero] using hA3)
      (by intros; omega) (by intros; omega)
    simpa only [Htail,Nat.add_zero,List.replicate_zero,List.append_nil] using he
  have heq:=Recaman.MomentNoOld.last_count_eq_local f N Htail v T z rfl
    (by simpa only [N,Htail,Nat.add_assoc] using hS4)
    (by simpa only [N,Htail,Nat.add_assoc] using hA4) hno
  have hp:=Recaman.AdjacentRunSupply.run_prefix_ray_budget [(true,L),(false,s)]
    (List.replicate U true++List.replicate v false) T
  have hl:=Recaman.AdjacentRunSupply.rayCount_A_S_le_one U v T hvpos
  simp only [runWord,List.length_cons,List.length_nil,List.append_nil,List.append_assoc,List.replicate_zero,List.nil_append] at hp
  have hlast : cN (EndN f 0) (N+Htail+v) T≤3 := by
    rw [heq]
    simp only [z,hz,List.replicate_zero,List.nil_append,List.append_assoc]
    omega
  simpa only [N,Htail,Nat.add_assoc] using hlast

end Recaman.ShortTargetLast3
