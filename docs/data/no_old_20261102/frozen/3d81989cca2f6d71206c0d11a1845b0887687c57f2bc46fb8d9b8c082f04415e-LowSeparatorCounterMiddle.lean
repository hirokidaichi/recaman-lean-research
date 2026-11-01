import Recaman.MiddleSSourceCharge

namespace Recaman.LowSeparatorCounterMiddle

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- Saturation forces a middle-S source. The old target's actual A cut
then yields R<=M<=6. This is a necessary-condition reduction, not absence. -/
theorem low_separator_counter_middle (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=1 ∨ v=2)
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
    (hC : mass (w.drop t)=3)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    j+1≤M ∧ M≤6 ∧ j+1≤6 ∧
    ∃ i, i<T ∧ sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) i := by
  classical
  have hb:=Recaman.LowSeparatorTargetCounter.low_separator_counter_parameters f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hc:=Recaman.LowSeparatorCounterCritical.low_separator_counter_critical f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  let B : Int:= -areaW z
  have hB : runKey z= -2*B := by
    unfold runKey
    rw [hmz]
    dsimp [B]
    grind only
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hkey : runKey (w.drop t)= -runKey z-12*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := hb.2.2.2
  have hkeyB : runKey (w.drop t)=2*B-12*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by
    rw [hB] at hkey
    omega
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  have hraw:=Recaman.LowSeparatorLocalBudget.low_separator_middle_source_bound (w.drop t) hu hC h M m L s U v (j+1) T
    hv (by have hR:=hb.2.1; omega) hzeroMass hs (by have hm:=hb.2.2.1; omega) B
    (by rw [←hhead]; exact hB)
    (by simpa only [Int.natCast_add,Int.natCast_one] using hkeyB)
  have heq:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hc.1)
  have hlast : rayCount (z++List.replicate v false) T=v+2 := by
    rw [←heq]
    simpa only [H,Nat.add_assoc] using hc.2.2.2.1
  have hbnd : rayCount (z++List.replicate v false) T≤v+1+cN Q 0 T := by
    simpa only [z,H,hhead,List.append_assoc,Q] using hraw
  have hex : ∃ i, i<T ∧ Q i := by
    by_cases he : ∃ i, i<T ∧ Q i
    · exact he
    · have hz : cN Q 0 T=0 := by
        apply cN_zero_of
        intro i _ hi hqi
        exact he ⟨i,by omega,hqi⟩
      omega
  obtain ⟨i,hi,hsupply⟩:=hex
  have hsupply0:=hsupply
  obtain ⟨q,hq,hqm,hbal,hks⟩:=hsupply
  have hprof:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hcut:=Recaman.MiddleSSourceCharge.middle_S_source_A_cut (w.drop t) hu h M m L s U v T j i q hq hqm
    (by have hR:=hb.2.1; omega) (by have hT:=hb.1; have hv2 : v≤2 := by omega; omega)
    (by simpa only [List.append_assoc] using hbal)
    (by simpa only [List.append_assoc] using hks)
    (by simpa only [z,H,hhead,List.append_assoc] using hprof.1)
    (by simpa only [z,H,hhead,List.append_assoc] using hprof.2)
  have hM6 : M≤6 := by
    have hpreA : seg f 0 (n+h)=w++List.replicate h false := by
      rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
    have hE:=endable_A_run_count f (n+h) M (w++List.replicate h false) hpreA hA
    have hE2:=block_rayCount_after_S hw h M
    have hpartA:=addition_endable_partition f (n+h) M
    rw [count_A_run f (n+h) M hA] at hpartA
    have h1:=cN_add P n h M
    have h2:=cN_add P n (h+M) (m+L+s+U)
    have hfh : cN P n (h+M+m+L+s+U)=4 := hc.2.1
    change M=cN (EndN f 0) (n+h) M+cN P (n+h) M at hpartA
    simp only [Nat.add_assoc] at h1 h2 hpartA hE hfh
    omega
  exact ⟨hcut,hM6,by omega,i,hi,hsupply0⟩

end Recaman.LowSeparatorCounterMiddle
