import Recaman.SupplyAreaCrossings
import Recaman.FloorSupplyFreeBudget

namespace Recaman.SameSourceLowCrossings

open Recaman.SupplyAreaCrossings Recaman.FloorSupplyPotential
open Recaman.FloorSupplyFreeBudget Recaman.SingleWindowEquality
open Classical

private theorem source_potential_zero (f : Nat → Bool) (s t : Nat)
    (hw : Win f s (t-s)) : floorPotential f s (Fw f s-1) t=0 := by
  unfold floorPotential
  rw [hw.2.2,show Fw f s-(Fw f s-1+1)=0 by omega]
  simp

/-- Every earlier nonnegative source-area anchor is followed by an
original low visit before this common-source hit. -/
theorem low_visit_after_anchor (f : Nat → Bool) (s a t : Nat)
    (hsa : s≤a) (hat : a<t) (hw : Win f s (t-s))
    (ha : 0≤floorPotential f s (Fw f s-1) a) :
    ∃ q, a<q ∧ q<t ∧ Fw f q<Fw f s := by
  let p := floorPotential f s (Fw f s-1)
  have ht : s<t := by have := hw.1; omega
  have hF := hw.2.1
  rw [show s+(t-s)=t by omega] at hF
  have hz : p t=0 := source_potential_zero f s t hw
  have hstep := floor_potential_step f s (t-1) (Fw f s-1) (by omega)
  rw [show t-1+1=t by omega,hF] at hstep
  change p t=p (t-1)+(Fw f s+1)-(Fw f s-1+1) at hstep
  obtain ⟨q,haq,hqt,hq⟩ := downcross_from_end_values p a (t-1) 0
    (by omega) ha (by omega)
  have hs := floor_potential_step f s (q-1) (Fw f s-1) (by omega)
  rw [show q-1+1=q by omega] at hs
  change p q=p (q-1)+Fw f q-(Fw f s-1+1) at hs
  have h0 := hq.1
  have h1 := hq.2
  exact ⟨q,haq,by omega,by omega⟩

/-- The latest original A at either low level precedes its hit and is
strictly later than every preceding common-source hit. No free tag or
new source prefix is assumed. -/
theorem ordered_low_predecessor (f : Nat → Bool) (s t : Nat) (l : Int)
    (hst : s≤t) (hw : Win f s (t-s))
    (hl : Fw f s-1≤l) (hu : l≤Fw f s) :
    ∃ q, s≤q ∧ q<t ∧ Fw f q=l ∧ f q=true ∧
      ∀ u, s≤u → u<t → Win f s (u-s) → u<q := by
  have ht : s<t := by have := hw.1; omega
  have hFt := hw.2.1
  rw [show s+(t-s)=t by omega] at hFt
  let Q := fun q => Fw f q=l ∧ f q=true
  have exists_after (a : Nat) (hsa : s≤a) (hat : a<t)
      (ha : 0≤floorPotential f s (Fw f s-1) a) :
      ∃ v, a<v ∧ v<t ∧ Q v := by
    obtain ⟨b,hab,hbt,hLow⟩ := low_visit_after_anchor f s a t hsa hat hw ha
    obtain ⟨v,hbv,hvt,hv,hA⟩ := ivt f t (l+1) (by omega) (t-b) b (by omega) (by omega)
    exact ⟨v,by omega,hvt,by dsimp [Q]; exact ⟨by omega,hA⟩⟩
  have h0 : floorPotential f s (Fw f s-1) s=0 := by simp [floorPotential,Ar]
  obtain ⟨v,hsv,hvt,hv⟩ := exists_after s (by omega) ht (by omega)
  obtain ⟨d,hd,hdm,hafter⟩ := last_markN Q s (t-s)
  have hdp : d≠0 := by
    intro hz
    have hn := hafter (v-s) (by omega) (by omega)
    rw [show s+(v-s)=v by omega] at hn
    exact hn hv
  have hmark := hdm.resolve_left hdp
  let q := s+d-1
  refine ⟨q,by dsimp [q]; omega,by dsimp [q]; omega,hmark.1,hmark.2,?_⟩
  intro u hsu hut hwu
  have hpu := source_potential_zero f s u hwu
  obtain ⟨z,huz,hzt,hz⟩ := exists_after u hsu hut (by omega)
  by_cases h : u<q
  · exact h
  · have hn := hafter (z-s) (by dsimp [q] at h; omega) (by omega)
    rw [show s+(z-s)=z by omega] at hn
    exact (hn hz).elim

/-- All hits from one unchanged source inject into each of its two
lower A levels. Their status as actual supplied/free is not erased. -/
theorem same_source_level_count (f : Nat → Bool) (s K : Nat) (l : Int)
    (hl : Fw f s-1≤l) (hu : l≤Fw f s) :
    cN (fun t => f t=true ∧ s≤t ∧ Win f s (t-s)) s K≤
      cN (fun t => Fw f t=l ∧ f t=true) s K := by
  let P := fun t => f t=true ∧ s≤t ∧ Win f s (t-s)
  have hq (t : Nat) (ht : P t) := ordered_low_predecessor f s t l ht.2.1 ht.2.2 hl hu
  let q := fun t => if ht : P t then Classical.choose (hq t ht) else s
  have hspec (t : Nat) (ht : P t) :
      s≤q t ∧ q t<t ∧ Fw f (q t)=l ∧ f (q t)=true ∧
        ∀ u, s≤u → u<t → Win f s (u-s) → u<q t := by
    dsimp only [q]
    rw [dif_pos ht]
    exact Classical.choose_spec (hq t ht)
  apply count_le_of_interval_injection P _ s K q
  · intro t hst htK ht
    have hh := hspec t ht
    exact ⟨hh.1,by omega,hh.2.2.1,hh.2.2.2.1⟩
  · intro t u hst htu huK ht hu hEq
    have hT := hspec t ht
    have hU := hspec u hu
    have htuq := hU.2.2.2.2 t hst htu ht.2.2
    omega

end Recaman.SameSourceLowCrossings
