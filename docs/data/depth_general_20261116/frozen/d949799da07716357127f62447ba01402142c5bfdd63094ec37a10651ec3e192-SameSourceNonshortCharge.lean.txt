import Recaman.SameSourceLowCrossings
import Recaman.ShortSourceTriples

namespace Recaman.SameSourceNonshortCharge

open Recaman.SameSourceLowCrossings Recaman.ShortSourceTriples
open Recaman.SingleWindowEquality Recaman.FloorSupplyFreeBudget
open Classical

private theorem latest_low (f : Nat → Bool) (s t : Nat) (l : Int)
    (hst : s≤t) (hw : Win f s (t-s))
    (hl : Fw f s-1≤l) (hu : l≤Fw f s) :
    ∃ q, s≤q ∧ q<t ∧ Fw f q=l ∧ f q=true ∧
      (∀ u, s≤u → u<t → Win f s (u-s) → u<q) ∧
      (∀ v, s≤v → v<t → Fw f v=l → f v=true → v≤q) := by
  obtain ⟨v,hsv,hvt,hvl,hvA,hvord⟩ := ordered_low_predecessor f s t l hst hw hl hu
  let Q := fun q => Fw f q=l ∧ f q=true
  obtain ⟨d,hd,hdm,hafter⟩ := last_markN Q s (t-s)
  have hd0 : d≠0 := by
    intro h0
    have hn := hafter (v-s) (by omega) (by omega)
    rw [show s+(v-s)=v by omega] at hn
    exact hn ⟨hvl,hvA⟩
  let q := s+d-1
  have hq := hdm.resolve_left hd0
  have hlatest (z : Nat) (hsz : s≤z) (hzt : z<t) (hz : Q z) : z≤q := by
    by_cases hh : z≤q
    · exact hh
    · have hn := hafter (z-s) (by dsimp [q] at hh; omega) (by omega)
      rw [show s+(z-s)=z by omega] at hn
      exact (hn hz).elim
  have hvq := hlatest v hsv hvt ⟨hvl,hvA⟩
  refine ⟨q,by dsimp [q]; omega,by dsimp [q]; omega,hq.1,hq.2,?_,?_⟩
  · intro u hsu hut hwu
    have hh := hvord u hsu hut hwu
    omega
  · intro z hsz hzt hz hzA
    exact hlatest z hsz hzt ⟨hz,hzA⟩

/-- One member of the ordered low pair cannot itself be an internal
SAA endpoint. No supplied A is relabelled as free. -/
theorem ordered_nonshort_predecessor (f : Nat → Bool) (s t : Nat)
    (hst : s≤t) (hw : Win f s (t-s)) :
    ∃ q, s≤q ∧ q<t ∧ (Fw f q=Fw f s-1 ∨ Fw f q=Fw f s) ∧
      f q=true ∧ ¬shortEndpoint f s q ∧
      ∀ u, s≤u → u<t → Win f s (u-s) → u<q := by
  obtain ⟨a,hsa,hat,ha,haA,haOrd,haLast⟩ := latest_low f s t (Fw f s-1) hst hw (by omega) (by omega)
  obtain ⟨b,hsb,hbt,hb,hbA,hbOrd,hbLast⟩ := latest_low f s t (Fw f s) hst hw (by omega) (by omega)
  have htF := hw.2.1
  rw [show s+(t-s)=t by omega] at htF
  have haStep := Fw_succ f a
  rw [haA] at haStep
  change Fw f (a+1)=Fw f a+1 at haStep
  obtain ⟨z,haz,hzt,hz,hzA⟩ := ivt f t (Fw f s+1) (by omega) (t-(a+1)) (a+1) (by omega) (by omega)
  have hzb := hbLast z (by omega) hzt (by omega) hzA
  have hab : a<b := by omega
  have hNotBoth : ¬(shortEndpoint f s a ∧ shortEndpoint f s b) := by
    rintro ⟨hAS,hBS⟩
    have hPrevA := hBS.2.2.2.1
    have hprev := Fw_succ f (b-1)
    rw [show b-1+1=b by omega,hPrevA] at hprev
    change Fw f b=Fw f (b-1)+1 at hprev
    have hprevLow : Fw f (b-1)=Fw f s-1 := by omega
    have hprevLast := haLast (b-1) (by have := hBS.1; omega) (by omega) hprevLow hPrevA
    have heq : b-1=a := by omega
    have hA2 := hAS.2.2.1
    have hS3 := hBS.2.1
    rw [show b-3=a-2 by have := hAS.1; omega,hA2] at hS3
    cases hS3
  by_cases has : shortEndpoint f s a
  · exact ⟨b,hsb,hbt,Or.inr hb,hbA,fun hbs => hNotBoth ⟨has,hbs⟩,hbOrd⟩
  · exact ⟨a,hsa,hat,Or.inl ha,haA,has,haOrd⟩

/-- The common-source family charges distinctly to original low A
remaining after all internal short endpoints are cancelled. -/
theorem same_source_nonshort_count (f : Nat → Bool) (s K : Nat) :
    cN (fun t => f t=true ∧ s≤t ∧ Win f s (t-s)) s K≤
      cN (fun q => (Fw f q=Fw f s-1 ∨ Fw f q=Fw f s) ∧ f q=true ∧ ¬shortEndpoint f s q) s K := by
  let P := fun t => f t=true ∧ s≤t ∧ Win f s (t-s)
  have hq (t : Nat) (ht : P t) := ordered_nonshort_predecessor f s t ht.2.1 ht.2.2
  let q := fun t => if ht : P t then Classical.choose (hq t ht) else s
  have spec (t : Nat) (ht : P t) :
      s≤q t ∧ q t<t ∧ (Fw f (q t)=Fw f s-1 ∨ Fw f (q t)=Fw f s) ∧
        f (q t)=true ∧ ¬shortEndpoint f s (q t) ∧
          ∀ u, s≤u → u<t → Win f s (u-s) → u<q t := by
    dsimp only [q]
    rw [dif_pos ht]
    exact Classical.choose_spec (hq t ht)
  apply count_le_of_interval_injection P _ s K q
  · intro t hst htK ht
    have hh := spec t ht
    exact ⟨hh.1,by omega,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩
  · intro t u hst htu huK ht hu heq
    have hT := spec t ht
    have hU := spec u hu
    have hh := hU.2.2.2.2.2 t hst htu ht.2.2
    omega

end Recaman.SameSourceNonshortCharge
