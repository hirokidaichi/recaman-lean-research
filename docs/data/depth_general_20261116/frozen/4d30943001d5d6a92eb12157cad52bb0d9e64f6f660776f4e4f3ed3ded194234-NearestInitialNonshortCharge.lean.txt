import Recaman.SameSourceNonshortCharge
import Recaman.NearestInitialSourcePair
import Recaman.SFinalWindowLength

namespace Recaman.NearestInitialNonshortCharge

open Recaman.SameSourceNonshortCharge Recaman.NearestInitialSourcePair
open Recaman.ShortSourceTriples Recaman.InitialSLowTargetTransport
open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Classical

/-- Cancelling internal SAA images leaves an original nonshort low A
for every exclusive nearest-source target, with ordered distinct images. -/
theorem nearest_nonshort_count (f : Nat → Bool) (h K : Nat)
    (hS : ∀ i, i<h → f i=false) :
    cN (fun t => EndN f 0 t ∧ ¬EndN f h t ∧ Fw f t-Fw f h=2) h K≤
      cN (fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ f t=true ∧ ¬shortEndpoint f h t) h K := by
  by_cases hh : h=0
  · subst h
    have hz : cN (fun t => EndN f 0 t ∧ ¬EndN f 0 t ∧ Fw f t-Fw f 0=2) 0 K=0 :=
      cN_zero_of _ _ _ (fun i _ _ hi => hi.2.1 hi.1)
    omega
  let s := h-1
  have hs : s+1=h := by dsimp [s]; omega
  have hS0 := hS s (by dsimp [s]; omega)
  have hstep := fw_false_run f s 1 (fun i hi hi1 => by
    have hie : i=s := by omega
    simpa only [hie] using hS0)
  rw [hs] at hstep
  let P := fun t => f t=true ∧ s≤t ∧ Win f s (t-s)
  let Q := fun t => (Fw f t=Fw f s-1 ∨ Fw f t=Fw f s) ∧ f t=true ∧ ¬shortEndpoint f s t
  have hm : cN (fun t => EndN f 0 t ∧ ¬EndN f h t ∧ Fw f t-Fw f h=2) h K≤cN P h K := by
    apply cN_mono
    intro t hht _ ht
    have hw := nearest_source_window f h t hS hht ht.1 ht.2.1 ht.2.2
    exact ⟨ht.1.1,by dsimp [s]; omega,hw.2⟩
  have hp := cN_add P s 1 K
  have hq := cN_add Q s 1 K
  have hp0 : cN P s 1=0 := by simp [cN,P,hS0]
  have hq0 : cN Q s 1=0 := by simp [cN,Q,hS0]
  rw [hs,hp0] at hp
  rw [hs,hq0] at hq
  have hc := same_source_nonshort_count f s (1+K)
  change cN P s (1+K)≤cN Q s (1+K) at hc
  rw [hp,hq] at hc
  have hmono : cN Q h K≤
      cN (fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ f t=true ∧ ¬shortEndpoint f h t) h K := by
    apply cN_mono
    intro t _ _ ht
    rcases ht with ⟨ht,hA,hn⟩
    refine ⟨?_,hA,?_⟩
    · rcases ht with ht|ht
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · intro hc
      exact hn ⟨by have := hc.1; omega,hc.2⟩
  exact Nat.le_trans hm (Nat.le_trans (by simpa using hc) hmono)

/-- The unpaid image class consists only of original local supplies
without an internal SAA; no short supplier is charged as free. -/
theorem nearest_free_nonshort_budget (f : Nat → Bool) (h K : Nat)
    (hS : ∀ i, i<h → f i=false) :
    cN (fun t => EndN f 0 t ∧ ¬EndN f h t ∧ Fw f t-Fw f h=2) h K≤
      cN (fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ f t=true ∧ ¬EndN f 0 t) h K+
      cN (fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ EndN f h t ∧ ¬shortEndpoint f h t) h K := by
  let P := fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ f t=true ∧ ¬shortEndpoint f h t
  have hb := nearest_nonshort_count f h K hS
  have hsplit := cN_split P (EndN f 0) h K
  have hlocal : cN (fun t => P t ∧ EndN f 0 t) h K=
      cN (fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ EndN f h t ∧ ¬shortEndpoint f h t) h K := by
    apply cN_congr
    intro t _ _
    dsimp [P]
    constructor
    · rintro ⟨⟨hc,hA,hn⟩,he⟩
      exact ⟨hc,(initial_S_low_target_source_iff f h t hS (by rcases hc with hc|hc <;> omega)).mp he,hn⟩
    · rintro ⟨hc,he,hn⟩
      exact ⟨⟨hc,he.1,hn⟩,end_mono f 0 h t (Nat.zero_le _) he⟩
  have hf : cN (fun t => P t ∧ ¬EndN f 0 t) h K≤
      cN (fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ f t=true ∧ ¬EndN f 0 t) h K := by
    apply cN_mono
    intro t _ _ ht
    exact ⟨ht.1.1,ht.1.2.1,ht.2⟩
  rw [hlocal] at hsplit
  change cN (fun t => EndN f 0 t ∧ ¬EndN f h t ∧ Fw f t-Fw f h=2) h K≤cN P h K at hb
  omega

/-- A literal original free-budget counter must internally provide a
long local window at one of the two low image heights. -/
theorem nearest_counter_has_long_low_source (f : Nat → Bool) (h K : Nat)
    (hS : ∀ i, i<h → f i=false)
    (hcounter : cN (fun t => f t=true ∧ ¬EndN f 0 t ∧ Fw f t≤Fw f h+1) 0 (h+K)<
      cN (fun t => EndN f 0 t ∧ ¬EndN f h t ∧ Fw f t-Fw f h=2) h K) :
    ∃ q u, h≤u ∧ u<q ∧ q<h+K ∧ f q=true ∧
      (Fw f q=Fw f h ∨ Fw f q=Fw f h+1) ∧
      (Fw f u=Fw f h-1 ∨ Fw f u=Fw f h) ∧ 7≤q-u ∧ Win f u (q-u) := by
  let L := fun t => f t=true ∧ ¬EndN f 0 t ∧ Fw f t≤Fw f h+1
  let O := fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ EndN f h t ∧ ¬shortEndpoint f h t
  have hb := nearest_free_nonshort_budget f h K hS
  have hf : cN (fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ f t=true ∧ ¬EndN f 0 t) h K≤cN L 0 (h+K) := by
    have hm : cN (fun t => (Fw f t=Fw f h ∨ Fw f t=Fw f h+1) ∧ f t=true ∧ ¬EndN f 0 t) h K≤cN L h K := by
      apply cN_mono
      intro t _ _ ht
      exact ⟨ht.2.1,ht.2.2,by rcases ht.1 with hc|hc <;> omega⟩
    have hs := cN_add L 0 h K
    simp only [Nat.zero_add] at hs
    omega
  have hex : ∃ q, h≤q ∧ q<h+K ∧ O q := by
    by_cases he : ∃ q, h≤q ∧ q<h+K ∧ O q
    · exact he
    · have hz : cN O h K=0 := cN_zero_of O h K (fun q hq hqK ho => he ⟨q,hq,hqK,ho⟩)
      change cN (fun t => EndN f 0 t ∧ ¬EndN f h t ∧ Fw f t-Fw f h=2) h K≤_+cN O h K at hb
      change cN L 0 (h+K)<_ at hcounter
      omega
  obtain ⟨q,hhq,hqK,hLevel,he,hNot⟩ := hex
  obtain ⟨hA,u,k,hu,huk,hWin⟩ := he
  have hLen : q-u=k := by have := hWin.1; omega
  have hLong : 7≤k := by
    rcases Recaman.SFinalWindowLength.window_three_or_at_least_seven f u k hWin with hk|hk
    · have hw3 : Win f u 3 := by rwa [hk] at hWin
      obtain ⟨hSu,hA1,hA2⟩ := win3 f u hw3
      have hs : shortEndpoint f h q := by
        refine ⟨by omega,?_,?_,?_,hA⟩
        · simpa only [show q-3=u by omega] using hSu
        · simpa only [show q-2=u+1 by omega] using hA1
        · simpa only [show q-1=u+2 by omega] using hA2
      exact (hNot hs).elim
    · exact hk
  have hr := hWin.2.1
  rw [huk] at hr
  refine ⟨q,u,hu,by have := hWin.1; omega,hqK,hA,hLevel,?_,by omega,by rwa [hLen]⟩
  rcases hLevel with hc|hc
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end Recaman.NearestInitialNonshortCharge
