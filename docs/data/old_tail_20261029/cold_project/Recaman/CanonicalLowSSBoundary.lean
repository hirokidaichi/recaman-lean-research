import Recaman.LowSSEndpoint
import Recaman.FiniteP2Semantics

namespace Recaman.CanonicalLowSSBoundary

open LeadingRunSupply OneSSMultiplicity CanonicalSSFreeSupply LowSSEndpoint

/-! The low-SS endpoint method stops at a real canonical two-SS window.
This refutes only extending the prefix-normalization statement to two SS,
not the full periodic capacity conjecture. Sign time 114 is step 115. -/

def boundaryWord : List Bool :=
  [true,true,true,false,false,false,true,false,true,false,true]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canonical_window : past canonicalSign 114 11=boundaryWord := by decide

theorem word_minimum : P2 boundaryWord ∧ ∀ d : Fin 11, ¬ P2 (boundaryWord.take d.val) := by
  unfold P2 boundaryWord
  decide

theorem canonical_minimum : ShortPeriodicSupply.P2 canonicalSign 114 11 ∧
    ∀ f : Nat, f<11 → ¬ ShortPeriodicSupply.P2 canonicalSign 114 f := by
  constructor
  · apply (past_p2_iff canonicalSign 114 11).mp
    rw [canonical_window]
    exact word_minimum.1
  · intro f hf hP
    apply word_minimum.2 ⟨f,hf⟩
    have h := (past_p2_iff canonicalSign 114 f).mpr hP
    rwa [← take_past canonicalSign 114 11 f (by omega),canonical_window] at h

theorem two_SS_and_NoSAAS : ssCount (past canonicalSign 114 11)=2 ∧
    SSFreeSupply.NoSAAS (past canonicalSign 114 11) := by
  rw [canonical_window]
  refine ⟨by decide,?_⟩
  intro u v heq
  have hc := saas_occurrence_positive u v
  have hz : saasCount boundaryWord=0 := by decide
  rw [← heq,hz] at hc
  omega

theorem current_and_endpoint_A : canonicalSign 114=true ∧ canonicalSign 103=true := by
  refine ⟨FiniteP2Semantics.finite_P2_forces_A 103 11 canonical_minimum.1,?_⟩
  have h := congrArg (fun w : List Bool => w[10]?) canonical_window
  simpa [past,boundaryWord] using h

/-- There is no shorter S-ended P2 witness to choose, despite the actual
greedy recurrence, current A, and absence of SAAS. -/
theorem no_S_ended_prefix : ¬ ∃ f : Nat, f≤11 ∧
    ShortPeriodicSupply.P2 canonicalSign 114 f ∧ canonicalSign (114-f)=false := by
  rintro ⟨f,hf,hP,hS⟩
  have heq : f=11 := by
    by_cases heq : f=11
    · exact heq
    · exact False.elim (canonical_minimum.2 f (by omega) hP)
  rw [heq] at hS
  change canonicalSign 103=false at hS
  have hA := current_and_endpoint_A.2
  rw [hA] at hS
  cases hS

end Recaman.CanonicalLowSSBoundary
