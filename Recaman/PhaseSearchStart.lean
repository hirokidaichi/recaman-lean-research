import Recaman.InitialRegion
import Recaman.PhaseSearch

namespace Recaman

/-- The canonical normal-phase node attached to an actual orbit time.

The phase-search rank itself does not contain coordinates or first-occurrence
evidence.  Those facts belong in a certificate for the node, rather than in
the purely numeric `PhaseSearchNode`. -/
def targetStartNode (n : Nat) : PhaseSearchNode :=
  ⟨n, a n, .normal, a n⟩

/-- Semantic evidence supplied by `InitialRegion` for a canonical normal
search start.  The first-occurrence time is retained even though it is not a
component of the numeric node: later normal/debt transitions may need it when
constructing their own semantic invariant. -/
structure TargetStartCertificate (m n : Nat) : Prop where
  near_target : n = m - 1 ∨ n = m
  time_ready : m ≤ n + 1
  value_ready : m ≤ a n
  witnesses : ∃ q r f,
    CoordinatesAt n q r ∧ f ≤ n ∧ FirstAt a (a n) f

/-- Every positive target has a canonical, semantically certified normal
phase-search start. -/
theorem exists_targetStartCertificate {m : Nat} (hm : 0 < m) :
    ∃ n, TargetStartCertificate m n := by
  rcases exists_targetReady_state_of_pos hm with
    ⟨n, q, r, f, hnear, htime, hvalue, hcoord, hf, hfirst⟩
  exact ⟨n, {
    near_target := hnear
    time_ready := htime
    value_ready := hvalue
    witnesses := ⟨q, r, f, hcoord, hf, hfirst⟩
  }⟩

/-- A numeric node is a canonical target start precisely when it is the
normal node of some orbit time carrying the `InitialRegion` certificate. -/
def TargetStartInvariant (m : Nat) (node : PhaseSearchNode) : Prop :=
  ∃ n, node = targetStartNode n ∧ TargetStartCertificate m n

/-- Positive targets have an actual numeric phase-search node satisfying the
canonical start invariant. -/
theorem exists_targetStartNode {m : Nat} (hm : 0 < m) :
    ∃ node, TargetStartInvariant m node := by
  rcases exists_targetStartCertificate hm with ⟨n, hcert⟩
  exact ⟨targetStartNode n, n, rfl, hcert⟩

/-- An oracle restricted to a semantic domain of phase-search nodes.

Unlike `PhaseSearchOracle`, this obligation is not quantified over arbitrary
tuples of naturals.  It asks for a decreasing child only from a node known to
belong to `Valid`, and requires the child to preserve `Valid`.  The predicate
can therefore combine the normal invariant, `DebtInvariant`, and any crossing
data needed by the eventual complete search. -/
def RestrictedPhaseSearchOracle (m : Nat)
    (Valid : PhaseSearchNode → Prop) : Prop :=
  ∀ parent : PhaseSearchNode, Valid parent →
    (∃ t, a t = m) ∨
      ∃ child : PhaseSearchNode,
        Valid child ∧ PhaseSearchProgress m child parent

/-- Well-founded phase search needs the oracle only on a preserved semantic
domain containing the chosen start. -/
theorem restrictedPhaseSearchOracle_reaches_from
    {m : Nat} {Valid : PhaseSearchNode → Prop}
    (horacle : RestrictedPhaseSearchOracle m Valid)
    {start : PhaseSearchNode} (hstart : Valid start) :
    ∃ t, a t = m := by
  induction start using (phaseSearchProgress_wellFounded m).induction with
  | h parent ih =>
      rcases horacle parent hstart with hoccurs |
        ⟨child, hchildValid, hprogress⟩
      · exact hoccurs
      · exact ih child hprogress hchildValid

/-- Start-specific completion schema for a positive target.

It is enough to choose a semantic domain which contains every certified
canonical start and to construct a restricted oracle preserving that domain.
No behavior is required on malformed or unreachable `PhaseSearchNode`s. -/
theorem targetStart_reaches_of_restrictedOracle
    {m : Nat} (hm : 0 < m)
    (Valid : PhaseSearchNode → Prop)
    (hstartValid : ∀ node, TargetStartInvariant m node → Valid node)
    (horacle : RestrictedPhaseSearchOracle m Valid) :
    ∃ t, a t = m := by
  rcases exists_targetStartNode hm with ⟨start, hstart⟩
  exact restrictedPhaseSearchOracle_reaches_from horacle
    (hstartValid start hstart)

/-- A total phase-search oracle is a special case of the restricted schema,
with every numeric node admitted into the semantic domain. -/
theorem phaseSearchOracle_to_restricted {m : Nat}
    (horacle : PhaseSearchOracle m) :
    RestrictedPhaseSearchOracle m (fun _ => True) := by
  intro parent _
  rcases horacle parent with hoccurs | ⟨child, hprogress⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨child, trivial, hprogress⟩

end Recaman
