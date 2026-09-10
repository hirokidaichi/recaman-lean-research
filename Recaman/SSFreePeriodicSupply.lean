import Recaman.SSFreeSupply
import Recaman.ShortLocalParityCapacity

namespace Recaman.SSFreePeriodicSupply

open LeadingRunSupply SSFreeSupply LocalParityPeriodic ShortPeriodicSupply

/-- No global fixed parity is assumed. Each supplied window avoids SS and
SAAS, which is enough to use the all-lag clean injection. -/
theorem periodic_SSFree_capacity (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x)
    (U : List Nat) (hUnodup : U.Nodup) (hUrange : ∀ u, u ∈ U → u < p)
    (hSupply : ∀ u, u ∈ U → ∃ d : Nat, ShortPeriodicSupply.P2 e u d ∧
      NoSS (past e u d) ∧ NoSAAS (past e u d)) :
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  apply periodic_clean_capacity e p hp hper U hUnodup hUrange
  intro u hu
  obtain ⟨d,hP,hss,hsaas⟩ := hSupply u hu
  exact ⟨d,hP,stream_noSS_clean e u d hss hsaas hP⟩

theorem short_plus_SSFree_capacity (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x)
    (Q : List Nat) (hQnodup : Q.Nodup) (hQrange : ∀ t, t ∈ Q → t < p)
    (hQ : ∀ t, t ∈ Q → e t = true ∧ ∃ d : Nat,
      19 ≤ d ∧ ShortPeriodicSupply.P2 e t d ∧
        NoSS (past e t d) ∧ NoSAAS (past e t d)) :
    suppliedCount e 0 p + LagElevenPeriodic.u11Count e 0 p + Q.length ≤ subtractionCount e 0 p := by
  apply ShortLocalParityCapacity.short_plus_clean_capacity e p hp hper Q hQnodup hQrange
  intro t ht
  obtain ⟨hA,d,hd,hP,hss,hsaas⟩ := hQ t ht
  exact ⟨hA,d,hd,hP,stream_noSS_clean e t d hss hsaas hP⟩

end Recaman.SSFreePeriodicSupply
