import Recaman.SS2LowSSTight
import Recaman.OnePerRun

/-!
# An internal SSS cannot be a low-SS P2 endpoint

This is the first, narrower Lean obligation in the E-370 paper proof. The
stream and all windows are actual integer-clock data. Neither NoSAAS,
positive period mass, nor a lag cutoff is assumed. No claim about the
q = oldest-S case or the full collision-pair inequality is made here.
-/

namespace Recaman.SS2InternalSSS

open LeadingRunSupply
open OneSSMultiplicity (ssCount)
open SharpPeriodicSupply (phase)
open LowSSPeriodicSupply (endpointPhase)

/-- Two overlapping SS edges are present in any word ending in SSS. -/
theorem ssCount_append_SSS (w : List Bool) :
    2 ≤ ssCount (w ++ [false, false, false]) := by
  have htwo : ssCount [false, false, false] = 2 := by decide
  rw [OnePerRun.ssCount_append, htwo]
  split_ifs <;> omega

/-- A current-A P2 window with at most one SS edge cannot have its oldest
endpoint at the first clock of an SSS run. The P2 hypothesis supplies the
minimum lag three; the two SS edges then occur inside the actual window. -/
theorem internal_sss_ne_lowSS_endpoint
    (e : Int → Bool) (q t : Int) (l : Nat)
    (hq0 : e q = false) (hq1 : e (q + 1) = false)
    (hq2 : e (q + 2) = false)
    (htP : P2 (past e t l))
    (htss : ssCount (past e t l) ≤ 1)
    (hend : t - (l : Int) = q) : False := by
  have hlag : 3 ≤ l := by
    have h := p2_length_ge_three (past e t l) htP
    simpa [past] using h
  have hthree : past e (q + 3) 3 = [false, false, false] := by
    rw [TwoSSLeadingSibling.past_three_eq]
    rw [show q + 3 - 1 = q + 2 by omega,
      show q + 3 - 2 = q + 1 by omega,
      show q + 3 - 3 = q by omega,
      hq2, hq1, hq0]
  have hsplit : past e t l =
      past e t (l - 3) ++ [false, false, false] := by
    have heq : l = (l - 3) + 3 := by omega
    conv_lhs => rw [heq]
    rw [past_append, show t - ((l - 3 : Nat) : Int) = q + 3 by omega, hthree]
  rw [hsplit] at htss
  have htwo := ssCount_append_SSS (past e t (l - 3))
  omega

/-- Periodicity transports every candidate endpoint phase to the first
integer clock of an actual SSS run. This is an all-period, all-lag exclusion;
it does not assert that the SSS lies in a particular donor window. -/
theorem internal_sss_phase_ne_lowSS_endpoint
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (q : Int)
    (hq0 : e q = false) (hq1 : e (q + 1) = false)
    (hq2 : e (q + 2) = false)
    (t : Int) (l : Nat)
    (htP : P2 (past e t l))
    (htss : ssCount (past e t l) ≤ 1) :
    endpointPhase p t l ≠ phase p q := by
  intro heq
  have hmod : (t - (l : Int)) % p = q % p :=
    SharpPeriodicSupply.phase_eq_mod p hp (t - l) q
      (by simpa [endpointPhase] using heq)
  obtain ⟨k, hk⟩ :=
    SharpPeriodicSupply.lift_equal_mod p q (t - l) hmod.symm
  have hP' : P2 (past e (t + k * p) l) := by
    rw [SharpPeriodicSupply.past_shift e p hper]
    exact htP
  have hss' : ssCount (past e (t + k * p) l) ≤ 1 := by
    rw [SharpPeriodicSupply.past_shift e p hper]
    exact htss
  exact internal_sss_ne_lowSS_endpoint e q (t + k * p) l
    hq0 hq1 hq2 hP' hss' (by omega)

end Recaman.SS2InternalSSS
