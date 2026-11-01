import Recaman.OldSourceKeyOrder

namespace Recaman.OldSeedInversionKey

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The old source clock is retained as a quadratic cost; no early-clock
cutoff or independent old mass/area signature is used. -/
theorem old_seed_clock_inversion (u z : List Bool) (hu : BlockWord u)
    (hmz : mass z=0) (v i : Nat) (I : Int)
    (hmeasure : runKey z=4*I-2*(cntF z : Int)^2)
    (hmass : mass u-(v : Int)+(i : Int)=1)
    (hkey : runKey (u++z++List.replicate v false)= -2) :
    2*I+2*mass u*(cntF z : Int)+(mass u)^2-((i : Int)-1)^2≤(cntF z : Int)^2 := by
  have hl : -2≤runKey u := by
    have h:=block_area_quadratic_lower hu
    unfold runKey
    omega
  rw [runKey_append_S,runKey_append,mass_append,hmz,hmeasure] at hkey
  grind only

/-- The same old window charges a measured head inversion. Neither its
area nor its mass is chosen independently of the source word. -/
theorem old_seed_inversion_inequality (u z : List Bool) (hu : BlockWord u)
    (hmz : mass z=0) (v i : Nat) (hi : i≤1) (I : Int)
    (hmeasure : runKey z=4*I-2*(cntF z : Int)^2)
    (hmass : mass u-(v : Int)+(i : Int)=1)
    (hkey : runKey (u++z++List.replicate v false)= -2) :
    2*I+2*mass u*(cntF z : Int)+(mass u)^2-1≤(cntF z : Int)^2 := by
  have hl : -2≤runKey u := by
    have h:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hd : ((v : Int)-mass u)^2≤1 := by
    have hv : i=0 ∨ i=1 := by omega
    rcases hv with rfl|rfl
    · have hh : (v : Int)-mass u= -1 := by omega
      rw [hh]
      decide
    · have hh : (v : Int)-mass u=0 := by omega
      rw [hh]
      decide
  rw [runKey_append_S,runKey_append,mass_append,hmz,hmeasure] at hkey
  grind only

theorem inversion_cap (S D I N d : Int) (hS : 0≤S) (hSN : S≤N)
    (hd : 0≤d) (hD : d≤D) (hN : 2*d≤N)
    (hkey : 2*I+2*D*S+D^2-1≤S^2) :
    2*I≤N*(N-2*d)-d*d+1 := by
  have ha:=Int.mul_nonneg (show 0≤D-d by omega) hS
  have hb:=Int.mul_nonneg (show 0≤D-d by omega) (show 0≤D+d by omega)
  have hc:=Int.mul_nonneg hS (show 0≤N-S by omega)
  have he:=Int.mul_nonneg (show 0≤N-2*d by omega) (show 0≤N-S by omega)
  grind only

end Recaman.OldSeedInversionKey
