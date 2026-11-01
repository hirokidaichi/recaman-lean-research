import Recaman.OneGapInteriorA

namespace Recaman.ShortGapSourceClocks

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- For an initial S-source, the full moment band admits only clock0
when v=2, or clock1 when v=3. The v=1 source family is empty. -/
theorem initial_S_small_gap_clock (d v i : Nat) (x : List Bool) (B : Int)
    (hm : mass (List.replicate d false++x)=0)
    (ha : areaW (List.replicate d false++x)= -B)
    (hS : 3≤cntF (List.replicate d false++x))
    (hlo : 4*(cntF (List.replicate d false++x) : Int)+6≤B)
    (hhi : B≤6*(cntF (List.replicate d false++x) : Int)+4)
    (hv : 1≤v) (hv3 : v≤3)
    (hbal : mass (x++List.replicate v false)+(i : Int)=1)
    (hkey : runKey (x++List.replicate v false)= -2) :
    (v=2 ∧ i=0 ∧ B=6*(cntF (List.replicate d false++x) : Int)) ∨
      (v=3 ∧ i=1 ∧ B=6*(cntF (List.replicate d false++x) : Int)+1) := by
  let S:=cntF (List.replicate d false++x)
  have hcnt : (cntF x : Int)=(S : Int)-(d : Int) := by
    dsimp [S]
    rw [cntF_append,cntF_replicate_S]
    omega
  have hm' := hm
  rw [mass_append,mass_rep_false] at hm'
  have hbal' := hbal
  rw [mass_append,mass_rep_false] at hbal'
  have hd : d+i=v+1 := by omega
  have hkz : runKey (List.replicate d false++x)= -2*B := by unfold runKey; rw [hm,ha]; grind only
  rw [runKey_prepend_S,hcnt] at hkz
  have hkey' := hkey
  rw [runKey_append_S] at hkey'
  have hB : B=2*(d : Int)*((S : Int)+(v : Int))-(d : Int)^2-(v : Int)^2+1 := by grind only
  change 3≤S at hS
  change 4*(S : Int)+6≤B at hlo
  change B≤6*(S : Int)+4 at hhi
  change (v=2 ∧ i=0 ∧ B=6*(S : Int)) ∨ (v=3 ∧ i=1 ∧ B=6*(S : Int)+1)
  have hvv : v=1 ∨ v=2 ∨ v=3 := by omega
  rcases hvv with rfl|rfl|rfl
  · have hdv : d=0 ∨ d=1 ∨ d=2 := by omega
    rcases hdv with rfl|rfl|rfl <;> omega
  · have hdv : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases hdv with rfl|rfl|rfl|rfl <;> omega
  · have hdv : d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 := by omega
    rcases hdv with rfl|rfl|rfl|rfl|rfl <;> omega

theorem nonnegative_square_gap (x k d : Int) (hx : 0≤x) (hk : 0≤k)
    (hlo : k*k<d) (hhi : d<(k+1)*(k+1)) : x*x≠d := by
  intro he
  by_cases hh : x≤k
  · have hp:=Int.mul_nonneg (show 0≤k-x by omega) (show 0≤k+x by omega)
    grind only
  · have hp:=Int.mul_nonneg (show 0≤x-k-1 by omega) (show 0≤x+k+1 by omega)
    grind only

/-- The third S-run source and the immediate final-S source share only
clocks0/2 when the final separator has length at most three. -/
theorem tail_S_small_gap_clock (q U v i : Nat) (hq : 1≤q) (hv : 1≤v) (hv3 : v≤3)
    (hm : mass (List.replicate q false++List.replicate U true++List.replicate v false)+(i : Int)=1)
    (hk : runKey (List.replicate q false++List.replicate U true++List.replicate v false)= -2) :
    i=0 ∨ i=2 := by
  rw [runKey_S_A_S] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  have he : (q : Int)^2=((v : Int)+1)^2-2*(v : Int)*(i : Int) := by grind only
  have hp:=Int.mul_nonneg (show 0≤(q : Int)-1 by omega) (show 0≤(q : Int)+1 by omega)
  have hsq : 1≤(q : Int)^2 := by grind only
  have hvv : v=1 ∨ v=2 ∨ v=3 := by omega
  rcases hvv with rfl|rfl|rfl
  · have hi : i=0 ∨ i=1 := by omega
    rcases hi with hi|rfl
    · exact Or.inl hi
    · have hn:=nonnegative_square_gap (q : Int) 1 2 (by omega) (by decide) (by decide) (by decide)
      exact False.elim (hn (by grind only))
  · have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with hi|rfl|hi
    · exact Or.inl hi
    · have hn:=nonnegative_square_gap (q : Int) 2 5 (by omega) (by decide) (by decide) (by decide)
      exact False.elim (hn (by grind only))
    · exact Or.inr hi
  · have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with hi|rfl|hi
    · exact Or.inl hi
    · have hn:=nonnegative_square_gap (q : Int) 3 10 (by omega) (by decide) (by decide) (by decide)
      exact False.elim (hn (by grind only))
    · exact Or.inr hi

end Recaman.ShortGapSourceClocks
