import Recaman.FourRunTargetArea

namespace Recaman.AdjacentRunSupply

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.ASourceReuse Recaman.RunClockClassifier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A local source cannot start in the immediately preceding A run
when a genuine S separator is followed by an A-only ray. -/
theorem preceding_A_key_exclusion (a v : Nat) (ha : 1≤a) (hv : 1≤v) :
    runKey (List.replicate a true++List.replicate v false)≠ -2 := by
  intro hk
  rw [runKey_A_S] at hk
  have he : (v : Int)*((v : Int)-2*(a : Int))=1 := by grind
  by_cases hf : 0<(v : Int)-2*(a : Int)
  · have hp:=Int.mul_nonneg (show 0≤(v : Int) by omega)
      (show 0≤(v : Int)-2*(a : Int)-1 by omega)
    have hv1 : (v : Int)≤1 := by grind
    omega
  · have hp:=Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤(v : Int) by omega)
      (show (v : Int)-2*(a : Int)≤0 by omega)
    omega

/-- The last S alone supplies clock2; every earlier source inside the
preceding A block is impossible. All a/v/i are unbounded. -/
theorem local_A_S_clock_iff (a v i : Nat) (hv : 1≤v) :
    Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate a true++List.replicate v false++List.replicate i true)=true ↔ i=2 := by
  have hh:=localSupply_two_run_iff 0 a v i 0
  simp only [List.replicate_zero,List.nil_append,List.append_nil] at hh
  rw [hh]
  constructor
  · rintro (h|h|h)
    · obtain ⟨q,hq,hq0,_⟩:=h; omega
    · obtain ⟨e,he,hea,hbal,hkey⟩:=h
      have hk : runKey (List.replicate e true++List.replicate v false)= -2 := by
        rw [runKey_A_S]
        simp only [Int.natCast_zero,Int.zero_add,Int.one_pow] at hkey
        grind
      exact False.elim (preceding_A_key_exclusion e v he hv hk)
    · omega
  · intro hi
    exact Or.inr (Or.inr ⟨by omega,hv⟩)

theorem rayCount_A_S_le_one (a v K : Nat) (hv : 1≤v) :
    rayCount (List.replicate a true++List.replicate v false) K≤1 := by
  apply cN_le_one_of_unique
  intro i hi j hj hsi hsj
  have hi2: i=2 := (local_A_S_clock_iff a v i hv).mp hsi
  have hj2: j=2 := (local_A_S_clock_iff a v j hv).mp hsj
  omega

/-- The cost of a chosen constant-run prefix is additive even when the
remaining suffix is arbitrary. This is a local count, no old-base reset. -/
theorem run_prefix_ray_budget (rs : List (Bool × Nat)) (z : List Bool) (K : Nat) :
    rayCount (runWord rs++z) K≤rs.length+rayCount z K := by
  induction rs with
  | nil => simp [runWord]
  | cons r rs ih =>
    obtain ⟨b,N⟩:=r
    have hb:=rayCount_const_append b N (runWord rs++z) K
    simp only [runWord,List.length_cons,List.append_assoc] at *
    omega

/-- Four-ray local supply has at most six clocks, not the seven from
counting each preceding constant block separately. -/
theorem fourth_ray_local_le_six (h M m L s U v K : Nat) (hv : 1≤v) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤6 := by
  have hp:=run_prefix_ray_budget [(false,h),(true,M),(false,m),(true,L),(false,s)]
    (List.replicate U true++List.replicate v false) K
  have hb:=rayCount_A_S_le_one U v K hv
  simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,
    List.append_assoc] at hp
  rw [List.append_assoc,List.append_assoc,List.append_assoc,List.append_assoc,List.append_assoc] at ⊢
  omega

/-- Dropping the genuine separator would invalidate the clock2 iff. -/
theorem empty_separator_control :
    Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate 7 true++List.replicate 0 false++List.replicate 2 true)=false := by decide

end Recaman.AdjacentRunSupply
