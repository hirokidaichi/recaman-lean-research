import Recaman.SourceFamilyFreeCount
import Recaman.ShortCounterFactorBounds

namespace Recaman.NonsquareHeadSupply

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The open interval between 6^2 and 7^2 contains no nonnegative integer square. -/
theorem square_gap (x K : Int) (hx : 0≤x) (hKlo : 18≤K) (hKhi : K≤23) :
    x^2≠2*K+1 := by
  intro he
  by_cases hx6 : x≤6
  · have hu:=Recaman.ShortCounterFactorBounds.square_lower 6 x hx hx6
    omega
  · have hl:=Recaman.ShortCounterFactorBounds.square_lower x 7 (by omega) (by omega)
    omega

/-- Every initial-S source is excluded by its required square; all run lengths are unbounded. -/
theorem initial_source_key_excluded (q M m L s : Nat)
    (hKlo : 18≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))
    (hKhi : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤23) :
    runKey (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)≠ -2 := by
  intro hk
  rw [Recaman.SourceFamilyFreeCount.runKey_five_runs] at hk
  have he : ((q : Int)+(m : Int)+(s : Int))^2=
      2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))+1 := by omega
  exact square_gap _ _ (by omega) hKlo hKhi he

private theorem erase_prefix_run (b : Bool) (N : Nat) (v : List Bool) (K : Nat)
    (hn : ∀ e, 1≤e → e≤N → runKey (List.replicate e b++v)≠ -2) :
    rayCount (List.replicate N b++v) K=rayCount v K := by
  unfold rayCount
  apply cN_congr
  intro i _ _
  rw [ray_supply_append_iff]
  constructor
  · rintro (ho|hl)
    · obtain ⟨t,ht,hm,hk⟩:=ho
      simp only [List.length_replicate] at ht
      have heq:=runKey_append ((List.replicate N b).drop t) v
      rw [List.drop_replicate] at heq hk
      have hz : runKey (List.replicate (N-t) b++v)= -2 := by omega
      exact False.elim (hn (N-t) (by omega) (by omega) hz)
    · exact hl
  · exact Or.inr

/-- Removing the impossible initial-S source leaves at most three local clocks, for every ray length. -/
theorem third_ray_three (h M m L s U : Nat)
    (hKlo : 18≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))
    (hKhi : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤23) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) U≤3 := by
  have he:=erase_prefix_run false h
    (List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false) U
    (fun q _ _=>by simpa only [List.append_assoc] using initial_source_key_excluded q M m L s hKlo hKhi)
  have ha:=rayCount_const_append true M
    (List.replicate m false++List.replicate L true++List.replicate s false) U
  have hs:=rayCount_S_A_S m L s U
  simp only [List.append_assoc] at he ha hs ⊢
  omega

end Recaman.NonsquareHeadSupply
