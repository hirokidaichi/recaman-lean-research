import Recaman.FourthSourceFamilies
import Recaman.ShortCounterFactorBounds
import Recaman.UnitTargetSASProfile

namespace Recaman.ThirdSeparatorClock

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.AdjacentRunSupply Recaman.ShortCounterFactorBounds

/-- Source in the last head separator. Its clock is never one. At
clock zero it needs a suffix of length v+1 and fixes the third A length. -/
theorem third_separator_clock (s U v i : Nat) (hv : 1≤v)
    (he : sourceAt false s (List.replicate U true++List.replicate v false) i) :
    i≠1 ∧ 2*i≤v+2 ∧ (i=0 → v+1≤s ∧ U=2*v+2) := by
  obtain ⟨q,hq,hqs,hm,hk⟩:=he
  rw [←List.append_assoc,runKey_S_A_S] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  have heq : 2*(v : Int)*(i : Int)=((v : Int)+1)^2-(q : Int)^2 := by grind only
  have hq2 := square_lower (q : Int) 1 (by decide) (by omega)
  refine ⟨?_,?_,?_⟩
  · intro hi
    rw [hi] at heq
    by_cases hqv : q≤v
    · have hsq := square_lower (v : Int) (q : Int) (by omega) (by omega)
      grind only
    · have hsq := square_lower (q : Int) ((v : Int)+1) (by omega) (by omega)
      grind only
  · by_cases hb : 2*i≤v+2
    · exact hb
    · have hp := Int.mul_nonneg (show 0≤(v : Int) by omega)
        (show 0≤2*(i : Int)-(v : Int)-3 by omega)
      grind only
  · intro hi
    rw [hi] at heq hm
    have hqv : q=v+1 := by
      have hp : ((q : Int)-((v : Int)+1))*((q : Int)+(v : Int)+1)=0 := by grind only
      rcases Int.mul_eq_zero.mp hp with h|h <;> omega
    omega

theorem third_separator_or_pair (s U v i : Nat) (hv : 1≤v)
    (he : Recaman.ThreeNonsuppliedData.localSupply
      ((List.replicate s false++(List.replicate U true++List.replicate v false))++
        List.replicate i true)=true) :
    sourceAt false s (List.replicate U true++List.replicate v false) i ∨ i=2 := by
  rcases (local_const_split false s _ i).mp he with hs|hp
  · exact Or.inl hs
  · exact Or.inr ((local_A_S_clock_iff U v i hv).mp hp)

theorem second_A_or_third_separator_or_pair (L s U v i : Nat) (hv : 1≤v)
    (he : Recaman.ThreeNonsuppliedData.localSupply
      ((List.replicate L true++(List.replicate s false++(List.replicate U true++List.replicate v false)))++
        List.replicate i true)=true) :
    sourceAt true L (List.replicate s false++(List.replicate U true++List.replicate v false)) i ∨
    sourceAt false s (List.replicate U true++List.replicate v false) i ∨ i=2 := by
  rcases (local_const_split true L _ i).mp he with hs|hp
  · exact Or.inl hs
  · exact Or.inr (third_separator_or_pair s U v i hv hp)

theorem second_A_one_unit_tail_absent (s i : Nat) :
    ¬sourceAt true 1 (List.replicate s false++(List.replicate 4 true++List.replicate 1 false)) i := by
  rintro ⟨q,hq,hq1,_,hk⟩
  have he : q=1 := by omega
  subst q
  rw [runKey_prepend_A,←List.append_assoc,runKey_S_A_S] at hk
  have hcnt : cntF (List.replicate s false++List.replicate 4 true++List.replicate 1 false)=s+1 := by
    simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,Nat.add_zero]
  rw [hcnt,Int.natCast_add] at hk
  have hs10 : (s : Int)^2=10 := by grind only
  by_cases hs3 : s≤3
  · have hs:=square_lower 3 (s : Int) (by omega) (by omega)
    grind only
  · have hs:=square_lower (s : Int) 4 (by decide) (by omega)
    grind only

/-- Two sources in the same constant block and with the same following
word cannot pay different clocks, even with different depth bounds. -/
theorem same_family_clock (b : Bool) (N K i k : Nat) (x : List Bool)
    (hi : sourceAt b N x i) (hk : sourceAt b K x k) : i=k := by
  obtain ⟨q,hq,_,hmi,hki⟩:=hi
  obtain ⟨r,hr,_,hmk,hkk⟩:=hk
  have he:=constant_run_root_unique b q r x hq hr hki hkk
  subst r
  omega

end Recaman.ThirdSeparatorClock
