import Recaman.ThirdSPairedSupply
import Recaman.SourceFamilyFreeCount

namespace Recaman.SeparatedSSourceCut

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock
open Recaman.ShortCounterFactorBounds

/-- If both S families supply the same final A ray, the earlier suffix
depth is strictly smaller than the intervening A length. -/
theorem earlier_S_depth_cut (m L s U v i j : Nat)
    (he : sourceAt false m (List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i)
    (hl : sourceAt false s (List.replicate U true++List.replicate v false) j) :
    sourceAt false (min m (L-1)) (List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i := by
  obtain ⟨b,hb,hbm,hm,hk⟩:=he
  obtain ⟨k,hk1,hks,_,hlk⟩:=hl
  have hkey:=Recaman.SourceFamilyFreeCount.runKey_five_runs b L s U v
  have hke : runKey (List.replicate b false++(List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false))=
      4*(L : Int)*((s : Int)+(v : Int))+4*(U : Int)*(v : Int)-
        2*((b : Int)+(s : Int)+(v : Int))^2 := by
    simpa only [List.append_assoc] using hkey
  rw [hke] at hk
  rw [←List.append_assoc,runKey_S_A_S] at hlk
  let z:=(s : Int)+(v : Int)
  let y:=(k : Int)+(v : Int)
  have hz : 1≤z := by dsimp [z]; omega
  have hy : 1≤y := by dsimp [y]; omega
  have hyz : y≤z := by dsimp [y,z]; omega
  have hsquare:=square_lower z y (by omega) hyz
  have heq : ((b : Int)+z)^2=y^2+2*(L : Int)*z := by dsimp [z,y]; grind only
  have hbl : b<L := by
    by_cases h : b<L
    · exact h
    · have hprod:=Int.mul_nonneg (show 0≤(b : Int)-(L : Int) by omega) (show 0≤z by omega)
      have hb2:=square_lower (b : Int) 1 (by decide) (by omega)
      grind only
  exact ⟨b,hb,by omega,hm,hk⟩

/-- An intervening A interval of length at most one forbids the two
S families, with no restriction on their independent clocks. -/
theorem unit_A_S_collision (m L s U v i j : Nat) (hL : L≤1)
    (he : sourceAt false m (List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i)
    (hl : sourceAt false s (List.replicate U true++List.replicate v false) j) : False := by
  obtain ⟨b,hb,hbN,_,_⟩:=earlier_S_depth_cut m L s U v i j he hl
  omega

/-- The two S families use one clock budget when the intervening A is unit. -/
theorem paired_S_count (m L s U v K : Nat) (hL : L≤1) :
    cN (fun i=>sourceAt false m (List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i ∨
      sourceAt false s (List.replicate U true++List.replicate v false) i) 0 K≤1 := by
  apply cN_le_one_of_unique
  intro i hi j hj hsi hsj
  rcases hsi with he|hl
  · rcases hsj with hE|hL'
    · exact same_family_clock false m m i j _ he hE
    · exact False.elim (unit_A_S_collision m L s U v i j hL he hL')
  · rcases hsj with hE|hL'
    · exact False.elim (unit_A_S_collision m L s U v j i hL hE hl)
    · exact same_family_clock false s s i j _ hl hL'

end Recaman.SeparatedSSourceCut
