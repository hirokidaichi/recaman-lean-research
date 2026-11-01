import Recaman.FourRunTargetArea

namespace Recaman.LargePrefixTargetArea

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.ASourceReuse Recaman.RunClockClassifier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunTargetArea

/-- When the first two A runs already contain R signs, the same target
area rules out the even boundary A=2R+2. This is an A count, not free. -/
theorem large_first_two_A_budget (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s U v T j : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hshort : T≤j+2) (hML : j+1≤M+L)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    2*(j+1)+3≤M+L+U+T := by
  have hb:=old_target_short_last_A_budget u hu hne h M m L s U v T j
    hM hm hL hs hU hv hshort hmass harea
  let A : Int := (M : Int)+(L : Int)+(U : Int)+(T : Int)
  let R : Int := (j : Int)+1
  let I : Int := (M : Int)*((m : Int)+(s : Int)+(v : Int))+
    (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)
  have he:=old_target_area_identity u h M m L s U v T j hmass harea
  have hlow:=block_area_quadratic_lower hu
  have hC : 1≤mass u := (sufPos_block hu [] u rfl hne).1
  have hmp:=Int.mul_nonneg (show 0≤(M : Int) by omega)
    (show 0≤(m : Int)+(s : Int)+(v : Int)-3 by omega)
  have hlp:=Int.mul_nonneg (show 0≤(L : Int) by omega)
    (show 0≤(s : Int)+(v : Int)-2 by omega)
  have hup:=Int.mul_nonneg (show 0≤(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hI : A≤I := by dsimp [A,I]; grind only
  by_cases hh : 2*(j+1)+3≤M+L+U+T
  · exact hh
  · have hAe : A=2*R+2 := by dsimp [A,R]; omega
    have hq : (mass u)^2+2*I≤A*(A-2*R)+1 := by dsimp [A,R,I]; grind only
    have hC1 : mass u=1 := by
      have hp:=Int.mul_nonneg (show 0≤mass u-1 by omega) (show 0≤mass u+1 by omega)
      rw [hAe] at hq
      grind only
    have huA:=block_mass_one hu hC1
    rw [huA] at he
    have hmA : mass [true]=1 := by decide
    have haA : areaW [true]=1 := by decide
    rw [hmA,haA] at he
    have he' : 2=2*A*(A-2*R)-4*I := he
    rw [hAe] at he'
    have hz : 2*I=2*R*2+3 := by grind only
    omega

end Recaman.LargePrefixTargetArea
