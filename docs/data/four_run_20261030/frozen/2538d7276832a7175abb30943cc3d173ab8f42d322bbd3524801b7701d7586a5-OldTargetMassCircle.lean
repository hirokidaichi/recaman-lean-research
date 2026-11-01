import Recaman.LargePrefixTargetArea

namespace Recaman.OldTargetMassCircle

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.ASourceReuse Recaman.RunClockClassifier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunTargetArea

/-- A measured A budget bounds only the target old suffix mass. It does
not bound other suppliers or permit erasing earlier actual history. -/
theorem target_mass_circle (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s U v T j budget : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hshort : T≤j+2)
    (hbudget : M+L+U+T≤j+1+budget)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    (mass u)^2+((j : Int)+1)^2≤((budget : Int)-1)^2-4 := by
  let A : Int:=(M : Int)+(L : Int)+(U : Int)+(T : Int)
  let R : Int:=(j : Int)+1
  let I : Int:=(M : Int)*((m : Int)+(s : Int)+(v : Int))+
    (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)
  have he:=old_target_area_identity u h M m L s U v T j hmass harea
  have hl:=block_area_quadratic_lower hu
  have hAlo:=old_target_short_last_A_budget u hu hne h M m L s U v T j
    hM hm hL hs hU hv hshort hmass harea
  have hpM:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)+(v : Int)-3 by omega)
  have hpL:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)+(v : Int)-2 by omega)
  have hpU:=Int.mul_nonneg (show 0≤(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hI : A-R+2≤I := by dsimp [A,R,I]; grind only
  have hq : (mass u)^2+2*I≤A*(A-2*R)+1 := by dsimp [A,R,I]; grind only
  have hx : 0≤A-R-1 := by dsimp [A,R]; omega
  have hxb : A-R-1≤(budget : Int)-1 := by dsimp [A,R]; omega
  have hp:=Int.mul_nonneg (show 0≤(budget : Int)-1-(A-R-1) by omega)
    (show 0≤(budget : Int)-1+(A-R-1) by omega)
  have hb : (A-R-1)^2≤((budget : Int)-1)^2 := by grind only
  change (mass u)^2+R^2≤((budget : Int)-1)^2-4
  grind only

/-- If the first-two-run A count is large, the cross term is at least A
and gives the tighter circle with R+1. -/
theorem large_prefix_mass_circle (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s U v T j budget : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hshort : T≤j+2) (hML : j+1≤M+L)
    (hbudget : M+L+U+T≤j+1+budget)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    (mass u)^2+((j : Int)+2)^2≤((budget : Int)-1)^2+1 := by
  let A : Int:=(M : Int)+(L : Int)+(U : Int)+(T : Int)
  let R : Int:=(j : Int)+1
  let I : Int:=(M : Int)*((m : Int)+(s : Int)+(v : Int))+
    (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)
  have he:=old_target_area_identity u h M m L s U v T j hmass harea
  have hl:=block_area_quadratic_lower hu
  have hAlo:=old_target_short_last_A_budget u hu hne h M m L s U v T j
    hM hm hL hs hU hv hshort hmass harea
  have hpM:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)+(v : Int)-3 by omega)
  have hpL:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)+(v : Int)-2 by omega)
  have hpU:=Int.mul_nonneg (show 0≤(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hI : A≤I := by dsimp [A,I]; grind only
  have hq : (mass u)^2+2*I≤A*(A-2*R)+1 := by dsimp [A,R,I]; grind only
  have hx : 0≤A-R-1 := by dsimp [A,R]; omega
  have hxb : A-R-1≤(budget : Int)-1 := by dsimp [A,R]; omega
  have hp:=Int.mul_nonneg (show 0≤(budget : Int)-1-(A-R-1) by omega)
    (show 0≤(budget : Int)-1+(A-R-1) by omega)
  have hb : (A-R-1)^2≤((budget : Int)-1)^2 := by grind only
  have heq : ((j : Int)+2)^2=(R+1)^2 := by dsimp [R]; omega
  rw [heq]
  grind only

end Recaman.OldTargetMassCircle
