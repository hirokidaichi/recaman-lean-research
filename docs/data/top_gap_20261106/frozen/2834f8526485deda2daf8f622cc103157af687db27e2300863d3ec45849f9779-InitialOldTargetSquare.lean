import Recaman.MomentTargetProfile

namespace Recaman.InitialOldTargetSquare

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse

/-- A counted initial-S source restricts the same selected old target.
The prefix between the old suffix and the source is a pure S word. -/
theorem initial_old_target_square (u x : List Bool) (d k T j : Nat) (hu : BlockWord u)
    (hmx : mass x+(k : Int)=1) (hkx : runKey x= -2)
    (hmt : mass ((u++(List.replicate d false++x))++List.replicate T true++List.replicate j false)=1)
    (hat : areaW ((u++(List.replicate d false++x))++List.replicate T true++List.replicate j false)=0) :
    let R := (j : Int)+1
    let tau := (T : Int)-(j : Int)-(k : Int)
    let A := ones x+(T : Int)
    R^2+(mass u)^2+tau^2≤2+2*tau*(A-R) := by
  dsimp only
  have hkt:=source_key_before_gap (u++(List.replicate d false++x)) T j hmt hat
  have hlo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hx:=mass_eq x
  have hs:=cntF_int x
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmt
  rw [runKey_append,runKey_prepend_S,hkx,cntF_append,cntF_replicate_S,Int.natCast_add] at hkt
  let R:=(j : Int)+1
  let tau:=(T : Int)-(j : Int)-(k : Int)
  let A:=ones x+(T : Int)
  have hd : (d : Int)=mass u+tau := by dsimp [tau]; omega
  have he : (d : Int)+(cntF x : Int)=mass u+A-R := by dsimp [A,R]; omega
  have hh : 2*R^2+runKey u-2+2*(d : Int)^2=
      4*tau*((d : Int)+(cntF x : Int)) := by
    dsimp only [R]
    grind only
  rw [he,hd] at hh
  change R^2+(mass u)^2+tau^2≤2+2*tau*(A-R)
  grind only

end Recaman.InitialOldTargetSquare
