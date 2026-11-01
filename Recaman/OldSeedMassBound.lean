import Recaman.OldSourceKeyOrder

namespace Recaman.OldSeedMassBound

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.OldSourceKeyOrder Recaman.ASourceReuse

/-- A short last ray with an old seed and an old target cannot have
target mass at least six when the zero-mass head has at most sixteen S.
All source positions and both old suffixes belong to the same BlockWord. -/
theorem old_seed_high_target_impossible (w z : List Bool) (hw : BlockWord w)
    (hmz : mass z=0) (hS : cntF z≤16) (s v T j i : Nat)
    (hj : 2≤j) (hshort : T≤j+2) (hC : 6≤mass (w.drop s))
    (hseed : tailOldRay w (z++List.replicate v false) i)
    (hmt : mass (w.drop s++z++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (hat : areaW (w.drop s++z++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) : False := by
  obtain ⟨t,ht,hmi,hki⟩:=hseed
  let D:=mass (w.drop t)
  let C:=mass (w.drop s)
  let S:=(cntF z : Int)
  let a:=z++List.replicate v false
  have hkt:=source_key_before_gap (w.drop s++a) T j
    (by simpa only [a,List.append_assoc] using hmt)
    (by simpa only [a,List.append_assoc] using hat)
  have hki' : runKey (w.drop t++a)= -2 := by
    rw [runKey_append]
    exact hki
  have hp:=Int.mul_nonneg (show 0≤(j : Int)-2 by omega)
    (show 0≤(j : Int)+4 by omega)
  have hkeygap : runKey (w.drop s++a)+9≤runKey (w.drop t++a) := by
    rw [hki',hkt]
    grind only
  have hDC : C<D := old_key_mass_order w a hw t s hkeygap
  have htarget:=hmt
  simp only [mass_append,mass_rep_false,mass_replicate_A,hmz] at htarget
  have hseedmass : D-(v : Int)+(i : Int)=1 := by
    simp only [mass_append,hmz,mass_rep_false] at hmi
    dsimp [D]
    omega
  have hi1 : i≤1 := by dsimp [C] at hDC; omega
  have hD7 : 7≤D := by dsimp [C] at hDC; omega
  have hdelta : ((v : Int)-D)^2≤1 := by
    have hiv : i=0 ∨ i=1 := by omega
    rcases hiv with rfl|rfl
    · have he : (v : Int)-D= -1 := by omega
      rw [he]
      decide
    · have he : (v : Int)-D=0 := by omega
      rw [he]
      decide
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hlow : -2≤runKey (w.drop t) := by
    have h:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hhead:=runKey_count_lower z
  have hki0:=hki
  rw [runKey_append_S,hmz,cntF_append,cntF_replicate_S] at hki0
  simp only [Int.natCast_add] at hki0
  change runKey (w.drop t)+(runKey z+4*(v : Int)*0-2*(v : Int)^2)+
    4*D*(S+(v : Int))= -2 at hki0
  have hquad : 2*D*S+D^2-1≤S^2 := by
    change -2*S^2≤runKey z at hhead
    grind only
  have hDS:=Int.mul_nonneg (show 0≤D-7 by omega) (show 0≤S by dsimp [S]; omega)
  have hDsq:=Int.mul_nonneg (show 0≤D-7 by omega) (show 0≤D+7 by omega)
  have hS16 : S≤16 := by dsimp [S]; omega
  have hSsq:=Int.mul_nonneg (show 0≤S by dsimp [S]; omega) (show 0≤16-S by omega)
  grind only

end Recaman.OldSeedMassBound
