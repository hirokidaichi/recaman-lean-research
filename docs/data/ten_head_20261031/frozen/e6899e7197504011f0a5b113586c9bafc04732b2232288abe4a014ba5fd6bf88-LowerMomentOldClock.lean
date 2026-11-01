import Recaman.MomentTargetProfile

namespace Recaman.LowerMomentOldClock

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem band_clock_scalar (C V I B S : Int) (hC : 3≤C) (hS : 0≤S) (hI : 0≤I)
    (hm : C-V+I=1) (hB : B≤6*S+4) (hk : 0≤B+V*V-2*C*(S+V)) : 4≤I := by
  by_cases hi : 4≤I
  · exact hi
  · let x:=V-I
    have hx : 2≤x := by dsimp [x]; omega
    have hp:=Int.mul_nonneg hI (show 0≤3-I by omega)
    have hiq : I*I≤3*I := by grind only
    have hq:=Int.mul_nonneg (show 0≤x-2 by omega) (show 0≤x+2 by omega)
    have hxq : 4≤x*x := by grind only
    have hqS:=Int.mul_nonneg (show 0≤x-2 by omega) (show 0≤S+1 by omega)
    have hxS : 2*S+2≤x*(S+1) := by grind only
    have hCx : C=x+1 := by dsimp [x]; omega
    have hVx : V=I+x := by dsimp [x]; omega
    rw [hCx,hVx] at hk
    have he : B+(I+x)*(I+x)-2*(x+1)*(S+(I+x))=
        B+I*I-2*I-x*x-2*(x*(S+1))-2*S := by grind only
    rw [he] at hk
    omega


/-- One unit below the old-clock-four band, every old supplier at clock0/1
has the exact mass-two AA profile. This is not an actual-free conclusion. -/
theorem early_old_lower_boundary (w z : List Bool) (hw : BlockWord w) (B : Int)
    (hmz : mass z=0) (haz : areaW z= -B)
    (hlo : 4*(cntF z : Int)+5≤B) (hhi : B≤6*(cntF z : Int)+4)
    (v i : Nat) (hv : 1≤v) (hi : i≤1)
    (he : tailOldRay w (z++List.replicate v false) i) :
    v=2 ∧ i=1 ∧ B=4*(cntF z : Int)+5 ∧
      ∃ t, t<w.length ∧ w.drop t=[true,true] := by
  obtain ⟨t,ht,hm,hk⟩:=he
  let u:=w.drop t
  have hu : BlockWord u := block_suffix hw (w.take t) u (List.take_append_drop t w)
  have hne : u≠[] := by
    intro hz
    have hh : u.length=w.length-t := List.length_drop
    rw [hz] at hh
    simp only [List.length_nil] at hh
    omega
  have hC : 1≤mass u := (sufPos_block hu [] u rfl hne).1
  have hl : -2≤runKey u := by have hh:=block_area_quadratic_lower hu; unfold runKey; omega
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz,haz]; grind only
  change mass u+mass (z++List.replicate v false)+(i : Int)=1 at hm
  change runKey u+runKey (z++List.replicate v false)+4*mass u*(cntF (z++List.replicate v false) : Int)= -2 at hk
  rw [mass_append,hmz,mass_rep_false] at hm
  rw [runKey_append_S,hkz,hmz,cntF_append,cntF_replicate_S] at hk
  simp only [Int.natCast_add] at hk
  have hkey : runKey u=2*B-2+2*(v : Int)^2-4*mass u*((cntF z : Int)+(v : Int)) := by grind only
  have hC2 : mass u≤2 := by
    by_cases hh : mass u≤2
    · exact hh
    · have hp : 0≤B+(v : Int)*(v : Int)-2*mass u*((cntF z : Int)+(v : Int)) := by grind only
      have hc:=band_clock_scalar (mass u) (v : Int) (i : Int) B (cntF z : Int)
        (by omega) (by omega) (by omega) (by omega) hhi hp
      omega
  have hic : i=0 ∨ i=1 := by omega
  by_cases h1 : mass u=1
  · have hu1:=block_mass_one hu h1
    have hku : runKey u=0 := by rw [hu1]; decide
    rw [h1,hku] at hm hkey
    rcases hic with h0|h1i <;> subst i <;> norm_num at hm hkey <;> grind only
  · have h2 : mass u=2 := by omega
    have hv2 : v=2 := by omega
    have hi1 : i=1 := by omega
    subst v; subst i
    rcases block_mass_two hu h2 with hAA|hSAAA
    · have hku : runKey u=0 := by rw [hAA]; decide
      refine ⟨rfl,rfl,?_,t,ht,hAA⟩
      rw [h2,hku] at hkey
      norm_num at hkey
      grind only
    · have hku : runKey u= -2 := by rw [hSAAA]; decide
      rw [h2,hku] at hkey
      norm_num at hkey
      grind only

end Recaman.LowerMomentOldClock
