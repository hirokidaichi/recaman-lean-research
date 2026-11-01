import Recaman.TerminalLocalProfile

namespace Recaman.TerminalOldClock

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.TerminalLocalProfile

private theorem mass_one_two_key_nonpositive (u : List Bool) (hu : BlockWord u)
    (hC : 1≤mass u) (hC2 : mass u≤2) : runKey u≤0 := by
  by_cases h1 : mass u=1
  · rw [block_mass_one hu h1]
    decide
  · rcases block_mass_two hu (by omega) with h|h <;> rw [h] <;> decide

private theorem clock_scalar (C V I : Int) (hC : 3≤C) (hV : 1≤V) (hI : 0≤I)
    (hm : C-V+I=1) (hk : -2≤122+2*V*V-4*C*(10+V)) : 4≤I := by
  by_cases hi : 4≤I
  · exact hi
  · let x:=V-I
    have hx : 2≤x := by dsimp [x]; omega
    have hp:=Int.mul_nonneg hI (show 0≤3-I by omega)
    have hiq : I*I≤3*I := by grind only
    have hq:=Int.mul_nonneg (show 0≤x-2 by omega) (show 0≤x+2 by omega)
    have hxq : 4≤x*x := by grind only
    have hz : 0≤2*I*I-4*I+84-44*x-2*x*x := by dsimp [x]; grind only
    omega

/-- A source in the unchanged old BlockWord cannot supply before clock4
after the fixed seed and ANY positive S gap. Its mass is unrestricted. -/
theorem terminal_old_clock_ge_four (w : List Bool) (hw : BlockWord w) (v i : Nat)
    (hv : 1≤v) (he : tailOldRay w (seed++List.replicate v false) i) : 4≤i := by
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
  have hmseed : mass seed=0 := by decide
  have hkseed : runKey seed= -124 := by decide
  have hcseed : cntF seed=10 := by decide
  change mass u+mass (seed++List.replicate v false)+(i : Int)=1 at hm
  change runKey u+runKey (seed++List.replicate v false)+4*mass u*(cntF (seed++List.replicate v false) : Int)= -2 at hk
  rw [mass_append,hmseed,mass_rep_false] at hm
  rw [runKey_append_S,hkseed,hmseed,cntF_append,hcseed,cntF_replicate_S] at hk
  simp only [Int.natCast_add] at hk
  change runKey u+(-124+4*(v : Int)*0-2*(v : Int)^2)+4*mass u*(10+(v : Int))= -2 at hk
  have hkey : runKey u=122+2*(v : Int)^2-4*mass u*(10+(v : Int)) := by grind only
  have hC3 : 3≤mass u := by
    by_cases hh : 3≤mass u
    · exact hh
    · have hkn:=mass_one_two_key_nonpositive u hu hC (by omega)
      have hp:=Int.sq_nonneg ((v : Int)-mass u)
      by_cases h1 : mass u=1
      · rw [h1] at hkey
        have hs:=Int.sq_nonneg ((v : Int)-1)
        grind only
      · have h2 : mass u=2 := by omega
        rw [h2] at hkey
        have hs:=Int.sq_nonneg ((v : Int)-2)
        grind only
  have hp : -2≤122+2*(v : Int)*(v : Int)-4*mass u*(10+(v : Int)) := by grind only
  have hh:=clock_scalar (mass u) (v : Int) (i : Int) hC3 (by omega) (by omega) (by omega) hp
  omega

end Recaman.TerminalOldClock
