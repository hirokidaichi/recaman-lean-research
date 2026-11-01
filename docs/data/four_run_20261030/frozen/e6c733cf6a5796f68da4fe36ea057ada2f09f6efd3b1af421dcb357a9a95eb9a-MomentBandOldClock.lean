import Recaman.TerminalOldClock

namespace Recaman.MomentBandOldClock

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

/-- A quantitative area band of ANY zero-mass sign word excludes all
old-source clocks before4 after a genuine S gap. Other old masses and
all word lengths remain unrestricted. It is not a local-supply bound. -/
theorem moment_band_old_clock (w z : List Bool) (hw : BlockWord w) (B : Int)
    (hmz : mass z=0) (haz : areaW z= -B)
    (hlo : 4*(cntF z : Int)+6≤B) (hhi : B≤6*(cntF z : Int)+4)
    (v i : Nat) (hv : 1≤v) (he : tailOldRay w (z++List.replicate v false) i) : 4≤i := by
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
  have hC3 : 3≤mass u := by
    by_cases hh : 3≤mass u
    · exact hh
    · have hkn : runKey u≤0 := by
        by_cases h1 : mass u=1
        · rw [block_mass_one hu h1]; decide
        · rcases block_mass_two hu (by omega) with h|h <;> rw [h] <;> decide
      by_cases h1 : mass u=1
      · rw [h1] at hkey
        have hs:=Int.sq_nonneg ((v : Int)-1)
        have hz : 0≤(cntF z : Int) := by omega
        grind only
      · have h2 : mass u=2 := by omega
        rw [h2] at hkey
        have hs:=Int.sq_nonneg ((v : Int)-2)
        grind only
  have hp : 0≤B+(v : Int)*(v : Int)-2*mass u*((cntF z : Int)+(v : Int)) := by grind only
  have hc:=band_clock_scalar (mass u) (v : Int) (i : Int) B (cntF z : Int) hC3
    (by omega) (by omega) (by omega) hhi hp
  omega

/-- One unit above the upper band permits clock3. This raw word control
is not a completed C1 or standard-orbit counterexample. -/
theorem upper_band_raw_control :
    let u:=[false,true,true,true,true]
    let z:=List.replicate 6 false++[true,false]++List.replicate 6 true
    BlockWord u ∧ mass z=0 ∧ cntF z=7 ∧ areaW z= -47 ∧
    mass (u++z++List.replicate 5 false++List.replicate 3 true)=1 ∧
    areaW (u++z++List.replicate 5 false++List.replicate 3 true)=0 := by
  dsimp only
  refine ⟨?_,by decide,by decide,by decide,by decide,by decide⟩
  exact BlockWord.free (BlockWord.aas BlockWord.nil)

/-- One unit below the lower band permits clock1 with an old mass2. -/
theorem lower_band_raw_control :
    let u:=[true,true]
    let z:=List.replicate 5 false++List.replicate 5 true
    BlockWord u ∧ mass z=0 ∧ cntF z=5 ∧ areaW z= -25 ∧
    mass (u++z++List.replicate 2 false++List.replicate 1 true)=1 ∧
    areaW (u++z++List.replicate 2 false++List.replicate 1 true)=0 := by
  dsimp only
  refine ⟨?_,by decide,by decide,by decide,by decide,by decide⟩
  exact BlockWord.free (BlockWord.free BlockWord.nil)


/-- Actual same-base old Win supplies the profile premise internally.
No arbitrary old-source predicate is assumed by this version. -/
theorem actual_moment_band_old_clock (f : Nat → Bool) (n b t v i : Nat) (w z : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hnb : n≤b) (ht : t<n)
    (hhead : seg f n (b-n)=z) (B : Int) (hmz : mass z=0) (haz : areaW z= -B)
    (hlo : 4*(cntF z : Int)+6≤B) (hhi : B≤6*(cntF z : Int)+4) (hv : 1≤v)
    (hS : ∀ x, b≤x → x<b+v → f x=false)
    (hA : ∀ k, k<i → f (b+v+k)=true)
    (hwin : Win f t (b+v+i-t)) : 4≤i := by
  have hword : seg f n (b+v-n)=z++List.replicate v false := by
    rw [show b+v-n=(b-n)+v by omega,seg_add,show n+(b-n)=b by omega,
      hhead,seg_false f b v hS]
  have hAt : seg f (b+v) i=List.replicate i true := by
    apply seg_A
    intro x hx hxi
    have hh:=hA (x-(b+v)) (by omega)
    rw [show b+v+(x-(b+v))=x by omega] at hh
    exact hh
  have hn : w.length=n := by rw [←hpre,seg_length]
  have hbase:=seg_add f 0 n (b+v-n)
  simp only [Nat.zero_add,hpre,hword,Nat.add_sub_cancel' (show n≤b+v by omega)] at hbase
  have hfull:=seg_add f 0 (b+v) i
  simp only [Nat.zero_add,hbase,hAt] at hfull
  rw [List.append_assoc] at hfull
  have hd:=seg_drop f 0 (b+v+i) t (by omega)
  simp only [Nat.zero_add,Nat.sub_zero] at hd
  have hsuf : seg f t (b+v+i-t)=(w.drop t++(z++List.replicate v false))++List.replicate i true := by
    rw [←hd,hfull,List.drop_append,show t-w.length=0 by omega,List.drop_zero,←List.append_assoc]
  have hm : mass (seg f t (b+v+i-t))=1 := by
    rw [seg_mass,show t+(b+v+i-t)=b+v+i by omega]
    have hh:=hwin.2.1
    rw [show t+(b+v+i-t)=b+v+i by omega] at hh
    omega
  have ha : areaW (seg f t (b+v+i-t))=0 := by rw [←Ar_areaW]; exact hwin.2.2
  have hk : runKey (seg f t (b+v+i-t))= -2 := by unfold runKey; rw [hm,ha]; decide
  rw [hsuf,mass_append,mass_append,mass_replicate_A] at hm
  rw [hsuf,runKey_append_A,runKey_append] at hk
  exact moment_band_old_clock w z hw B hmz haz hlo hhi v i hv ⟨t,by omega,hm,hk⟩


def localCounterHead : List Bool := List.replicate 8 false++List.replicate 8 true++
  [false,true,true,true]++List.replicate 5 false++List.replicate 3 true++
  List.replicate 4 false++List.replicate 4 true

/-- The moment band constrains old BlockWord sources, not the arbitrary
local suffixes of z. This raw head has a local clock0 despite the band;
it is not a C1 or actual-orbit counterexample. -/
theorem moment_band_local_half_counterexample :
    mass localCounterHead=0 ∧ cntF localCounterHead=18 ∧ areaW localCounterHead= -86 ∧
    (4*18+6 : Int)≤86 ∧ (86 : Int)≤6*18+4 ∧
    Recaman.ThreeNonsuppliedData.localSupply (localCounterHead++[false])=true ∧
    ¬2*rayCount (localCounterHead++[false]) 1≤1 := by
  have hl : Recaman.ThreeNonsuppliedData.localSupply (localCounterHead++[false])=true := by
    rw [localSupply_iff]
    exact ⟨30,by decide,by decide,by decide⟩
  refine ⟨by decide,by decide,by decide,by decide,by decide,hl,?_⟩
  have he : rayCount (localCounterHead++[false]) 1=1 := by
    unfold rayCount
    rw [cN_succ_pos _ 0 0 (by simpa only [Nat.zero_add,List.replicate_zero,List.append_nil] using hl)]
    rfl
  rw [he]
  decide

end Recaman.MomentBandOldClock
