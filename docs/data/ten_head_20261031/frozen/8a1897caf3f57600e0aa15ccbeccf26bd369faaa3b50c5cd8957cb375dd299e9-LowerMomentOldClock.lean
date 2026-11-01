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
    rw [h1] at hm
    rw [h1,hku] at hkey
    have hv1 : v=1 := by omega
    have hi1 : i=1 := by omega
    subst v; subst i
    simp only [Int.natCast_one] at hkey
    grind only
  · have h2 : mass u=2 := by omega
    rw [h2] at hm
    have hvi : (v=1 ∧ i=0) ∨ (v=2 ∧ i=1) := by omega
    rcases hvi with ⟨hv1,hi0⟩|⟨hv2,hi1⟩
    · subst v; subst i
      rcases block_mass_two hu h2 with hAA|hSAAA
      · have hku : runKey u=0 := by rw [hAA]; decide
        rw [h2,hku] at hkey
        grind only
      · have hku : runKey u= -2 := by rw [hSAAA]; decide
        rw [h2,hku] at hkey
        grind only
    · subst v; subst i
      rcases block_mass_two hu h2 with hAA|hSAAA
      · have hku : runKey u=0 := by rw [hAA]; decide
        refine ⟨rfl,rfl,?_,t,ht,hAA⟩
        rw [h2,hku] at hkey
        grind only
      · have hku : runKey u= -2 := by rw [hSAAA]; decide
        rw [h2,hku] at hkey
        grind only

private theorem twice_area_parity (z : List Bool) :
    ∃ k : Int, 2*areaW z=(z.length : Int)*((z.length : Int)+1)+4*k := by
  induction z with
  | nil => exact ⟨0,by decide⟩
  | cons x z ih =>
    obtain ⟨k,hk⟩:=ih
    cases x
    · refine ⟨k-(z.length : Int)-1,?_⟩
      simp only [areaW,Recaman.ShortPeriodicSupply.sign,List.length_cons,Int.natCast_add,Int.natCast_one]
      grind only
    · refine ⟨k,?_⟩
      simp only [areaW,Recaman.ShortPeriodicSupply.sign,List.length_cons,Int.natCast_add,Int.natCast_one]
      grind only

/-- The missing parity obstruction is a word fact, not an assumed rank. -/
theorem lower_five_circle_excluded (z : List Bool) (hmz : mass z=0)
    (B R : Int) (haz : areaW z= -B) (hB : B=4*(cntF z : Int)+5)
    (hcircle : R*R=2*(cntF z : Int)+5) : False := by
  let S:=(cntF z : Int)
  have hlen : (z.length : Int)=2*S := by have h:=mass_cntF z; rw [hmz] at h; dsimp [S]; omega
  obtain ⟨k,hk⟩:=twice_area_parity z
  rw [haz,hlen] at hk
  have hsplit : -B=2*(S*S)+S+2*k := by grind only
  change B=4*S+5 at hB
  have hSodd : S%2=1 := by omega
  have hSrep : S=2*(S/2)+1 := by omega
  have hRrep : R=2*(R/2) ∨ R=2*(R/2)+1 := by omega
  change R*R=2*S+5 at hcircle
  rcases hRrep with he|ho
  · rw [he,hSrep] at hcircle
    have hh : 4*((R/2)*(R/2))=4*(S/2)+7 := by grind only
    omega
  · rw [ho,hSrep] at hcircle
    have hh : 4*((R/2)*(R/2))+4*(R/2)+1=4*(S/2)+7 := by grind only
    omega

/-- Same-prefix target coupling excludes every old supplier on the last
short ray even at lower band 4S+5. The older uncoupled clock-four lemma
needs 4S+6; this statement keeps the measured target window. -/
theorem lower_band_target_no_old (w z : List Bool) (hw : BlockWord w) (B : Int)
    (hmz : mass z=0) (haz : areaW z= -B)
    (hlo : 4*(cntF z : Int)+5≤B) (hhi : B≤6*(cntF z : Int)+4)
    (s v T j i : Nat) (hs : s<w.length) (hv : 1≤v) (hj : 2≤j)
    (hshort : T≤j+2) (hi : i<T)
    (hm : mass (w.drop s++z++List.replicate v false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (w.drop s++z++List.replicate v false++List.replicate T true++List.replicate j false)=0) :
    ¬tailOldRay w (z++List.replicate v false) i := by
  intro he
  obtain ⟨t,ht,hmt,hkt⟩:=he
  have hm1 : mass (w.drop t++(z++List.replicate v false)++List.replicate i true)=1 := by
    simpa only [mass_append,mass_replicate_A] using hmt
  have hk1 : runKey (w.drop t++(z++List.replicate v false))= -2 := by
    rw [runKey_append]
    exact hkt
  have ha1 : areaW (w.drop t++(z++List.replicate v false)++List.replicate i true)=0 := by
    have hkey : runKey (w.drop t++(z++List.replicate v false)++List.replicate i true)= -2 := by
      rw [runKey_append_A,hk1]
    unfold runKey at hkey
    rw [hm1] at hkey
    omega
  have ho:=Recaman.OldSourceKeyOrder.old_target_prior_clock w (z++List.replicate v false) hw t s i T j hj hm1 ha1
    (by simpa only [List.append_assoc] using hm) (by simpa only [List.append_assoc] using ha)
  have hi1 : i≤1 := by omega
  obtain ⟨hv2,hi1,hB,tAA,htAA,hAA⟩:=early_old_lower_boundary w z hw B hmz haz hlo hhi v i hv hi1 ⟨t,ht,hmt,hkt⟩
  have huu : BlockWord (w.drop s) := block_suffix hw (w.take s) (w.drop s) (List.take_append_drop s w)
  have hne : w.drop s≠[] := by
    intro heq
    have hh : (w.drop s).length=w.length-s := List.length_drop
    rw [heq] at hh
    simp only [List.length_nil] at hh
    omega
  have hC : 1≤mass (w.drop s) := (sufPos_block huu [] (w.drop s) rfl hne).1
  have hC2 : mass (w.drop t)=2 := by
    change mass (w.drop t)+mass (z++List.replicate v false)+(i : Int)=1 at hmt
    rw [mass_append,hmz,mass_rep_false,hv2,hi1] at hmt
    omega
  have hC1 : mass (w.drop s)=1 := by omega
  have huA:=block_mass_one huu hC1
  have hku : runKey (w.drop s)=0 := by rw [huA]; decide
  have hk:=Recaman.ASourceReuse.source_key_before_gap (w.drop s++z++List.replicate v false) T j hm ha
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz,haz]; grind only
  rw [runKey_append_S,runKey_append,hkz,mass_append,hmz,hC1,hku,hv2] at hk
  have hc : ((j : Int)+1)*((j : Int)+1)=2*(cntF z : Int)+5 := by grind only
  exact lower_five_circle_excluded z hmz B ((j : Int)+1) haz hB hc

end Recaman.LowerMomentOldClock
