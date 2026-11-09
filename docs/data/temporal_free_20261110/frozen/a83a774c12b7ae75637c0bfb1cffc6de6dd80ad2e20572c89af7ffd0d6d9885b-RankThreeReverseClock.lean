import Recaman.LowCrossSupplyCount

namespace Recaman.RankThreeReverseClock

open Recaman.AdditionRankSlack Recaman.LowCrossLocalClocks
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

private theorem reverse_data (p u : List Bool) (i j : Nat)
    (hu : runKey u= -2) (hpu : runKey (p++u)= -2)
    (hm : mass u+(i : Int)=1) (hn : mass (p++u)+(j : Int)=1) :
    mass p=(i : Int)-(j : Int) ∧ (cntF p : Int)%2=0 ∧
    runKey p= -(4*((i : Int)-(j : Int))*(cntF u : Int)) := by
  have hmu : mass p=(i : Int)-(j : Int) := by rw [mass_append] at hn; omega
  have h1:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hu
  have h2:=Recaman.MixedASQuarterBudget.source_subtraction_odd (p++u) hpu
  rw [cntF_append,Int.natCast_add] at h2
  rw [runKey_append,hu,hmu] at hpu
  exact ⟨hmu,by omega,by omega⟩

private theorem large_future_forces_six (a s d F : Int)
    (ha : a≤7) (hs : 0≤s) (hd : 1≤d) (hf : 13≤F)
    (hM : a=s+d) (hpar : s%2=0) (hQ : 0≤2*s^2-4*d*F) :
    s=6 ∧ d=1 ∧ a=7 := by
  have h6 : s=6 := by
    by_cases h : s=6
    · exact h
    · have hs4 : s≤4 := by omega
      have hprod:=Int.mul_nonneg (show 0≤4-s by omega) (show 0≤4+s by omega)
      have hprod2:=Int.mul_nonneg (show 0≤d-1 by omega) (show 0≤F by omega)
      grind only
  exact ⟨h6,by omega,by omega⟩

private theorem small_future_if_two (a s d F : Int)
    (ha : a≤7) (hs : 0≤s) (hd : 2≤d) (hf : 1≤F)
    (hM : a=s+d) (hpar : s%2=0) (hQ : 0≤2*s^2-4*d*F) : F≤4 := by
  have hprod:=Int.mul_nonneg (show 0≤4-s by omega) (show 0≤4+s by omega)
  have hprod2:=Int.mul_nonneg (show 0≤d-2 by omega) (show 0≤F by omega)
  grind only

/-- In a positive original interval with at most three free additions,
a reverse primitive pair has inner clock at most six. If it drops by
at least two clocks, the inner clock is at most two. -/
theorem rank_three_reverse_clock_band (f : Nat → Bool) (n K i j : Nat) (w u : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hp : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hf : free f n K≤3) (hji : j<i)
    (hu : runKey u= -2) (hpu : runKey (seg f n K++u)= -2)
    (hmu : mass u+(i : Int)=1) (hmpu : mass (seg f n K++u)+(j : Int)=1) :
    i≤6 ∧ j≤5 ∧ cntF u≤11 ∧ (j+2≤i → i≤2) := by
  let a:=additions f n K
  let s:=subtractions f n K
  let d:=(i : Int)-(j : Int)
  let F:=cntF u
  have ha:=positive_r3_additions_free_bound f n 0 K hw
    (by simpa only [List.replicate_zero,List.append_nil] using hpre) hp hf
  change a≤2*free f n K+1 at ha
  obtain ⟨hm,hpar,hk⟩:=reverse_data (seg f n K) u i j hu hpu hmu hmpu
  change mass (seg f n K)=d at hm
  change runKey (seg f n K)= -(4*d*(F : Int)) at hk
  rw [cntF_seg] at hpar
  change (s : Int)%2=0 at hpar
  have hM:=seg_mass f n K
  have hwalk:=(cN_walk f n K).1
  change Fw f (n+K)=Fw f n+(a : Int)-(s : Int) at hwalk
  have hAdd : (a : Int)=(s : Int)+d := by omega
  have hQe : cross (seg f n K)=2*(s : Int)^2-4*d*(F : Int) := by
    unfold cross
    rw [hk,cntF_seg]
    change -(4*d*(F : Int))+2*(s : Int)^2=_
    omega
  have hQ:=cross_nonnegative (seg f n K)
  rw [hQe] at hQ
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hu
  change (F : Int)%2=1 at hodd
  have hF : F≤11 := by
    by_cases h : F≤11
    · exact h
    · obtain ⟨hS,hD,hA⟩:=large_future_forces_six (a : Int) (s : Int) d (F : Int)
        (by omega) (by omega) (by dsimp [d]; omega) (by omega) hAdd hpar hQ
      rw [hS,hD] at hQe
      have h20 : cross (seg f n K)≤20 := by omega
      have hmod : cross (seg f n K)%8=4 := by omega
      have hE:=Recaman.LowCrossSupplyCount.low_cross_original_supply_three f n K w hw hpre
        (by change s=6; omega) h20 hmod
      have hspl : a=cN (EndN f 0) n K+free f n K := additions_split f n K
      omega
  have hclock (h3 : 3≤cntF u) := Recaman.PrimitiveClockRadius.primitive_clock_half_S u i h3 hu hmu
  have hi1 (he : F=1) : i≤2 := by
    have hF' : cntF u=1 := he
    have hfo:=cntF_int u
    have hmass:=mass_eq u
    have h0:=(ones_bounds u).1
    omega
  have hi6 : i≤6 := by
    by_cases h1 : F=1
    · have h2:=hi1 h1
      omega
    · have h2:=hclock (by change 3≤F; omega)
      change 2*(i : Int)≤(F : Int)+1 at h2
      omega
  refine ⟨hi6,by omega,hF,?_⟩
  intro hj2
  have h4:=small_future_if_two (a : Int) (s : Int) d (F : Int)
    (by omega) (by omega) (by dsimp [d]; omega) (by omega) hAdd hpar hQ
  by_cases h1 : F=1
  · exact hi1 h1
  · have h2:=hclock (by change 3≤F; omega)
    change 2*(i : Int)≤(F : Int)+1 at h2
    omega

end Recaman.RankThreeReverseClock
