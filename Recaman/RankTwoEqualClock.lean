import Recaman.FourAdditionsJointSupply
import Recaman.RankTwoDistinctClocks

namespace Recaman.RankTwoEqualClock

open Recaman.AdditionRankSlack Recaman.LowCrossLocalClocks Recaman.LowCrossSegmentCuts
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

private theorem four_neutral_shape (x : List Bool) (hlen : x.length=4)
    (hA : ones x=2) (hQ : cross x=8) (hS : x[0]?=some false) :
    x=[false,true,true,false] := by
  cases x with
  | nil => simp at hlen
  | cons a x =>
    cases x with
    | nil => simp at hlen
    | cons b x =>
      cases x with
      | nil => simp at hlen
      | cons c x =>
        cases x with
        | nil => simp at hlen
        | cons d x =>
          have hx : x=[] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_cons] at hlen
            omega
          subst x
          cases a <;> cases b <;> cases c <;> cases d <;>
            simp [cross,ones,cntF,runKey,areaW,Recaman.ShortPeriodicSupply.sign] at hA hQ hS ⊢

/-- In an original positive interval with at most two free additions,
two different starts for one primitive clock are separated by SAAS. -/
theorem equal_clock_two_free_shape (f : Nat → Bool) (n K i : Nat) (w u : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hK : 0<K)
    (hpos : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hFree : free f n K≤2)
    (hu : runKey u= -2) (hpu : runKey (seg f n K++u)= -2)
    (hmu : mass u+(i : Int)=1) (hmpu : mass (seg f n K++u)+(i : Int)=1) :
    K=4 ∧ seg f n K=[false,true,true,false] ∧ free f n K=2 := by
  let p:=seg f n K
  let a:=additions f n K
  let s:=subtractions f n K
  have ha:=positive_r3_additions_free_bound f n 0 K hw
    (by simpa only [List.replicate_zero,List.append_nil] using hpre) hpos
    (by change free f n K≤3; omega)
  change a≤2*free f n K+1 at ha
  obtain ⟨hm,hpar,hk⟩:=Recaman.RankThreeReverseClock.reverse_data p u i i hu hpu hmu hmpu
  have hm0 : mass p=0 := by omega
  have hk0 : runKey p=0 := by rw [show (i : Int)-(i : Int)=0 by omega] at hk; omega
  have hsc : cntF p=s := cntF_seg f n K
  rw [hsc] at hpar
  have hM:=seg_mass f n K
  have hwalk:=(cN_walk f n K).1
  change Fw f (n+K)=Fw f n+(a : Int)-(s : Int) at hwalk
  have he : a=s := by change mass (seg f n K)=0 at hm0; omega
  have hLen : a+s=K := (cN_walk f n K).2
  have hCases : a=2 ∨ a=4 := by omega
  have hQ : cross p=2*(s : Int)^2 := by unfold cross; rw [hk0,hsc]; omega
  have h2 : a=2 := by
    rcases hCases with ha2|ha4
    · exact ha2
    · have hS4 : s=4 := by omega
      have hQ32 : cross p=32 := by rw [hQ,hS4]; decide
      have hn:=Recaman.FourAdditionsJointSupply.original_four_additions_supply_one
        f n K w hw hpre (by change a≤4; omega) (by change s≤4; omega)
        (by change cross p=0 → s≤2; omega)
      have hspl : a=cN (EndN f 0) n K+free f n K := additions_split f n K
      omega
  have hK4 : K=4 := by omega
  have h4 : p.length=4 := by change (seg f n K).length=4; rw [seg_length,hK4]
  have hfS : f n=false := by
    cases hs : f n with
    | false => rfl
    | true =>
      have hp:=hpos 1 (by decide) (by omega)
      have hz : subtractions f n 1=0 := by simp [subtractions,cN,hs]
      omega
  have h0 : p[0]?=some false := by
    change (seg f n K)[0]?=some false
    rw [seg_get f n K 0 hK,Nat.add_zero,hfS]
  have hA : ones p=(a : Int) := ones_seg_eq_count f n K
  have hQ8 : cross p=8 := by rw [hQ,show s=2 by omega]; decide
  have hShape:=four_neutral_shape p h4 (by omega) hQ8 h0
  have hEnd : cN (EndN f 0) n K=0 := by
    apply cN_zero_of
    intro t hnt ht he'
    rcases Recaman.SmallReverseSupplyCount.original_end_source f n t w hnt hpre he' with ho|hl
    · let x:=seg f n (t-n)
      let z:=seg f (t+1) (n+K-(t+1))
      have hsplit : seg f n K=x++[true]++z := split_at_addition f n K t hnt ht he'.1
      have hsf:=hsc
      change cntF (seg f n K)=s at hsf
      rw [hsplit,cntF_append,cntF_append,show cntF [true]=0 by decide,Nat.add_zero] at hsf
      have hx:=Recaman.LowCrossOldClocks.old_source_small_S w x z hw (by omega) (by omega) ho
      omega
    · have hAstep : additions f n (t-n+1)=additions f n (t-n)+1 :=
        cN_succ_pos _ n (t-n) (by rw [show n+(t-n)=t by omega]; exact he'.1)
      have hAl : additions f n (t-n+1)≤a :=
        count_prefix_le (fun t=>f t=true) n (t-n+1) K (by omega)
      have hOne : ones (seg f n (t-n))=(additions f n (t-n) : Int) :=
        ones_seg_eq_count f n (t-n)
      obtain ⟨v,hv⟩:=local_source_three_prior_A _ (by omega) hl
      rw [hv,ones_append,show ones [false,true,true]=2 by decide] at hOne
      have hv0:=(ones_bounds v).1
      omega
  have hspl : a=cN (EndN f 0) n K+free f n K := additions_split f n K
  exact ⟨hK4,hShape,by omega⟩

end Recaman.RankTwoEqualClock
