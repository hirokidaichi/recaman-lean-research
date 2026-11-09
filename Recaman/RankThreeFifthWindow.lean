import Recaman.InitialRankBonus

namespace Recaman.RankThreeFifthWindow

open Recaman.AdditionRankSlack Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.RunSupplyKeys

private theorem addition_hit (f : Nat → Bool) (n q K : Nat)
    (hq : 0<q) (ha : q≤additions f n K) :
    ∃ t, t<K ∧ f (n+t)=true ∧ additions f n t=q-1 ∧ additions f n (t+1)=q := by
  induction K with
  | zero => simp [additions,cN] at ha; omega
  | succ K ih =>
    by_cases he : q≤additions f n K
    · obtain ⟨t,ht,hA,hb,hh⟩:=ih he
      exact ⟨t,by omega,hA,hb,hh⟩
    · cases hs : f (n+K) with
      | false =>
        have h : additions f n (K+1)=additions f n K := cN_succ_neg _ n K (by rw [hs]; decide)
        omega
      | true =>
        have h : additions f n (K+1)=additions f n K+1 := cN_succ_pos _ n K hs
        exact ⟨K,by omega,hs,by omega,by omega⟩

/-- A rank-three history with at most two surplus S-before-A pairs has
its fifth addition in a window of length eight or nine. -/
theorem fifth_window_at_small_slack (f : Nat → Bool) (n K : Nat)
    (hp : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hf : free f n K≤3) (ha : 5≤additions f n K) (hsl : rankSlack f n 3 K≤8) :
    ∃ k, k≤K ∧ additions f n k=5 ∧ f (n+(k-1))=true ∧
      ((k=8 ∧ 2≤runKey (seg f n k)) ∨ (k=9 ∧ 8≤runKey (seg f n k))) := by
  obtain ⟨t,ht,hat,hbefore,hafter⟩:=addition_hit f n 5 K (by decide) ha
  have hb : additions f n t=4 := hbefore
  have hP (q : Nat) (hq : 0<q) (hqt : q≤t) := hp q hq (by omega)
  have hf' : free f n t≤3 := Nat.le_trans (free_prefix_mono f n t K (by omega)) hf
  have hbonus:=Recaman.InitialRankBonus.initial_two_subtraction_bonus f n 3 t hP hf'
  rw [hb] at hbonus
  have hb4 : 4≤rankSlack f n 3 t := by simpa using hbonus
  have hm:=rankSlack_mono f n 3 K hp hf (t+1) K (by omega) (by omega)
  have h8 : rankSlack f n 3 (t+1)≤8 := Int.le_trans hm hsl
  have hsc : subtractions f n (t+1)=subtractions f n t := cN_succ_neg _ n t (by rw [hat]; decide)
  have hstep:=rankSlack_step_A f n 3 t hat
  rw [hafter,← hsc] at hstep
  have hSmax : subtractions f n (t+1)≤4 := by omega
  have hSmin : 3≤subtractions f n (t+1) := by
    have hsp:=additions_split f n (t+1)
    have hfp:=free_prefix_mono f n (t+1) K (by omega)
    have hpp:=hp (t+1) (by omega) (by omega)
    omega
  have htally : additions f n (t+1)+subtractions f n (t+1)=t+1 := (cN_walk f n (t+1)).2
  refine ⟨t+1,by omega,hafter,by simpa using hat,?_⟩
  unfold rankSlack at h8
  rw [hafter] at h8
  have hc : rankCost 3 5=32 := by decide
  rw [hc] at h8
  by_cases h3 : subtractions f n (t+1)=3
  · rw [h3] at h8
    left
    exact ⟨by omega,by omega⟩
  · have h4 : subtractions f n (t+1)=4 := by omega
    rw [h4] at h8
    right
    exact ⟨by omega,by omega⟩

end Recaman.RankThreeFifthWindow
