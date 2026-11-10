import Recaman.OldReturnNearFloorCount

namespace Recaman.OldSupplyDowncrossBudget

open Recaman.OldReturnNearFloorCount Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction

private theorem downcross_between (f : Nat → Bool) (s : Nat) (H : Int)
    (hs : H-1≤Fw f s) :
    ∀ K, Fw f (s+K)≤H-2 →
      ∃ t, s≤t ∧ t<s+K ∧ f t=false ∧ Fw f t=H-1 := by
  intro K
  induction K with
  | zero =>
    intro he
    rw [Nat.add_zero] at he
    omega
  | succ k ih =>
    intro he
    by_cases hp : Fw f (s+k)≤H-2
    · obtain ⟨t,ht,htk,hS,hH⟩ := ih hp
      exact ⟨t,ht,by omega,hS,hH⟩
    · rcases fw_cases f (s+k) with ⟨h,_⟩ | ⟨h,hS⟩
      · rw [show s+k+1=s+(k+1) by omega] at h
        omega
      · rw [show s+k+1=s+(k+1) by omega] at h
        exact ⟨s+k,by omega,by omega,hS,by omega⟩

/-- At any one height, each actual subtraction from one below that height
can pay for at most two additional old-supplied positions in the bound. -/
theorem old_supplies_le_downcross_budget (f : Nat → Bool) (n a s K : Nat) (H : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hns : n≤s) :
    cN (fun t => Fw f t=H ∧ f t=true ∧ ∃ u, u<n ∧ Win f u (t-u)) s K≤
      2+2*cN (fun t => f t=false ∧ Fw f t=H-1) s K := by
  let P := fun t => Fw f t=H ∧ f t=true ∧ ∃ u, u<n ∧ Win f u (t-u)
  let Q := fun t => f t=false ∧ Fw f t=H-1
  change cN P s K≤2+2*cN Q s K
  induction K using Nat.strongRecOn generalizing s with
  | ind K ih =>
    by_cases hc : ∃ t, s≤t ∧ t<s+K ∧ Q t
    · obtain ⟨t,ht,htK,hq⟩ := hc
      let d := t-s
      let r := K-d-1
      have hdt : s+d=t := by dsimp [d]; omega
      have hlen : d+(1+r)=K := by dsimp [r,d]; omega
      have hpn : ¬ P t := by
        intro hp
        have hs := hp.2.1
        rw [hq.1] at hs
        cases hs
      have hP0 : cN P t 1=0 := cN_succ_neg P t 0 (by simpa only [Nat.add_zero] using hpn)
      have hQ1 : cN Q t 1=1 := cN_succ_pos Q t 0 (by simpa only [Nat.add_zero] using hq)
      have hP := cN_add P s d (1+r)
      have hQ := cN_add Q s d (1+r)
      rw [hlen,hdt,cN_add P t 1 r,hP0,Nat.zero_add] at hP
      rw [hlen,hdt,cN_add Q t 1 r,hQ1] at hQ
      have h1 := ih d (by dsimp [d]; omega) s hns
      have h2 := ih r (by dsimp [r]; omega) (t+1) (by omega)
      omega
    · suffices h : cN P s K≤2 by omega
      apply count_le_two_of_no_ordered_triple
      intro b c d hsb hbc hcd hd hb hcp hdp
      obtain ⟨i,hib,hid,hlo⟩ := three_old_need_dip f n a b c d H hw hpre
        (by omega) hbc hcd hb hcp hdp
      have hlo' : Fw f (b+(i-b))≤H-2 := by
        rwa [Nat.add_sub_cancel' hib]
      obtain ⟨j,hbj,hj,hS,hH⟩ := downcross_between f b H (by have := hb.1; omega) (i-b) hlo'
      exact (hc ⟨j,by omega,by omega,hS,hH⟩).elim

end Recaman.OldSupplyDowncrossBudget
