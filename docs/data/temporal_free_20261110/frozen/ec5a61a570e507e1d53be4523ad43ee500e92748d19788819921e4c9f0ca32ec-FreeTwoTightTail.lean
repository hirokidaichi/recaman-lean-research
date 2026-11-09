import Recaman.ForwardSourceFreeTwoFactor

namespace Recaman.FreeTwoTightTail

open Recaman.AdditionRankSlack Recaman.RunSupplyKeys
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem additions_le_at_prefix (f : Nat → Bool) (n k K : Nat) (hk : k≤K) :
    additions f n k≤additions f n K := by
  have h:=cN_add (fun x=>f x=true) n k (K-k)
  rw [show k+(K-k)=K by omega] at h
  unfold additions
  omega

/-- The free-two extremal key pushes every addition into the first nine
positions, independent of the old prefix's size or the future length. -/
theorem tight_free_two_tail (f : Nat → Bool) (n : Nat)
    (hp : ∀ k, 0<k → k≤11 → cN (EndN f 0) n k+1≤subtractions f n k)
    (hf : free f n 11≤2) (ha : additions f n 11=5) (hk : runKey (seg f n 11)=4) :
    f (n+8)=true ∧ f (n+9)=false ∧ f (n+10)=false := by
  have ht : additions f n 11+subtractions f n 11=11 := (cN_walk f n 11).2
  have hs : subtractions f n 11=6 := by omega
  have hsl : rankSlack f n 2 11=0 := by
    unfold rankSlack
    rw [ha,hs,hk]
    decide
  have hlate (t : Nat) (ht0 : 9≤t) (ht1 : t<11) : f (n+t)=false := by
    cases h : f (n+t) with
    | false => rfl
    | true =>
      have he:=rank_floor_of_tight f n 2 11 t hp hf hsl ht1 h
      have hm:=additions_le_at_prefix f n (t+1) 11 (by omega)
      have hs0 : subtractions f n (t+1)=subtractions f n t :=
        cN_succ_neg _ n t (by rw [h]; decide)
      have ht0' : additions f n (t+1)+subtractions f n (t+1)=t+1 := (cN_walk f n (t+1)).2
      omega
  have h9:=hlate 9 (by decide) (by decide)
  have h10:=hlate 10 (by decide) (by decide)
  have hA9 : additions f n 9=5 := by
    have h1 : additions f n 10=additions f n 9 :=
      cN_succ_neg _ n 9 (by rw [h9]; decide)
    have h2 : additions f n 11=additions f n 10 :=
      cN_succ_neg _ n 10 (by rw [h10]; decide)
    omega
  have hA8 : additions f n 8≤4 := by
    have hsum : additions f n 8+subtractions f n 8=8 := (cN_walk f n 8).2
    have hsp:=additions_split f n 8
    have hf8:=free_prefix_mono f n 8 11 (by decide)
    have hp8:=hp 8 (by decide) (by decide)
    omega
  refine ⟨?_,h9,h10⟩
  cases h : f (n+8) with
  | true => rfl
  | false =>
    have h1 : additions f n 9=additions f n 8 := cN_succ_neg _ n 8 (by rw [h]; decide)
    omega

end Recaman.FreeTwoTightTail
