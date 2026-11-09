import Recaman.MixedPrefixClockSquare

namespace Recaman.AdditionRankSlack

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

noncomputable def additions (f : Nat → Bool) (n k : Nat) : Nat :=
  cN (fun x => f x = true) n k

noncomputable def subtractions (f : Nat → Bool) (n k : Nat) : Nat :=
  cN (fun x => f x = false) n k

noncomputable def free (f : Nat → Bool) (n k : Nat) : Nat :=
  cN (fun x => f x = true ∧ ¬EndN f 0 x) n k

/-- Four times the sum of the subtraction floors at the first `a` addition ranks. -/
def rankCost (r a : Nat) : Int :=
  4 * (a : Int) + 2 * ((a-r : Nat) : Int) * (((a-r : Nat) : Int) + 1)

noncomputable def rankSlack (f : Nat → Bool) (n r k : Nat) : Int :=
  4 * (additions f n k : Int) * (subtractions f n k : Int) -
    2 * (subtractions f n k : Int)^2 - runKey (seg f n k) - rankCost r (additions f n k)

private theorem rankCost_step (r a : Nat) :
    rankCost r (a+1) = rankCost r a + 4*(1+(((a+1-r : Nat) : Int))) := by
  unfold rankCost
  by_cases h : a<r
  · rw [show a-r=0 by omega, show a+1-r=0 by omega]
    omega
  · rw [show a+1-r=a-r+1 by omega]
    simp only [Int.natCast_add,Int.natCast_one]
    grind only

private theorem segKey_step_A (f : Nat → Bool) (n k : Nat) (ha : f (n+k)=true) :
    runKey (seg f n (k+1))=runKey (seg f n k) := by
  rw [seg_succ,ha]
  exact runKey_append_A (seg f n k) 1

private theorem segKey_step_S (f : Nat → Bool) (n k : Nat) (hs : f (n+k)=false) :
    runKey (seg f n (k+1))=runKey (seg f n k)+
      4*((additions f n k : Int)-(subtractions f n k : Int))-2 := by
  have hm:=seg_mass f n k
  have hw:=(cN_walk f n k).1
  have he : mass (seg f n k)=(additions f n k : Int)-(subtractions f n k : Int) := by
    unfold additions subtractions
    omega
  rw [seg_succ,hs]
  have hk:=runKey_append_S (seg f n k) 1
  rw [he] at hk
  simpa only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
    Int.natCast_one,Int.mul_one,Int.one_pow] using hk

/-- At an addition the slack charges the subtraction count above its rank floor. -/
theorem rankSlack_step_A (f : Nat → Bool) (n r k : Nat) (ha : f (n+k)=true) :
    rankSlack f n r (k+1)=rankSlack f n r k +
      4*((subtractions f n k : Int)-1-(((additions f n (k+1)-r : Nat) : Int))) := by
  have hac : additions f n (k+1)=additions f n k+1 := cN_succ_pos _ n k ha
  have hsc : subtractions f n (k+1)=subtractions f n k :=
    cN_succ_neg _ n k (by rw [ha]; decide)
  unfold rankSlack
  rw [hac,hsc,segKey_step_A f n k ha,rankCost_step]
  simp only [Int.natCast_add,Int.natCast_one]
  grind only

/-- A subtraction changes the key and the rectangle by the same amount. -/
theorem rankSlack_step_S (f : Nat → Bool) (n r k : Nat) (hs : f (n+k)=false) :
    rankSlack f n r (k+1)=rankSlack f n r k := by
  have hac : additions f n (k+1)=additions f n k :=
    cN_succ_neg _ n k (by rw [hs]; decide)
  have hsc : subtractions f n (k+1)=subtractions f n k+1 := cN_succ_pos _ n k hs
  unfold rankSlack
  rw [hac,hsc,segKey_step_S f n k hs]
  simp only [Int.natCast_add,Int.natCast_one]
  grind only

theorem free_prefix_mono (f : Nat → Bool) (n k K : Nat) (hle : k≤K) :
    free f n k≤free f n K := by
  have h:=cN_add (fun x=>f x=true ∧ ¬EndN f 0 x) n k (K-k)
  rw [show k+(K-k)=K by omega] at h
  unfold free
  omega

theorem additions_split (f : Nat → Bool) (n k : Nat) :
    additions f n k=cN (EndN f 0) n k+free f n k := by
  have he:=cN_congr (P := fun x=>f x=true ∧ EndN f 0 x) (Q := EndN f 0) (s := n) k
    (fun x _ _ => ⟨fun h=>h.2,fun h=>⟨h.1,h⟩⟩)
  unfold additions free
  rw [cN_split (Q := EndN f 0),he]

/-- The original free budget bounds every prefix, hence the rank slack is
nondecreasing on the whole interval. No equality about supplied/free pairs is assumed. -/
theorem rankSlack_mono (f : Nat → Bool) (n r K : Nat)
    (hpos : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hfree : free f n K≤r) :
    ∀ k l, k≤l → l≤K → rankSlack f n r k≤rankSlack f n r l := by
  have hstep (t : Nat) (ht : t<K) : rankSlack f n r t≤rankSlack f n r (t+1) := by
    cases hf : f (n+t) with
    | false =>
      rw [rankSlack_step_S f n r t hf]
      exact Int.le_refl _
    | true =>
      have hs : subtractions f n (t+1)=subtractions f n t :=
        cN_succ_neg _ n t (by rw [hf]; decide)
      have hp:=hpos (t+1) (by omega) (by omega)
      have he:=additions_split f n (t+1)
      have hb:=free_prefix_mono f n (t+1) K (by omega)
      rw [hs] at hp
      rw [rankSlack_step_A f n r t hf]
      omega
  intro k l
  induction l with
  | zero =>
    intro hk _
    rw [show k=0 by omega]
    exact Int.le_refl _
  | succ l ih =>
    intro hk hl
    by_cases h : k=l+1
    · rw [h]
      exact Int.le_refl _
    · exact Int.le_trans (ih (by omega) (by omega)) (hstep l (by omega))

theorem rankSlack_zero (f : Nat → Bool) (n r : Nat) : rankSlack f n r 0=0 := by
  simp [rankSlack,rankCost,additions,subtractions,cN,seg,runKey,areaW,mass]

/-- At equality, every actual addition attains its subtraction floor. -/
theorem rank_floor_of_tight (f : Nat → Bool) (n r K t : Nat)
    (hpos : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hfree : free f n K≤r) (htight : rankSlack f n r K=0)
    (ht : t<K) (ha : f (n+t)=true) :
    subtractions f n t=1+(additions f n (t+1)-r) := by
  have hm:=rankSlack_mono f n r K hpos hfree
  have h0:=rankSlack_zero f n r
  have h1:=hm 0 t (by omega) (by omega)
  have h2:=hm (t+1) K (by omega) (by omega)
  rw [rankSlack_step_A f n r t ha] at h2
  have hp:=hpos (t+1) (by omega) (by omega)
  have hs : subtractions f n (t+1)=subtractions f n t :=
    cN_succ_neg _ n t (by rw [ha]; decide)
  have he:=additions_split f n (t+1)
  have hb:=free_prefix_mono f n (t+1) K (by omega)
  omega

end Recaman.AdditionRankSlack
