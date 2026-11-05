import Recaman.SingleWindowEquality

namespace Recaman.ClockCountSaturation

open Recaman.SingleWindowEquality

theorem count_le_length (P : Nat → Prop) (b : Nat) : ∀ K, cN P b K≤K
  | 0 => Nat.le_refl 0
  | K+1 => by
    have hp:=cN_succ_le P b K
    have hl:=count_le_length P b K
    omega

theorem full_count_at (P : Nat → Prop) (b : Nat) :
    ∀ K, K≤cN P b K → ∀ i, i<K → P (b+i)
  | 0,_,i,hi => by omega
  | K+1,h,i,hi => by
    by_cases he : P (b+K)
    · rw [cN_succ_pos P b K he] at h
      by_cases hk : i=K
      · simpa only [hk] using he
      · exact full_count_at P b K (by omega) i (by omega)
    · rw [cN_succ_neg P b K he] at h
      have hp:=count_le_length P b K
      omega

private theorem count_single (P : Nat → Prop) (b x : Nat) :
    ∀ K, (∀ i, b≤i → i<b+K → P i → i=x) → cN P b K≤1
  | 0,_ => by change 0≤1; omega
  | K+1,h => by
    by_cases he : P (b+K)
    · rw [cN_succ_pos P b K he]
      have hlast:=h (b+K) (by omega) (by omega) he
      have hzero : cN P b K=0 := by
        apply cN_zero_of
        intro i hi hk hp
        have hix:=h i hi (by omega) hp
        omega
      omega
    · rw [cN_succ_neg P b K he]
      exact count_single P b x K (fun i hi hk hp=>h i hi (by omega) hp)

/-- If the only clock after the early band is clock2, saturation
requires that clock to lie outside the band and every early clock to pay. -/
theorem saturated_pair_clock (P : Nat → Prop) (b T D : Nat) (hD : D≤T)
    (hs : ∀ i, i<T → P (b+i) → i<D ∨ i=2)
    (hfull : D+1≤cN P b T) :
    D≤2 ∧ 2<T ∧ ∀ i, i<D → P (b+i) := by
  have hsplit:=cN_add P b D (T-D)
  rw [show D+(T-D)=T by omega] at hsplit
  have he := count_le_length P b D
  have hl := count_single P (b+D) (b+2) (T-D) (by
    intro x hx hxt hp
    have he := hs (x-b) (by omega) (by rwa [Nat.add_sub_cancel' (show b≤x by omega)])
    omega)
  have hlate : 1≤cN P (b+D) (T-D) := by omega
  have hwindow : D≤2 ∧ 2<T := by
    by_cases hz : D≤2 ∧ 2<T
    · exact hz
    · have hzero : cN P (b+D) (T-D)=0 := by
        apply cN_zero_of
        intro x hx hxt hp
        have he := hs (x-b) (by omega) (by rwa [Nat.add_sub_cancel' (show b≤x by omega)])
        apply hz
        omega
      omega
  exact ⟨hwindow.1,hwindow.2,full_count_at P b D (by omega)⟩

end Recaman.ClockCountSaturation
