import Recaman.ClockCountSaturation
import Recaman.ThirdSeparatorClock

namespace Recaman.GapFourClockReduction

open Recaman.SingleWindowEquality Recaman.RunSupplyBudget
open Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock Recaman.ClockCountSaturation

/-- With every final-ray clock supplied at gap4, the second-prefix
cost is nine and a third-S source pays the last clock. Clock2 needs
a separate case because it can be supplied by the terminal pair. -/
theorem gap_four_clock_reduction (f : Nat → Bool) (b T M L s U v : Nat)
    (hv : 1≤v) (hT : 1≤T) (hM : M≤6) (hW : M+L≤9)
    (hU5 : M+L=9 → U≤5)
    (hfull : cN (EndN f 0) b T=T)
    (hcount : cN (EndN f 0) b T≤max (T-4) (M+L+T-9)+1)
    (hpair : ∀ i, i<T → max (T-4) (M+L+T-9)≤i → EndN f 0 (b+i) → i=2)
    (hthird : ∀ i, i<T → max (T-4) (M+L-1+T-9)≤i → EndN f 0 (b+i) →
      sourceAt false s (List.replicate U true++List.replicate v false) i ∨ i=2)
    (htail : ∀ i k, k<L → i<T → max (T-4) (M+(L-k-1)+T-9)≤i → EndN f 0 (b+i) →
      sourceAt true k (List.replicate s false++(List.replicate U true++List.replicate v false)) i ∨
      sourceAt false s (List.replicate U true++List.replicate v false) i ∨ i=2) :
    M+L=9 ∧ ((T=1 ∧ U=4 ∧ v=1 ∧ 2≤s) ∨ (4≤T ∧ 2*T-4≤v)) := by
  let W:=M+L
  let D:=max (T-4) (W+T-9)
  change T≤D+1 at hcount
  have hall := full_count_at (EndN f 0) b T (by omega)
  have hW9 : W=9 := by
    by_cases hW8 : W≤8
    · exfalso
      by_cases hW7 : W≤7
      · by_cases hT2 : 2≤T
        · have hD : D≤T-2 := by
            dsimp [D]
            exact Nat.max_le.mpr ⟨by omega,by omega⟩
          omega
        · have hD0 : D=0 := by
            dsimp [D]
            rw [Nat.sub_eq_zero_of_le (show T≤4 by omega),Nat.sub_eq_zero_of_le (show W+T≤9 by omega),
              Nat.max_self]
          have h := hpair 0 (by omega) (by change D≤0; omega) (hall 0 (by omega))
          omega
      · have hD : D=T-1 := by
          dsimp [D]
          rw [Nat.max_eq_right (by omega)]
          omega
        obtain ⟨hD2,hT3,_⟩:=saturated_pair_clock (EndN f 0) b T D (by omega)
          (fun i hi he=>by
            by_cases hh : i<D
            · exact Or.inl hh
            · exact Or.inr (hpair i hi (by change D≤i; omega) he)) (by omega)
        have hsrc:=hthird 1 (by omega) (Nat.max_le.mpr ⟨by omega,by omega⟩) (hall 1 (by omega))
        rcases hsrc with hs|h2
        · exact (third_separator_clock s U v 1 hv hs).1 rfl
        · omega
    · dsimp [W] at *
      omega
  have hU := hU5 hW9
  refine ⟨hW9,?_⟩
  have hTne3 : T≠3 := by
    intro h3
    have hL : 3≤L := by dsimp [W] at hW9; omega
    have hsrc1:=htail 1 1 (by omega) (by omega) (Nat.max_le.mpr ⟨by omega,by dsimp [W] at hW9; omega⟩)
      (hall 1 (by omega))
    have h1 : sourceAt true 1 (List.replicate s false++(List.replicate U true++List.replicate v false)) 1 := by
      rcases hsrc1 with hs|hs|he
      · exact hs
      · exact False.elim ((third_separator_clock s U v 1 hv hs).1 rfl)
      · omega
    have hsrc0:=htail 0 2 (by omega) (by omega) (Nat.max_le.mpr ⟨by omega,by dsimp [W] at hW9; omega⟩)
      (hall 0 (by omega))
    have h0 : sourceAt false s (List.replicate U true++List.replicate v false) 0 := by
      rcases hsrc0 with hs|hs|he
      · have h:=same_family_clock true 2 1 0 1 _ hs h1
        omega
      · exact hs
      · omega
    have hUeq:=(third_separator_clock s U v 0 hv h0).2.2 rfl
    have hv1 : v=1 := by omega
    have hU4 : U=4 := by omega
    rw [hv1,hU4] at h1
    exact second_A_one_unit_tail_absent s 1 h1
  let i:=T-1
  have hi : i<T := by dsimp [i]; omega
  have hsrc := hthird i hi (Nat.max_le.mpr ⟨by dsimp [i]; omega,by dsimp [i,W] at *; omega⟩) (hall i hi)
  have hthirdOnly : sourceAt false s (List.replicate U true++List.replicate v false) i := by
    rcases hsrc with hs|h2
    · exact hs
    · dsimp [i] at h2
      omega
  have ht := third_separator_clock s U v i hv hthirdOnly
  by_cases hTl : T≤3
  · have hT1 : T=1 := by have hi1:=ht.1; dsimp [i] at hi1; omega
    obtain ⟨hsv,hUeq⟩:=ht.2.2 (by dsimp [i]; omega)
    exact Or.inl ⟨hT1,by omega,by omega,by omega⟩
  · have hbound:=ht.2.1
    dsimp [i] at hbound
    exact Or.inr ⟨by omega,by omega⟩

end Recaman.GapFourClockReduction
