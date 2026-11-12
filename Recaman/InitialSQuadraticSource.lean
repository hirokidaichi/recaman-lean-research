import Recaman.InitialSLowTargetTransport

namespace Recaman.InitialSQuadraticSource

open Recaman.InitialSLowTargetTransport Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality

/-- Every original source in an initial S prefix is determined by the
actual target height. A single explicit quadratic area test constructs
the old source in the reverse direction; local sources remain original. -/
theorem initial_S_source_quadratic_iff (f : Nat → Bool) (h q : Nat)
    (hS : ∀ i, i<h → f i=false) :
    let M := Fw f (h+q)-Fw f h
    EndN f 0 (h+q) ↔ EndN f h (h+q) ∨
      (f (h+q)=true ∧ 2≤M ∧ M≤(h : Int)+1 ∧
        2*Ar f h q=2*(q : Int)*(M-1)+M*(M-1)) := by
  dsimp only
  let M := Fw f (h+q)-Fw f h
  change EndN f 0 (h+q) ↔ EndN f h (h+q) ∨
    (f (h+q)=true ∧ 2≤M ∧ M≤(h : Int)+1 ∧
      2*Ar f h q=2*(q : Int)*(M-1)+M*(M-1))
  constructor
  · rintro ⟨hA,t,k,_,htk,hWin⟩
    by_cases ht : h≤t
    · exact Or.inl ⟨hA,t,k,ht,htk,hWin⟩
    · have hStep := fw_false_run f t (h-t) (fun i _ hi => hS i (by omega))
      rw [show t+(h-t)=h by omega] at hStep
      have hRise := hWin.2.1
      rw [htk] at hRise
      have hM : M=((h-t : Nat) : Int)+1 := by dsimp [M]; omega
      have hAr : Ar f t (h+q-t)=0 := by
        rw [show h+q-t=k by omega]
        exact hWin.2.2
      have hQuad : 2*Ar f t (h-t)= -((h-t : Nat) : Int)*(((h-t : Nat) : Int)+1) := by
        rw [Ar_areaW,seg_false f t (h-t) (fun i _ hi => hS i (by omega))]
        exact twice_area_replicate_S (h-t)
      have hSplit := area_split_at f t h (h+q) (by omega) (by omega)
      rw [hAr,show h+q-h=q by omega,
        show Fw f h-Fw f t= -((h-t : Nat) : Int) by omega] at hSplit
      refine Or.inr ⟨hA,by omega,by omega,?_⟩
      rw [hM]
      grind only
  · rintro (hLocal | ⟨hA,hM2,hMh,hPoly⟩)
    · exact end_mono f 0 h (h+q) (Nat.zero_le _) hLocal
    · let d := (M-1).toNat
      have hd : (d : Int)=M-1 := by
        dsimp [d]
        exact Int.toNat_of_nonneg (by omega)
      have hdp : 0<d := by omega
      have hdh : d≤h := by omega
      let t := h-d
      have hth : t<h := by dsimp [t]; omega
      have htd : h-t=d := by dsimp [t]; omega
      have hStep := fw_false_run f t (h-t) (fun i _ hi => hS i (by omega))
      rw [show t+(h-t)=h by omega,htd] at hStep
      have hRise : Fw f (h+q)=Fw f t+1 := by dsimp [M] at hd; omega
      have hQuad : 2*Ar f t (h-t)= -(d : Int)*((d : Int)+1) := by
        rw [Ar_areaW,seg_false f t (h-t) (fun i _ hi => hS i (by omega)),htd]
        exact twice_area_replicate_S d
      have hSplit := area_split_at f t h (h+q) (by omega) (by omega)
      rw [show h+q-h=q by omega,
        show Fw f h-Fw f t= -(d : Int) by omega] at hSplit
      have hMd : M=(d : Int)+1 := by omega
      rw [hMd] at hPoly
      have hAr : Ar f t (h+q-t)=0 := by grind only
      refine ⟨hA,t,h+q-t,by omega,by omega,by omega,?_,hAr⟩
      rw [show t+(h+q-t)=h+q by omega]
      exact hRise

end Recaman.InitialSQuadraticSource
