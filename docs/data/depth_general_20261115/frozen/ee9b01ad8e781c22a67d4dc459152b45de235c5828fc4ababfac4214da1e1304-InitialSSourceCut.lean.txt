import Recaman.InitialSQuadraticSource

namespace Recaman.InitialSSourceCut

open Recaman.InitialSQuadraticSource Recaman.InitialSLowTargetTransport
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.AdditionRankSlack Recaman.CapacityEqualityInduction

/-- Exact original sources surviving an arbitrary initial-S cut.
The quadratic is evaluated on the unchanged original future. -/
theorem retained_source_iff (f : Nat → Bool) (h C q : Nat)
    (hS : ∀ i, i<h → f i=false) (hC : C≤h) :
    let M := Fw f (h+q)-Fw f h
    EndN f (h-C) (h+q) ↔ EndN f h (h+q) ∨
      (f (h+q)=true ∧ 2≤M ∧ M≤(C : Int)+1 ∧
        2*Ar f h q=2*(q : Int)*(M-1)+M*(M-1)) := by
  dsimp only
  constructor
  · intro he
    by_cases hl : EndN f h (h+q)
    · exact Or.inl hl
    · have hFull := end_mono f 0 (h-C) (h+q) (Nat.zero_le _) he
      have hQuad := (initial_S_source_quadratic_iff f h q hS).mp hFull
      rcases hQuad with hc|⟨hA,hM2,_,hPoly⟩
      · exact (hl hc).elim
      · obtain ⟨_,t,k,ht,htk,hWin⟩ := he
        have hth : t<h := by
          by_cases hlt : h≤t
          · exact (hl ⟨hA,t,k,hlt,htk,hWin⟩).elim
          · omega
        have hs := fw_false_run f t (h-t) (fun i _ hi => hS i (by omega))
        rw [show t+(h-t)=h by omega] at hs
        have hr := hWin.2.1
        rw [htk] at hr
        exact Or.inr ⟨hA,hM2,by omega,hPoly⟩
  · rintro (hl|⟨hA,hM2,hMC,hPoly⟩)
    · exact end_mono f (h-C) h (h+q) (by omega) hl
    · have hFull := (initial_S_source_quadratic_iff f h q hS).mpr
        (Or.inr ⟨hA,hM2,by omega,hPoly⟩)
      have hSd : ∀ i, i<h-C → f i=false := fun i hi => hS i (by omega)
      have hh := fw_false_run f 0 h (fun i _ hi => hS i (by omega))
      have hd := fw_false_run f 0 (h-C) (fun i _ hi => hSd i (by omega))
      simp only [Nat.zero_add,Fw] at hh hd
      have hTarget : Fw f (h+q)≤Fw f (h-C)+1 := by omega
      exact (initial_S_low_target_source_iff f (h-C) (h+q) hSd hTarget).mp hFull

/-- An explicit source-cost marker, used only in conclusions/counts.
It is not an unproved supply-family hypothesis. -/
def cutLoss (f : Nat → Bool) (h C b : Nat) : Prop :=
  let M := Fw f b-Fw f h
  f b=true ∧ (C : Int)+2≤M ∧ M≤(h : Int)+1 ∧
    2*Ar f h (b-h)=2*((b-h : Nat) : Int)*(M-1)+M*(M-1) ∧ ¬EndN f h b

theorem lost_source_iff (f : Nat → Bool) (h C q : Nat)
    (hS : ∀ i, i<h → f i=false) (hC : C≤h) :
    (EndN f 0 (h+q) ∧ ¬EndN f (h-C) (h+q)) ↔ cutLoss f h C (h+q) := by
  simp only [cutLoss,Nat.add_sub_cancel_left]
  constructor
  · rintro ⟨he,hn⟩
    have hl : ¬EndN f h (h+q) := fun hh =>
      hn (end_mono f (h-C) h (h+q) (by omega) hh)
    rcases (initial_S_source_quadratic_iff f h q hS).mp he with hc|⟨ha,hm,hh,hp⟩
    · exact (hl hc).elim
    · have hBig : (C : Int)+2≤Fw f (h+q)-Fw f h := by
        by_cases hs : Fw f (h+q)-Fw f h≤(C : Int)+1
        · exact (hn ((retained_source_iff f h C q hS hC).mpr
            (Or.inr ⟨ha,hm,hs,hp⟩))).elim
        · omega
      exact ⟨ha,hBig,hh,hp,hl⟩
  · rintro ⟨ha,hm,hh,hp,hl⟩
    have he := (initial_S_source_quadratic_iff f h q hS).mpr
      (Or.inr ⟨ha,by omega,hh,hp⟩)
    refine ⟨he,?_⟩
    intro hc
    rcases (retained_source_iff f h C q hS hC).mp hc with hc|⟨_,_,hb,_⟩
    · exact hl hc
    · omega

/-- Actual retained-tail supply and free cost at the original clocks.
All lost suppliers are internally identified by the original quadratic
and absence of an original local alternative, with no depth bound. -/
theorem cut_tail_count_cost (f : Nat → Bool) (h C K : Nat)
    (hS : ∀ i, i<h → f i=false) (hC : C≤h) :
    cN (EndN f 0) h K=cN (EndN f (h-C)) h K+cN (cutLoss f h C) h K ∧
    cN (fun i => f i=true ∧ ¬EndN f (h-C) i) h K=
      free f h K+cN (cutLoss f h C) h K := by
  have hSub (i : Nat) (he : EndN f (h-C) i) : EndN f 0 i :=
    end_mono f 0 (h-C) i (Nat.zero_le _) he
  have he := cN_split (EndN f 0) (EndN f (h-C)) h K
  have hKeep : cN (fun i => EndN f 0 i ∧ EndN f (h-C) i) h K=
      cN (EndN f (h-C)) h K := by
    apply cN_congr
    intro i _ _
    exact ⟨fun hh => hh.2,fun hh => ⟨hSub i hh,hh⟩⟩
  have hLost : cN (fun i => EndN f 0 i ∧ ¬EndN f (h-C) i) h K=
      cN (cutLoss f h C) h K := by
    apply cN_congr
    intro i hi _
    have hl := lost_source_iff f h C (i-h) hS hC
    simpa only [show h+(i-h)=i by omega] using hl
  rw [hKeep,hLost] at he
  have hA := cN_split (fun i => f i=true) (EndN f (h-C)) h K
  have hAKeep : cN (fun i => f i=true ∧ EndN f (h-C) i) h K=
      cN (EndN f (h-C)) h K := by
    apply cN_congr
    intro i _ _
    exact ⟨fun hh => hh.2,fun hh => ⟨hh.1,hh⟩⟩
  rw [hAKeep] at hA
  have hOld := additions_split f h K
  unfold additions at hOld
  exact ⟨he,by omega⟩

end Recaman.InitialSSourceCut
