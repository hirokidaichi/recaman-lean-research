import Recaman.BlockSameMassSpan

namespace Recaman.PenultimateRunWindow

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem key_S (s : Nat) : runKey (List.replicate s false) = -2*(s : Int)^2 := by
  have h := runKey_prepend_S s []
  simpa [runKey,areaW,mass,cntF,Int.neg_mul] using h

/-- Exact square condition for a P2 window starting in an A run before
one more S/A run. Only its endpoint gap is separated; s is unbounded. -/
theorem ASAS_window_square (d s T j : Nat)
    (hm : mass (List.replicate d true++List.replicate s false++
      List.replicate T true++List.replicate j false)=1)
    (ha : areaW (List.replicate d true++List.replicate s false++
      List.replicate T true++List.replicate j false)=0) :
    (d : Int)^2=(T : Int)*((T : Int)-2*((j : Int)+1)) := by
  let v:=List.replicate d true++List.replicate s false++List.replicate T true
  have hmv : mass v=(j : Int)+1 := by
    simpa only [v,mass_append,mass_replicate_A,mass_rep_false] using (show mass v=(j : Int)+1 by
      change mass (v++List.replicate j false)=1 at hm
      rw [mass_append,mass_rep_false] at hm
      omega)
  have hmass : (d : Int)-(s : Int)+(T : Int)=(j : Int)+1 := by
    simpa only [v,mass_append,mass_replicate_A,mass_rep_false,Int.sub_eq_add_neg] using hmv
  have hkv : runKey v= -2*(s : Int)^2+4*(d : Int)*(s : Int) := by
    dsimp [v]
    rw [runKey_append_A,runKey_prepend_A,key_S,cntF_replicate_S]
  have hwhole : runKey (v++List.replicate j false)= -2 := by
    unfold runKey
    change mass (v++List.replicate j false)=1 at hm
    change areaW (v++List.replicate j false)=0 at ha
    rw [hm,ha]
    decide
  rw [runKey_append,hkv,key_S,cntF_replicate_S,hmv] at hwhole
  have hs : (s : Int)=(d : Int)+(T : Int)-(j : Int)-1 := by omega
  rw [hs] at hwhole
  grind

set_option maxRecDepth 10000 in
private theorem bounded_divisor_parity (R Y : Nat) (hR5 : 5≤R) (hR10 : R≤10)
    (hRY : R<Y) (hSum : R+Y≤20) :
    ((R : Int)^2 % (Y : Int)≠0) ∨ (((R : Int)^2 / (Y : Int)+(Y : Int))%2=1) := by
  have hc : (List.range 11).all (fun R => (List.range 21).all (fun Y =>
      decide (5≤R ∧ R≤10 ∧ R<Y ∧ R+Y≤20 →
        ((R : Int)^2 % (Y : Int)≠0) ∨ (((R : Int)^2 / (Y : Int)+(Y : Int))%2=1))))=true := by decide
  have h := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hc R
    (List.mem_range.mpr (by omega))) Y (List.mem_range.mpr (by omega)))
  exact h ⟨hR5,hR10,hRY,hSum⟩

private theorem small_square_not (d T j : Nat) (hd : 1≤d) (hA : d+T≤20)
    (hj : 4≤j) (hj9 : j≤9) :
    (d : Int)^2≠(T : Int)*((T : Int)-2*((j : Int)+1)) := by
  intro heq
  let R : Int:=(j : Int)+1
  have hdpos : 0<(d : Int)^2 := by
    have hh := Int.mul_pos (show 0<(d : Int) by omega) (show 0<(d : Int) by omega)
    have he : (d : Int)^2=(d : Int)*(d : Int) := by grind
    rw [he]
    exact hh
  have hT : 2*R<(T : Int) := by
    by_cases hh : 2*R<(T : Int)
    · exact hh
    · have hp := Int.mul_nonneg (show 0≤(T : Int) by omega) (show 0≤2*R-(T : Int) by omega)
      have hid : (T : Int)*(2*R-(T : Int))= -((T : Int)*((T : Int)-2*R)) := by grind
      rw [hid] at hp
      change (d : Int)^2=(T : Int)*((T : Int)-2*R) at heq
      omega
  let x : Int:=(T : Int)-R-(d : Int)
  let y : Int:=(T : Int)-R+(d : Int)
  have hypos : 0<y := by dsimp [y,R]; omega
  have hprod : x*y=R^2 := by dsimp [x,y,R]; grind
  have hmod : R^2%y=0 := by rw [←hprod]; exact Int.mul_emod_left x y
  have hdiv : R^2/y=x := by rw [←hprod]; exact Int.mul_ediv_cancel x (by omega)
  have hparity : (x+y)%2=0 := by
    have hh : x+y=((T : Int)-R)*2 := by dsimp [x,y]; omega
    rw [hh]
    exact Int.mul_emod_left _ _
  let Y:=T+d-(j+1)
  have hY : (Y : Int)=y := by dsimp [Y,y,R]; omega
  have hcheck := bounded_divisor_parity (j+1) Y (by omega) (by omega)
    (by
      have hh : R<y := by dsimp [y]; omega
      have hRcast : ((j+1 : Nat) : Int)=R := by simp [R]
      omega)
    (by dsimp [Y]; omega)
  have hR : ((j+1 : Nat) : Int)=R := by simp [R]
  rw [hY,hR] at hcheck
  rcases hcheck with hbad|hbad
  · exact hbad hmod
  · rw [hdiv,hparity] at hbad
    contradiction

/-- Under the actual three-run residual bounds this entire source shape
is excluded, without limiting the intervening S-run length. -/
theorem ASAS_no_small_window (d s T j : Nat) (hd : 1≤d) (hA : d+T≤20)
    (hj : 4≤j) (hj9 : j≤9) :
    ¬(mass (List.replicate d true++List.replicate s false++
        List.replicate T true++List.replicate j false)=1 ∧
      areaW (List.replicate d true++List.replicate s false++
        List.replicate T true++List.replicate j false)=0) := by
  rintro ⟨hm,ha⟩
  exact small_square_not d T j hd hA hj hj9 (ASAS_window_square d s T j hm ha)

/-- Literal actual-window adapter; arbitrary earlier history is retained.
Only a window with this start/run shape is ruled out. -/
theorem actual_ASAS_no_small_window (f : Nat → Bool) (start d s T j : Nat)
    (hword : seg f start (d+s+T+j)=List.replicate d true++List.replicate s false++
      List.replicate T true++List.replicate j false)
    (hd : 1≤d) (hA : d+T≤20) (hj : 4≤j) (hj9 : j≤9) :
    ¬Win f start (d+s+T+j) := by
  intro hw
  apply ASAS_no_small_window d s T j hd hA hj hj9
  constructor
  · rw [←hword,seg_mass]
    have hh := hw.2.1
    omega
  · rw [←hword,←Ar_areaW]
    exact hw.2.2

/-- These are window controls outside the declared assumptions, not C1
counterexamples. They prevent erasing the A budget or the gap lower bound. -/
theorem outside_assumption_controls :
    mass (List.replicate 3 true++List.replicate 8 false++
      List.replicate 9 true++List.replicate 3 false)=1 ∧
    areaW (List.replicate 3 true++List.replicate 8 false++
      List.replicate 9 true++List.replicate 3 false)=0 ∧
    mass (List.replicate 8 true++List.replicate 18 false++
      List.replicate 16 true++List.replicate 5 false)=1 ∧
    areaW (List.replicate 8 true++List.replicate 18 false++
      List.replicate 16 true++List.replicate 5 false)=0 := by decide

/-- The residual bounds are derived from a genuine counterexample before
excluding the second A-run as a source. Its endpoint A and old history stay
in the hypotheses; only this one source location is ruled out. -/
theorem three_run_counterexample_not_second_A (f : Nat → Bool) (n h M m L s T j t : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hB : 0<h+M+m+L+s+T)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1)
    (hwin : Win f t (n+h+M+m+L+s+T+j-t)) :
    ¬(n+h+M+m≤t ∧ t<n+h+M+m+L) := by
  intro ht
  have hr := Recaman.ThreeRunSupplyBudget.three_run_free_gap_residual f n h M m L s T j w hw hpre
    hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad
  have hshape := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
  have hon := ones_seg_eq_count f n (h+M+m+L+s+T)
  rw [hshape] at hon
  simp only [ones_append,ones_replicate_S,ones_replicate_A] at hon
  let d:=n+h+M+m+L-t
  have hd : 1≤d := by dsimp [d]; omega
  have hA20 : d+T≤20 := by dsimp [d]; omega
  have hAd : seg f t d=List.replicate d true := by
    apply seg_A
    intro x hx hxK
    have ha := hA2 (x-(n+h+M+m)) (by dsimp [d] at hxK; omega)
    simpa only [show n+h+M+m+(x-(n+h+M+m))=x by omega] using ha
  have hAT : seg f (n+h+M+m+L+s) T=List.replicate T true := by
    apply seg_A
    intro x hx hxT
    have ha := hA3 (x-(n+h+M+m+L+s)) (by omega)
    simpa only [Nat.add_sub_cancel' hx] using ha
  have hword : seg f t (d+s+T+j)=List.replicate d true++List.replicate s false++
      List.replicate T true++List.replicate j false := by
    rw [seg_add,show t+(d+s+T)=n+h+M+m+L+s+T by dsimp [d]; omega,
      seg_false f (n+h+M+m+L+s+T) j hgap,seg_add,
      show t+(d+s)=n+h+M+m+L+s by dsimp [d]; omega,hAT,
      seg_add,show t+d=n+h+M+m+L by dsimp [d]; omega,
      seg_false f (n+h+M+m+L) s hS3,hAd]
  apply actual_ASAS_no_small_window f t d s T j hword hd hA20 (by omega) hr.2.2.2
  simpa only [show n+h+M+m+L+s+T+j-t=d+s+T+j by dsimp [d]; omega] using hwin

end Recaman.PenultimateRunWindow
