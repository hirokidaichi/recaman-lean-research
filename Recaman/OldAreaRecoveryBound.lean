import Recaman.BlockSuffixPositivity

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Recaman.OldAreaRecoveryBound

open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Recaman.LeadingRunSupply
open Recaman.ThreeNonsuppliedData (localSupply)
open Recaman.ShortPeriodicSupply (sign)

/-! A relaxation of old source areas. The explicit old-source admission
premise is produced on paper from the original floor and at most three
old A. No joint realization of the admitted sources is assumed. -/

def oldAllowed (p : Nat) (j C : Int) : Bool :=
  if j < 0 then false else
  let tri := j*(j+1)/2
  if p ≤ 2 then
    (List.range (p+1)).any fun r => decide
      (-tri+(r : Int)*(1-2*j) ≤ C ∧ C ≤ (r : Int)^2-tri ∧
       (C-(r : Int)+tri)%2=0)
  else
    decide (C = -tri ∨ (2 ≤ j ∧ C = 1-tri) ∨ (1 ≤ j ∧ C = 4-tri)) ||
      (List.range (j.toNat+1)).any (fun s => decide (C = 9-tri-6*(s : Int)))

def possible (p : Nat) (w : List Bool) : Bool :=
  localSupply w || oldAllowed p (mass w-1) ((mass w-1)*(w.length : Int)-areaW w)

def oldPaid (p : Nat) : Nat := if p=0 then 0 else if p=1 then 1 else 2

def nextPaid (p : Nat) (w : List Bool) (a : Nat) : Nat :=
  a + if possible p w then 0 else 1

def check : Nat → Nat → List Bool → Int → Nat → Bool
  | 0, _, _, _, _ => false
  | fuel+1, p, w, h, a =>
    decide (h < 7) &&
      ((if 1 < h then check fuel p (w ++ [false]) (h-1) a else true) &&
       (if nextPaid p w a ≤ 4 then
          check fuel p (w ++ [true]) (h+1) (nextPaid p w a) else true))

/-- The four relaxed roots have finite proof certificates. Proof fuel
does not bound the original future length in the theorem below. -/
theorem four_roots_checked :
    (List.range 4).all (fun p => check 14 p [] 0 (oldPaid p)) = true := by
  decide

private def Good (p : Nat) (w : List Bool) (h : Int) (a : Nat) : Prop :=
  ∃ fuel, check fuel p w h a = true

private theorem good_height (p : Nat) (w : List Bool) (h : Int) (a : Nat)
    (hg : Good p w h a) : h < 7 := by
  obtain ⟨fuel,hg⟩ := hg
  cases fuel with
  | zero => simp [check] at hg
  | succ fuel =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg.1

private theorem good_S (p : Nat) (w : List Bool) (h : Int) (a : Nat)
    (hg : Good p w h a) (hh : 1 < h) : Good p (w ++ [false]) (h-1) a := by
  obtain ⟨fuel,hg⟩ := hg
  cases fuel with
  | zero => simp [check] at hg
  | succ fuel =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact ⟨fuel, by simpa only [if_pos hh] using hg.2.1⟩

private theorem good_A (p : Nat) (w : List Bool) (h : Int) (a : Nat)
    (hg : Good p w h a) (ha : nextPaid p w a ≤ 4) :
    Good p (w ++ [true]) (h+1) (nextPaid p w a) := by
  obtain ⟨fuel,hg⟩ := hg
  cases fuel with
  | zero => simp [check] at hg
  | succ fuel =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact ⟨fuel, by simpa only [if_pos ha] using hg.2.2⟩

/-- Every actual supplier is retained: local windows are literal and
every crossing old window is admitted by the explicit area premise. -/
theorem actual_implies_possible (f : Nat → Bool) (v q p : Nat) (hvq : v ≤ q)
    (hOld : ∀ u k, u < v → u+k=q → Win f u k →
      oldAllowed p (Fw f q-Fw f v-1)
        ((Fw f q-Fw f v-1)*((q-v : Nat) : Int)-Ar f v (q-v)) = true)
    (he : EndN f 0 q) : possible p (seg f v (q-v)) = true := by
  obtain ⟨hA,u,k,_,huk,hW⟩ := he
  unfold possible
  apply Bool.or_eq_true_iff.mpr
  by_cases hu : v ≤ u
  · left
    exact (localSupply_seg_iff f v q hvq hA).mpr ⟨hA,u,k,hu,huk,hW⟩
  · right
    rw [seg_mass,seg_length,←Ar_areaW,Nat.add_sub_cancel' hvq]
    exact hOld u k (by omega) huk hW

private theorem paid_A_step_le (f : Nat → Bool) (v n p a : Nat)
    (hA : f n = true)
    (ha : a ≤ cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 n)
    (hpossible : EndN f 0 n → possible p (seg f v (n-v)) = true) :
    nextPaid p (seg f v (n-v)) a ≤
      cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 (n+1) := by
  by_cases he : EndN f 0 n
  · have hh := hpossible he
    have hc := cN_succ_neg (fun i => f i = true ∧ ¬EndN f 0 i) 0 n
      (fun h => h.2 (by simpa only [Nat.zero_add] using he))
    rw [hc]
    simpa [nextPaid,hh] using ha
  · have hc := cN_succ_pos (fun i => f i = true ∧ ¬EndN f 0 i) 0 n
      (by simpa only [Nat.zero_add] using And.intro hA he)
    rw [hc]
    cases hb : possible p (seg f v (n-v)) <;> simp [nextPaid,hb] <;> omega

private theorem original_prefix_good (f : Nat → Bool) (v K p : Nat) (hp : p < 4)
    (hpaid : oldPaid p ≤ cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 v)
    (hfree : cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 (v+K) ≤ 4)
    (hfloor : ∀ j, 0 < j → j ≤ K → Fw f v < Fw f (v+j))
    (hOld : ∀ q, v ≤ q → q < v+K → ∀ u k, u < v → u+k=q → Win f u k →
      oldAllowed p (Fw f q-Fw f v-1)
        ((Fw f q-Fw f v-1)*((q-v : Nat) : Int)-Ar f v (q-v)) = true) :
    ∀ j, j ≤ K → ∃ a, Good p (seg f v j) (Fw f (v+j)-Fw f v) a ∧
      a ≤ cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 (v+j) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨oldPaid p,?_,by simpa only [Nat.add_zero] using hpaid⟩
    simp only [Nat.add_zero,Int.sub_self,seg,List.range_zero,List.map_nil]
    exact ⟨14,List.all_eq_true.mp four_roots_checked p (List.mem_range.mpr hp)⟩
  | succ j ih =>
    intro hj
    obtain ⟨a,hg,ha⟩ := ih (by omega)
    let n := v+j
    have hclock : v+(j+1)=n+1 := by dsimp [n]; omega
    have hnv : n-v=j := by dsimp [n]; omega
    have hpos := hfloor (j+1) (by omega) hj
    rw [hclock] at hpos ⊢
    have hc : cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 (n+1) ≤ 4 := by
      have hm := count_prefix_le (fun i => f i = true ∧ ¬EndN f 0 i)
        0 (n+1) (v+K) (by dsimp [n]; omega)
      omega
    change Good p (seg f v j) (Fw f n-Fw f v) a at hg
    change a ≤ cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 n at ha
    cases hs : f n with
    | false =>
      have hw : seg f v (j+1)=seg f v j ++ [false] := by
        rw [seg_succ]
        change seg f v j ++ [f n]=_
        rw [hs]
      have hh : Fw f (n+1)-Fw f v=(Fw f n-Fw f v)-1 := by
        rw [Fw_succ,hs]
        change Fw f n + (-1) - Fw f v = (Fw f n-Fw f v)-1
        omega
      have hf : cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 (n+1) =
          cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 n := by
        apply cN_succ_neg
        intro ht
        have htA := ht.1
        simp only [Nat.zero_add,hs] at htA
        contradiction
      refine ⟨a,?_,by rwa [hf]⟩
      rw [hw,hh]
      exact good_S _ _ _ _ hg (by omega)
    | true =>
      have hw : seg f v (j+1)=seg f v j ++ [true] := by
        rw [seg_succ]
        change seg f v j ++ [f n]=_
        rw [hs]
      have hh : Fw f (n+1)-Fw f v=(Fw f n-Fw f v)+1 := by
        rw [Fw_succ,hs]
        change Fw f n + 1 - Fw f v = (Fw f n-Fw f v)+1
        omega
      have hposs : EndN f 0 n → possible p (seg f v (n-v)) = true := by
        intro he
        exact actual_implies_possible f v n p (by dsimp [n]; omega)
          (hOld n (by dsimp [n]; omega) (by dsimp [n]; omega)) he
      have hle := paid_A_step_le f v n p a hs ha hposs
      rw [hnv] at hle
      refine ⟨nextPaid p (seg f v j) a,?_,hle⟩
      rw [hw,hh]
      exact good_A _ _ _ _ hg (by omega)

/-- Conditional original-history consumer of the explicit old-area
admission premise. Every original free is charged from Nat0; K, depth
and upper prehistory are unrestricted. The paper spectrum producer is
not silently claimed as a Lean theorem by this declaration. -/
theorem recovery_bound_of_old_area_admission (f : Nat → Bool) (v K p : Nat) (hp : p < 4)
    (hpaid : oldPaid p ≤ cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 v)
    (hfree : cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 (v+K) ≤ 4)
    (hfloor : ∀ j, 0 < j → j ≤ K → Fw f v < Fw f (v+j))
    (hOld : ∀ q, v ≤ q → q < v+K → ∀ u k, u < v → u+k=q → Win f u k →
      oldAllowed p (Fw f q-Fw f v-1)
        ((Fw f q-Fw f v-1)*((q-v : Nat) : Int)-Ar f v (q-v)) = true) :
    Fw f (v+K) < Fw f v+7 := by
  obtain ⟨a,hg,_⟩ := original_prefix_good f v K p hp hpaid hfree hfloor hOld K (Nat.le_refl _)
  have hh := good_height _ _ _ _ hg
  omega

end Recaman.OldAreaRecoveryBound
