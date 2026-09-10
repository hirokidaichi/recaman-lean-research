import Recaman.NonpositivePeriodDrift

namespace Recaman.OneSSGapAlgebra

open LeadingRunSupply

/-! The algebraic part of the one-SS classification. The arbitrary-word
classification and prefix-minimality proof are recorded on paper; this module
certifies the exact gap encoding and its numerical case split. -/

def gapWord (a : Nat) : List Nat → List Bool
  | [] => List.replicate a true
  | g::gs => List.replicate a true ++ false :: gapWord g gs

def gapWeight : List Nat → Int
  | [] => 0
  | g::gs => (gs.length : Int)*g+gapWeight gs

theorem gapWord_length (a : Nat) (gs : List Nat) :
    (gapWord a gs).length=a+gs.sum+gs.length := by
  induction gs generalizing a with
  | nil => simp [gapWord]
  | cons g gs ih => simp [gapWord,ih]; omega

theorem gapWord_mass (a : Nat) (gs : List Nat) :
    mass (gapWord a gs)=(a : Int)+gs.sum-gs.length := by
  induction gs generalizing a with
  | nil => simp [gapWord,mass_replicate_A]
  | cons g gs ih => simp [gapWord,mass_append,mass_replicate_A,mass_cons,ih,ShortPeriodicSupply.sign]; omega

/-- Exact first moment for the concrete encoded word, not an abstract proxy. -/
theorem gapWord_moment (a : Nat) (gs : List Nat) :
    2*moment (gapWord a gs) =
      ((gapWord a gs).length : Int)*((gapWord a gs).length+1)-
      2*(gs.length : Int)*(2*a+gs.length+1)-4*gapWeight gs := by
  induction gs generalizing a with
  | nil => simpa [gapWord,gapWeight] using twice_moment_replicate_A a
  | cons g gs ih =>
    have ht := ih g
    have ha := twice_moment_replicate_A a
    have hm := gapWord_mass g gs
    have hl := gapWord_length g gs
    simp only [gapWord,moment_append,List.length_replicate,moment,mass_cons,
      ShortPeriodicSupply.sign,Bool.false_eq_true,if_false,gapWeight,List.length_cons,
      List.length_append,Int.natCast_add,Int.cast_ofNat_Int]
    rw [hl] at ht ⊢
    simp only [Int.natCast_add] at ht ⊢
    grind

/-- The gap data appearing in the paper classification give this exact P2
criterion on the actual encoded word. The weight formula is explicit. -/
theorem one_SS_gap_P2_iff (a n j z h : Nat) (gs : List Nat)
    (hlen : gs.length=n) (hcount : a+gs.sum=n+1)
    (hweight : 2*gapWeight gs=(n : Int)*(n-1)-2*(n-z)+2*h*(n-j)) :
    P2 (gapWord a gs) ↔ (n : Int)*(2*a+2*h-5)=2*h*j-2*z+1 := by
  have hl := gapWord_length a gs
  have hm := gapWord_mass a gs
  have hM := gapWord_moment a gs
  have hlength : (gapWord a gs).length=2*n+1 := by omega
  have hmass : mass (gapWord a gs)=1 := by omega
  have hmoment : moment (gapWord a gs)=2*(h : Int)*j-2*z+1-(n : Int)*(2*a+2*h-5) := by
    rw [hlength,hlen] at hM
    simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int] at hM
    grind
  unfold P2
  rw [hmass,hmoment]
  constructor
  · intro hh; omega
  · intro hh; exact ⟨rfl,by omega⟩

/-- Complete arithmetic split of the seven allowed extra-A allocations.
Only the last two cases can have a first P2 at their full length. -/
theorem one_SS_parameter_classification (n a v h j z : Nat)
    (hn : 2 ≤ n) (hz : 1 ≤ z) (hzn : z < n)
    (hbudget : a+v+h=3) (hh : h=0 ∨ 2 ≤ h)
    (hP : (n : Int)*(2*a+2*h-5)=2*h*j-2*z+1) :
    (h=0 ∧ a=2 ∧ v=1 ∧ n=2*z-1) ∨
    (h=2 ∧ a=0 ∧ v=1 ∧ (n : Int)=2*z-4*j-1) ∨
    (h=2 ∧ a=1 ∧ v=0 ∧ (n : Int)=4*j-2*z+1) ∨
    (h=3 ∧ a=0 ∧ v=0 ∧ (n : Int)=6*j-2*z+1) := by
  have hcases : h=0 ∨ h=2 ∨ h=3 := by omega
  have acases : a=0 ∨ a=1 ∨ a=2 ∨ a=3 := by omega
  rcases hcases with hh0 | hh2 | hh3 <;> rcases acases with ha0 | ha1 | ha2 | ha3
  all_goals first | subst h
  all_goals first | subst a
  all_goals simp at hP ⊢; omega

theorem bad_gap3_has_clean_room (n j z : Nat) (hzn : z < n)
    (hP : (n : Int)=2*z-4*j-1) :
    4*j+2 ≤ z ∧ 8*j+3 < 2*n+1 := by omega

theorem gapWeight_set (gs : List Nat) (i v : Nat) (hi : i<gs.length) :
    gapWeight (gs.set i v)=gapWeight gs+((gs.length : Int)-i-1)*((v : Int)-gs[i]) := by
  induction gs generalizing i with
  | nil => simp at hi
  | cons g gs ih =>
    cases i with
    | zero => simp [gapWeight]; grind
    | succ i =>
      have hi' : i<gs.length := by simpa using hi
      have h := ih i hi'
      simp only [List.set_cons_succ,gapWeight,List.length_set,List.length_cons,
        List.getElem_cons_succ,Int.natCast_add,Int.cast_ofNat_Int]
      rw [h]
      grind

theorem sum_set_cast (gs : List Nat) (i v : Nat) (hi : i<gs.length) :
    ((gs.set i v).sum : Int)=(gs.sum : Int)+(v : Int)-gs[i] := by
  induction gs generalizing i with
  | nil => simp at hi
  | cons g gs ih =>
    cases i with
    | zero => simp; omega
    | succ i =>
      have h := ih i (by simpa using hi)
      simp only [List.set_cons_succ,List.sum_cons,List.getElem_cons_succ,Int.natCast_add]
      omega

theorem replicate_one_data (n : Nat) :
    (List.replicate n 1).sum=n ∧ 2*gapWeight (List.replicate n 1)=(n : Int)*(n-1) := by
  induction n with
  | zero => simp [gapWeight]
  | succ n ih =>
    simp only [List.replicate_succ,List.sum_cons,gapWeight,List.length_replicate,
      Int.natCast_add,Int.cast_ofNat_Int,Int.mul_one]
    constructor
    · omega
    · grind

def familyGaps (n j z h : Nat) : List Nat :=
  (((List.replicate n 1).set (n-1) 0).set (z-1) 0).set (j-1) (h+1)

theorem familyGaps_data (n j z h : Nat) (hn : 2≤n) (hj : 1≤j) (hjn : j<n)
    (hz : 1≤z) (hzn : z<n) (hjz : j≠z) :
    (familyGaps n j z h).length=n ∧
    ((familyGaps n j z h).sum : Int)=(n : Int)-2+h ∧
    2*gapWeight (familyGaps n j z h)=(n : Int)*(n-1)-2*(n-z)+2*h*(n-j) := by
  let g0 := (List.replicate n 1).set (n-1) 0
  let g1 := g0.set (z-1) 0
  have hl0 : g0.length=n := by simp [g0]
  have hl1 : g1.length=n := by simp [g1,hl0]
  have hnj : n-1≠j-1 := by omega
  have hnz : n-1≠z-1 := by omega
  have hzj : z-1≠j-1 := by omega
  have hg0 : g0[z-1]'(by rw [hl0]; omega)=1 := by simp [g0,hnz]
  have hg1 : g1[j-1]'(by rw [hl1]; omega)=1 := by simp [g1,g0,hzj,hnj]
  have hr := replicate_one_data n
  have hs0 := sum_set_cast (List.replicate n 1) (n-1) 0 (by simp; omega)
  have hs1 := sum_set_cast g0 (z-1) 0 (by rw [hl0]; omega)
  have hs2 := sum_set_cast g1 (j-1) (h+1) (by rw [hl1]; omega)
  have hw0 := gapWeight_set (List.replicate n 1) (n-1) 0 (by simp; omega)
  have hw1 := gapWeight_set g0 (z-1) 0 (by rw [hl0]; omega)
  have hw2 := gapWeight_set g1 (j-1) (h+1) (by rw [hl1]; omega)
  have hncast : ((n-1 : Nat) : Int)=(n : Int)-1 := by omega
  have hjcast : ((j-1 : Nat) : Int)=(j : Int)-1 := by omega
  have hzcast : ((z-1 : Nat) : Int)=(z : Int)-1 := by omega
  simp only [List.length_replicate,List.getElem_replicate,hncast,
    Int.cast_ofNat_Int] at hs0 hw0
  rw [hg0,hl0,hzcast] at hw1
  rw [hg1,hl1,hjcast] at hw2
  rw [hg0] at hs1
  rw [hg1] at hs2
  change (familyGaps n j z h).length=n ∧ _
  refine ⟨by simp [familyGaps],?_,?_⟩
  · change ((g1.set (j-1) (h+1)).sum : Int)=(n : Int)-2+h
    change (g0.sum : Int)=((List.replicate n (1 : Nat)).sum : Int)+0-1 at hs0
    change (g1.sum : Int)=(g0.sum : Int)+0-1 at hs1
    simp only [hr.1,Int.natCast_add,Int.cast_ofNat_Int] at hs0 hs2
    omega
  · change 2*gapWeight (g1.set (j-1) (h+1))=_
    change gapWeight g0=gapWeight (List.replicate n 1)+((n : Int)-(n-1)-1)*(0-1) at hw0
    change gapWeight g1=gapWeight g0+((n : Int)-(z-1)-1)*(0-1) at hw1
    simp only [Int.natCast_add,Int.cast_ofNat_Int] at hw2
    grind

/-- All parameters of both candidate families give actual P2 words. The
arbitrary-word exhaustion and minimum-lag assertion remain paper proofs. -/
theorem family_P2 (n a j z h : Nat) (hn : 2≤n) (hj : 1≤j) (hjn : j<n)
    (hz : 1≤z) (hzn : z<n) (hjz : j≠z) (hah : a+h=3)
    (hP : (n : Int)*(2*a+2*h-5)=2*h*j-2*z+1) :
    (gapWord a (familyGaps n j z h)).length=2*n+1 ∧ P2 (gapWord a (familyGaps n j z h)) := by
  obtain ⟨hl,hs,hw⟩ := familyGaps_data n j z h hn hj hjn hz hzn hjz
  have hcount : a+(familyGaps n j z h).sum=n+1 := by omega
  have hp := (one_SS_gap_P2_iff a n j z h _ hl hcount hw).mpr hP
  refine ⟨?_,hp⟩
  rw [gapWord_length,hl]
  omega

theorem family_A_P2 (n j z : Nat) (hn : 2≤n) (hj : 1≤j) (hjn : j<n)
    (hz : 1≤z) (hzn : z<n) (hjz : j≠z) (hP : (n : Int)=6*j-2*z+1) :
    (gapWord 0 (familyGaps n j z 3)).length=2*n+1 ∧ P2 (gapWord 0 (familyGaps n j z 3)) := by
  apply family_P2 n 0 j z 3 hn hj hjn hz hzn hjz (by decide)
  simpa using hP

theorem family_B_P2 (n j z : Nat) (hn : 2≤n) (hj : 1≤j) (hjn : j<n)
    (hz : 1≤z) (hzn : z<n) (hjz : j≠z) (hP : (n : Int)=4*j-2*z+1) :
    (gapWord 1 (familyGaps n j z 2)).length=2*n+1 ∧ P2 (gapWord 1 (familyGaps n j z 2)) := by
  apply family_P2 n 1 j z 2 hn hj hjn hz hzn hjz (by decide)
  simpa using hP

theorem centered_counterexample_family_A :
    gapWord 0 (familyGaps 7 2 3 3)=
      [false,true,false,true,true,true,true,false,false,true,false,true,false,true,false] ∧
    P2 (gapWord 0 (familyGaps 7 2 3 3)) := by unfold P2; decide

end Recaman.OneSSGapAlgebra
