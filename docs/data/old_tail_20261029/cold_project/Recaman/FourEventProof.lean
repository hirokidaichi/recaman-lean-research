import Recaman.BlockSuffixPositivity

namespace Recaman.FourEventProof

open Recaman.FourNonsuppliedData
open Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

def endpointGood (s : State) : Bool :=
  decide (((s.subtractions : Int)-(s.additions : Int)+(s.nonsupplied : Int)=1) →
    s.word ∈ endpointWords)

def goodState (s : State) : Bool :=
  decide (s.additions≤10 ∧ s.subtractions≤19 ∧ s.nonsupplied≤4 ∧ gap s 0=s) &&
    (List.range 20).all (fun j => endpointGood (gap s j))

def successors (s : State) : List State :=
  (List.range 20).flatMap fun j => [macroA s j false,macroA s j true].filterMap id

/-- A finite proof DAG, without a global table lookup or an unverified
table hypothesis. Concrete certificates must be constructed by the kernel. -/
inductive Checked : State → Prop
  | node (s : State) (good : goodState s=true)
      (children : ∀ t, t∈successors s → Checked t) : Checked s

theorem checked_of_children (s : State) (children : List State)
    (hg : goodState s=true) (hnext : successors s=children)
    (hc : ∀ t, t∈children → Checked t) : Checked s := by
  apply Checked.node s hg
  rw [hnext]
  exact hc

theorem checked_good {s : State} (h : Checked s) : goodState s=true := by
  cases h with
  | node _ hg _ => exact hg

theorem checked_additions_le_ten {s : State} (h : Checked s) : s.additions≤10 := by
  have hg := checked_good h
  simp only [goodState,Bool.and_eq_true,decide_eq_true_eq] at hg
  exact hg.1.1

theorem checked_gap_zero {s : State} (h : Checked s) : gap s 0=s := by
  have hg := checked_good h
  simp only [goodState,Bool.and_eq_true,decide_eq_true_eq] at hg
  exact hg.1.2.2.2

theorem checked_macro {s t : State} (h : Checked s) (j : Nat) (e : Bool)
    (ht : macroA s j e=some t) : Checked t := by
  cases h with
  | node _ _ hc =>
    apply hc t
    apply List.mem_flatMap.mpr
    refine ⟨min j 19,List.mem_range.mpr (by omega),?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨macroA s (min j 19) e,?_,?_⟩
    · cases e <;> simp
    · simpa only [id_eq,macroA,←gap_clamp] using ht

def Covered (s : State) : Prop := ∃ t j, Checked t ∧ gap t j=s

theorem checked_covered {s : State} (h : Checked s) : Covered s :=
  ⟨s,0,h,checked_gap_zero h⟩

theorem covered_additions_le_ten {s : State} (h : Covered s) : s.additions≤10 := by
  obtain ⟨t,j,hc,rfl⟩ := h
  change t.additions≤10
  exact checked_additions_le_ten hc

theorem covered_S {s : State} (h : Covered s) : Covered (stepS s) := by
  obtain ⟨t,j,hc,rfl⟩ := h
  exact ⟨t,j+1,hc,(gap_add t j 1).symm⟩

theorem covered_A {s t : State} (h : Covered s) (e : Bool)
    (ht : stepA s e=some t) : Covered t := by
  obtain ⟨u,j,hc,hgap⟩ := h
  apply checked_covered
  apply checked_macro hc j e
  simpa only [macroA,hgap] using ht

theorem covered_endpoint {s : State} (h : Covered s)
    (hd : (s.subtractions : Int)-(s.additions : Int)+(s.nonsupplied : Int)=1) :
    s.word∈endpointWords := by
  obtain ⟨t,j,hc,rfl⟩ := h
  have hg := checked_good hc
  simp only [goodState,Bool.and_eq_true,decide_eq_true_eq] at hg
  have hp := List.all_eq_true.mp hg.2 (min j 19) (List.mem_range.mpr (by omega))
  have he := of_decide_eq_true hp
  rw [←gap_clamp] at he
  exact he hd

/-- The initial certificate is an explicit parameter of this reduction.
No unconditional classification is claimed until data constructs it. -/
theorem actual_covered_of_initial (initial : Checked ⟨[],0,0,0⟩)
    (f : Nat → Bool) (n a B : Nat) {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true)
    (hpos : ∀ k, 0<k → k≤B → cN (EndN f 0) n k+1≤cN (fun u => f u=false) n k)
    (hbudget : cN (fun u => f u=true ∧ ¬EndN f 0 u) n B≤4) :
    Covered (actualFourState f n B) := by
  have hall : ∀ k, k≤B → Covered (actualFourState f n k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hz : actualFourState f n 0=⟨[],0,0,0⟩ := by rfl
      rw [hz]
      exact checked_covered initial
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hcount : cN (fun u => f u=true) n k≤10 := covered_additions_le_ten hp
      by_cases hS : f (n+k)=false
      · rw [←actualFourState_S f n k hS]
        exact covered_S hp
      · have hA : f (n+k)=true := by cases h : f (n+k) <;> simp_all
        have hbud : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (k+1)≤4 := by
          have h := count_prefix_le (fun u => f u=true ∧ ¬EndN f 0 u) n (k+1) B hk
          omega
        have hpar := addition_endable_partition f n (k+1)
        have hpost := hpos (k+1) (by omega) hk
        have ha := cN_succ_pos (fun u => f u=true) n k hA
        have hs := cN_succ_neg (fun u => f u=false) n k (by simp [hA])
        have hbal : 1≤(cN (fun u => f u=false) n k : Int)-
            (cN (fun u => f u=true) n k+1 : Nat)+
            (cN (fun u => f u=true ∧ ¬EndN f 0 u) n (k+1) : Int) := by omega
        by_cases he : EndN f 0 (n+k)
        · exact covered_A hp true (actualFourState_A f n a k hβ hseg hA hcount true he hbud hbal)
        · exact covered_A hp false (actualFourState_A f n a k hβ hseg hA hcount false he hbud hbal)
  exact hall B (Nat.le_refl _)

theorem excursion_word_of_initial (initial : Checked ⟨[],0,0,0⟩)
    (f : Nat → Bool) (n a B : Nat) {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true)
    (hpos : ∀ k, 0<k → k≤B → cN (EndN f 0) n k+1≤cN (fun u => f u=false) n k)
    (hbudget : cN (fun u => f u=true ∧ ¬EndN f 0 u) n B≤4)
    (hend : cN (EndN f 0) n B+1=cN (fun u => f u=false) n B) :
    seg f n B∈endpointWords := by
  have hc := actual_covered_of_initial initial f n a B hβ hseg hpos hbudget
  have ha : cN (fun u => f u=true) n B≤10 := covered_additions_le_ten hc
  have hpar := addition_endable_partition f n B
  have hslt : cN (fun u => f u=false) n B<19 := by omega
  have hnot : ¬19≤cN (fun u => f u=false) n B := by omega
  have hmin : min 19 (cN (fun u => f u=false) n B)=cN (fun u => f u=false) n B := by omega
  have hbal : ((actualFourState f n B).subtractions : Int)-
      ((actualFourState f n B).additions : Int)+((actualFourState f n B).nonsupplied : Int)=1 := by
    simp only [actualFourState,hmin]
    omega
  have hw := covered_endpoint hc hbal
  simpa only [actualFourState,if_neg hnot] using hw

theorem excursion_word_from_zero_of_initial (initial : Checked ⟨[],0,0,0⟩)
    (f : Nat → Bool) (n a q : Nat) {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hnq : n≤q)
    (hzero : cN (EndN f 0) 0 n=cN (fun u => f u=false) 0 n)
    (hpos : ∀ u, n<u → u≤q → cN (EndN f 0) 0 u+1≤cN (fun u => f u=false) 0 u)
    (hroot : cN (EndN f 0) 0 q+1=cN (fun u => f u=false) 0 q)
    (haz : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤4) :
    seg f n (q-n)∈endpointWords := by
  have hrel : ∀ k, 0<k → k≤q-n →
      cN (EndN f 0) n k+1≤cN (fun u => f u=false) n k := by
    intro k hk hkq
    have hp := hpos (n+k) (by omega) (by omega)
    have he := cN_add (EndN f 0) 0 n k
    have hs := cN_add (fun u => f u=false) 0 n k
    simp only [Nat.zero_add] at he hs
    omega
  have hr : cN (EndN f 0) n (q-n)+1=cN (fun u => f u=false) n (q-n) := by
    have he := cN_add (EndN f 0) 0 n (q-n)
    have hs := cN_add (fun u => f u=false) 0 n (q-n)
    rw [Nat.add_sub_cancel' hnq] at he hs
    simp only [Nat.zero_add] at he hs
    omega
  exact excursion_word_of_initial initial f n a (q-n) hβ hseg hrel haz hr

theorem area_from_zero_of_initial (initial : Checked ⟨[],0,0,0⟩)
    (f : Nat → Bool) (n a q b : Nat) {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hnq : n≤q) (hqb : q≤b)
    (hzero : cN (EndN f 0) 0 n=cN (fun u => f u=false) 0 n)
    (hpos : ∀ u, n<u → u≤b → cN (EndN f 0) 0 u+1≤cN (fun u => f u=false) 0 u)
    (hroot : cN (EndN f 0) 0 q+1=cN (fun u => f u=false) 0 q)
    (haz : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤4)
    (hay : cN (fun u => f u=true ∧ ¬EndN f 0 u) q (b-q)≤1)
    (hguard : Fw f b≤Fw f n) :
    0≤Ar f n (b-n)+((b-n : Nat) : Int)*(Fw f n-Fw f b+1) := by
  have hw := excursion_word_from_zero_of_initial initial f n a q hβ hseg hnq hzero
    (fun u hnu huq => hpos u hnu (by omega)) hroot haz
  exact sixteen_root_area_from_zero f n a q b hβ hseg hnq hqb hzero hpos hroot hw hay hguard

theorem no_old_window_of_initial (initial : Checked ⟨[],0,0,0⟩)
    (f : Nat → Bool) (n a q b t : Nat) {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hnq : n≤q) (hqb : q≤b)
    (hzero : cN (EndN f 0) 0 n=cN (fun u => f u=false) 0 n)
    (hpos : ∀ u, n<u → u≤b → cN (EndN f 0) 0 u+1≤cN (fun u => f u=false) 0 u)
    (hroot : cN (EndN f 0) 0 q+1=cN (fun u => f u=false) 0 q)
    (haz : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤4)
    (hay : cN (fun u => f u=true ∧ ¬EndN f 0 u) q (b-q)≤1) (htn : t<n) :
    ¬Win f t (b-t) := by
  have hw := excursion_word_from_zero_of_initial initial f n a q hβ hseg hnq hzero
    (fun u hnu huq => hpos u hnu (by omega)) hroot haz
  exact sixteen_root_no_old_window f n a q b t hβ hseg hnq hqb hzero hpos hroot hw hay htn

theorem depth_from_zero_of_initial (initial : Checked ⟨[],0,0,0⟩)
    (f : Nat → Bool) (n a q : Nat) {β : List Bool} (hβ : BlockWord β)
    (hseg : seg f 0 n=β++List.replicate a true) (hnq : n≤q)
    (hzero : cN (EndN f 0) 0 n=cN (fun u => f u=false) 0 n)
    (hpos : ∀ u, n<u → u≤q → cN (EndN f 0) 0 u+1≤cN (fun u => f u=false) 0 u)
    (hroot : cN (EndN f 0) 0 q+1=cN (fun u => f u=false) 0 q)
    (haz : cN (fun u => f u=true ∧ ¬EndN f 0 u) n (q-n)≤4) :
    ∀ u, n≤u → u≤q → Fw f n-4≤Fw f u := by
  have hw := excursion_word_from_zero_of_initial initial f n a q hβ hseg hnq hzero hpos hroot haz
  intro u hnu huq
  have hd := four_endpoint_word_prefix_depth (seg f n (q-n)) hw (u-n) (by
    rw [seg_length]; omega)
  rw [seg_take f n (q-n) (u-n) (by omega),seg_mass,Nat.add_sub_cancel' hnu] at hd
  omega

open Classical in
theorem area_int_of_initial (initial : Checked ⟨[],0,0,0⟩)
    (e : Int → Bool) (p : Int) (n a q b : Nat) {β : List Bool} (hβ : BlockWord β)
    (hseg : segment e p n=β++List.replicate a true) (hnq : n≤q) (hqb : q≤b)
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ u, n<u → u≤b → endableCount e p u+1≤subtractionCount e p u)
    (hroot : endableCount e p q+1=subtractionCount e p q)
    (haz : countP (fun c => e c=true ∧ ¬Endable e p c) (p+(n : Int)) (q-n)≤4)
    (hay : countP (fun c => e c=true ∧ ¬Endable e p c) (p+(q : Int)) (b-q)≤1)
    (hguard : Fw (fun i => e (p+(i : Int))) b≤Fw (fun i => e (p+(i : Int))) n) :
    0≤Ar (fun i => e (p+(i : Int))) n (b-n)+((b-n : Nat) : Int)*
      (Fw (fun i => e (p+(i : Int))) n-Fw (fun i => e (p+(i : Int))) b+1) := by
  classical
  rw [segment_seg e p p 0 (by simp)] at hseg
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos hroot
  rw [nonsupplied_count_shift] at haz hay
  exact area_from_zero_of_initial initial (fun i => e (p+(i : Int))) n a q b
    hβ hseg hnq hqb hzero hpos hroot haz hay hguard

end Recaman.FourEventProof
