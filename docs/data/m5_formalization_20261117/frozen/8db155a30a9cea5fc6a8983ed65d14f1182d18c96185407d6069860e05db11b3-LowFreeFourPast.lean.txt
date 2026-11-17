import Recaman.InitialLowFreeRanks
import Recaman.OldAdditionSourceRadius

namespace Recaman.LowFreeFourPast

open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction Recaman.InitialLowFreeRanks
open Recaman.SeparatorTailFreeGap

set_option maxHeartbeats 2000000

theorem downward_crossing (f : Nat → Bool) (n : Nat) (c : Int)
    (hn : Fw f n<c) : ∀ k u, u+k=n → c≤Fw f u →
    ∃ t, u≤t ∧ t<n ∧ Fw f t=c ∧ f t=false := by
  intro k
  induction k with
  | zero => intro u hu hU; simp only [Nat.add_zero] at hu; subst u; omega
  | succ k ih =>
    intro u hu hU
    rcases fw_cases f u with ⟨hF,hA⟩|⟨hF,hS⟩
    · obtain ⟨t,ht,htn,hc,hs⟩ := ih (u+1) (by omega) (by omega)
      exact ⟨t,by omega,htn,hc,hs⟩
    · by_cases he : Fw f u=c
      · exact ⟨u,Nat.le_refl _,by omega,he,hS⟩
      · obtain ⟨t,ht,htn,hc,hs⟩ := ih (u+1) (by omega) (by omega)
        exact ⟨t,by omega,htn,hc,hs⟩

theorem shifted_height (f : Nat → Bool) (s k : Nat) :
    Fw (fun i => f (s+i)) k=Fw f (s+k)-Fw f s := by
  have h1 := seg_mass (fun i => f (s+i)) 0 k
  rw [seg_nat_shift] at h1
  simp only [Nat.add_zero,Nat.zero_add,Fw] at h1
  have h2 := seg_mass f s k
  omega

/-- A proved old floor excludes EVERY erased source for a low target.
The converse restores the identical original window, with its original sign. -/
theorem low_actual_cut_iff (f : Nat → Bool) (s q : Nat) (m : Int)
    (hfloor : ∀ i, i≤s → m≤Fw f i) (hlevel : Fw f (s+q)≤m) :
    EndN f 0 (s+q) ↔ EndN (fun i => f (s+i)) 0 q := by
  have hshift := endN_nat_shift f s 0 q
  simp only [Nat.add_zero] at hshift
  constructor
  · rintro ⟨hA,u,k,_,huk,hW⟩
    have hsu : s≤u := by
      by_cases hu : u<s
      · have hf := hfloor u (by omega)
        have hm := hW.2.1
        rw [huk] at hm
        omega
      · omega
    exact hshift.mp ⟨hA,u,k,hsu,huk,hW⟩
  · intro he
    exact end_mono f 0 s (s+q) (Nat.zero_le _) (hshift.mpr he)

private theorem fourth_high (f : Nat → Bool) (h v : Nat) (hh : 1≤h)
    (hS : ∀ i, i<h → f i=false)
    (hlow : cN (fun i => f i=true ∧ ¬EndN f 0 i ∧ Fw f i≤1-(h : Int)) 0 v≤2)
    (hfour : 4≤cN (fun i => f i=true) 0 v) :
    ∃ q, q<v ∧ 1-(h : Int)<Fw f q ∧
      2≤cN (fun i => f i=true ∧ ¬EndN f 0 i ∧ Fw f i≤1-(h : Int)) 0 q ∧
      ∀ i, i≤q → -(h : Int)-1≤Fw f i := by
  let L := fun i => f i=true ∧ ¬EndN f 0 i ∧ Fw f i≤1-(h : Int)
  obtain ⟨t,htv,htA,htC⟩ := count_rank_clock (fun i => f i=true) 2 v (by omega)
  obtain ⟨q,hqv,hqA,hqC⟩ := count_rank_clock (fun i => f i=true) 3 v (by omega)
  have htq : t<q := by
    by_cases he : q≤t
    · have hm := count_prefix_le (fun i => f i=true) 0 q t he
      omega
    · omega
  have htwoT := two_low_free_of_two_additions f h t hh hS (by omega)
  have hte : EndN f 0 t := by
    by_cases he : EndN f 0 t
    · exact he
    · have hl : L t := ⟨htA,he,early_free_is_low f h t hh hS htA (by omega) he⟩
      have hs := cN_succ_pos L 0 t (by simpa using hl)
      have hm := count_prefix_le L 0 (t+1) v (by omega)
      change 2≤cN L 0 t at htwoT
      change cN L 0 v≤2 at hlow
      omega
  have hqf := fourth_free_after_third_actual f t q htq htC hqC hte
  have htwoQ := two_low_free_of_two_additions f h q hh hS (by omega)
  have hhigh : 1-(h : Int)<Fw f q := by
    by_cases hl : Fw f q≤1-(h : Int)
    · have hs := cN_succ_pos L 0 q (by simpa only [Nat.zero_add] using And.intro hqA (And.intro hqf hl))
      have hm := count_prefix_le L 0 (q+1) v (by omega)
      change 2≤cN L 0 q at htwoQ
      change cN L 0 v≤2 at hlow
      omega
    · omega
  refine ⟨q,hqv,hhigh,htwoQ,?_⟩
  intro i hi
  have hwq := cN_walk f 0 q
  have hwi := cN_walk f 0 i
  simp only [Nat.zero_add,Fw] at hwq hwi
  have hm := count_prefix_le (fun i => f i=false) 0 i q hi
  omega

private theorem descent_run (f : Nat → Bool) (t v : Nat) (ell : Int)
    (htv : t<v) (ht : Fw f t=ell) (htS : f t=false)
    (hno : ∀ i, i<v → Fw f i<ell → f i=false) :
    ∀ i, t≤i → i<v → f i=false := by
  have run : ∀ k, k<v-t → f (t+k)=false := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      by_cases h0 : k=0
      · simpa [h0] using htS
      · have hpre : ∀ i, t≤i → i<t+k → f i=false := by
          intro i hti hik
          have hi := ih (i-t) (by omega) (by omega)
          simpa only [Nat.add_sub_cancel' hti] using hi
        have hw := fw_false_run f t k hpre
        exact hno (t+k) (by omega) (by omega)
  intro i hti hiv
  have hi := run (i-t) (by omega)
  simpa only [Nat.add_sub_cancel' hti] using hi

/-- Low free four confines the unchanged past before any sufficiently
deep original minimum to at most three additions. All heights are unbounded. -/
theorem old_additions_le_three (f : Nat → Bool) (h T v : Nat)
    (hh : 1≤h) (hS : ∀ i, i<h → f i=false) (hvT : v≤T)
    (hmin : ∀ i, i≤T → Fw f v≤Fw f i)
    (hdeep : Fw f v ≤ -(h : Int)-5) (hend : 2-(h : Int)≤Fw f T)
    (hlow : cN (fun i => f i=true ∧ ¬EndN f 0 i ∧ Fw f i≤1-(h : Int)) 0 T≤4) :
    cN (fun i => f i=true) 0 v≤3 := by
  let L := fun i => f i=true ∧ ¬EndN f 0 i ∧ Fw f i≤1-(h : Int)
  obtain ⟨u,w,hvu,huw,hwT,huF,hwF,huA,huf,hwA,hwf⟩ :=
    two_nonsupplied_additions_of_recovery f 0 0 v T BlockWord.nil (by simp [seg])
      (Nat.zero_le _) hvT (Fw f v) rfl (fun i _ hi => hmin i (by omega)) (by omega)
  have hpost : 2≤cN L v (T-v) := two_marks_le_count L v u w (T-v) hvu huw (by omega)
    ⟨huA,huf,by omega⟩ ⟨hwA,hwf,by omega⟩
  have hsplit := cN_sub0 L v T hvT
  have hpre : cN L 0 v≤2 := by change cN L 0 T≤4 at hlow; omega
  by_cases hthree : cN (fun i => f i=true) 0 v≤3
  · exact hthree
  · obtain ⟨q,hqv,hqhigh,hqtwo,hqfloor⟩ := fourth_high f h v hh hS hpre (by omega)
    let ell : Int := -(h : Int)-1
    have hno : ∀ i, i<v → Fw f i<ell → f i=false := by
      intro i hiv hil
      cases hiA : f i
      · rfl
      · obtain ⟨z,hzv,⟨hzA,hzl⟩,hfirst⟩ := SingleWindowEquality.first_mark
          (fun z => f z=true ∧ Fw f z<ell) (v-1) ⟨i,by omega,hiA,hil⟩
        have hfloorZ : ∀ y, y≤z → Fw f z≤Fw f y := by
          have hf := floor_lemma f 0 z (Fw f z) (Int.le_refl _) (by
            intro y _ hy hyF hyA
            exact hfirst y hy ⟨hyA,by omega⟩)
          exact fun y hy => hf y (Nat.zero_le _) hy
        have hzf := block_prefix_low_clock_not_endable f 0 0 z BlockWord.nil
          (by simp [seg]) (Nat.zero_le _) (Fw f z)
          (fun y _ hy => hfloorZ y (by omega)) (by omega)
        have hqz : q<z := by
          by_cases hzq : z≤q
          · have hf := hqfloor z hzq
            dsimp [ell] at hzl
            omega
          · omega
        have hzL : L z := ⟨hzA,hzf,by dsimp [ell] at hzl; omega⟩
        have hm1 := count_prefix_le L 0 q z (by omega)
        have hs := cN_succ_pos L 0 z (by simpa using hzL)
        have hm2 := count_prefix_le L 0 (z+1) v (by omega)
        change 2≤cN L 0 q at hqtwo
        omega
    obtain ⟨t,_,htv,ht,htS⟩ := downward_crossing f v ell (by dsimp [ell]; omega)
      v 0 (by omega) (by simp only [Fw]; dsimp [ell]; omega)
    have hrun := descent_run f t v ell htv ht htS hno
    have htvF := fw_false_run f t (v-t) (by intro i hi hj; exact hrun i hi (by omega))
    rw [Nat.add_sub_cancel' (by omega : t≤v)] at htvF
    have hlen : 4≤v-t := by dsimp [ell] at ht; omega
    have hqt : q<t := by
      by_cases htq : t≤q
      · have hf := fw_false_run f t (q-t) (by intro i hi hj; exact hrun i hi (by omega))
        rw [Nat.add_sub_cancel' htq,ht] at hf
        dsimp [ell] at hf
        omega
      · omega
    have hfloorT : ∀ i, i≤t → ell≤Fw f i := by
      have hf := floor_lemma f 0 t ell (by omega) (by
        intro i _ hit hiF hiA
        have hs := hno i (by omega) (by omega)
        simp [hs] at hiA)
      exact fun i hi => hf i (Nat.zero_le _) hi
    let g := fun i => f (t+i)
    have hgS : ∀ i, i<2 → g i=false := by
      intro i hi
      exact hrun (t+i) (by omega) (by omega)
    have hgDeep := shifted_height f t (v-t)
    rw [Nat.add_sub_cancel' (by omega : t≤v),ht] at hgDeep
    have hgEnd := shifted_height f t (T-t)
    rw [Nat.add_sub_cancel' (by omega : t≤T),ht] at hgEnd
    have hthreeLow := three_low_free_of_deep_return g 2 (T-t) (v-t) (by omega) hgS
      (by omega) (by dsimp [g,ell] at *; omega) (by dsimp [g,ell] at *; omega)
    have hmap : cN (fun i => g i=true ∧ ¬EndN g 0 i ∧ Fw g i≤1-(2 : Int)) 0 (T-t)≤
        cN (fun i => L (t+i)) 0 (T-t) := by
      apply cN_mono
      intro i _ hi hgi
      have hheight := shifted_height f t i
      have hlevel : Fw f (t+i)≤ell := by change Fw g i=_ at hheight; omega
      have hiff := low_actual_cut_iff f t i ell hfloorT hlevel
      refine ⟨hgi.1,fun he => hgi.2.1 (hiff.mp he),?_⟩
      change Fw g i=_ at hheight
      dsimp [ell] at ht
      omega
    have hshift := count_nat_shift L t 0 (T-t)
    simp only [Nat.add_zero] at hshift
    rw [hshift] at hmap
    have h3 : 3≤cN L t (T-t) := Nat.le_trans hthreeLow hmap
    have htwoBefore := count_prefix_le L 0 q t (by omega)
    have htotal := cN_sub0 L t T (by omega)
    change 2≤cN L 0 q at hqtwo
    change cN L 0 T≤4 at hlow
    omega

end Recaman.LowFreeFourPast
