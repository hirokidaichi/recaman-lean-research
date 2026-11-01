import Recaman.OldTargetClockCollision

namespace Recaman.OldTargetMiddleCharge

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A middle-S source supplying the final band of the last A ray charges
at least j+1 A signs to the first run. All word lengths are unrestricted. -/
theorem middle_S_tail_first_run (u : List Bool) (hu : BlockWord u)
    (h M m L s i T j q : Nat) (hq : q≤m) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (List.replicate q false++List.replicate L true++List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate q false++List.replicate L true++List.replicate s false)= -2)
    (hm2 : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) : j+1≤M := by
  let a := m-q
  let U := u++List.replicate h false++List.replicate M true++List.replicate a false
  let v := List.replicate q false++List.replicate L true++List.replicate s false
  let C := mass u
  let H : Int := (h : Int)+(a : Int)
  let R : Int := (j : Int)+1
  have ha : a+q=m := by dsimp [a]; omega
  have hsplit : U++v++List.replicate T true++List.replicate j false=
      u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false := by
    simp only [U,v,List.append_assoc]
    rw [←List.append_assoc (List.replicate a false) (List.replicate q false),
      List.replicate_append_replicate,ha]
  have hk := source_key_before_gap (U++v) T j (by simpa only [hsplit] using hm2)
    (by simpa only [hsplit] using ha2)
  have hv : runKey v= -2 := hk1
  have hmU : 0≤mass U := by
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm1 hm2
    simp only [U,mass_append,mass_rep_false,mass_replicate_A]
    have hcast : (a : Int)+(q : Int)=(m : Int) := by omega
    omega
  have hC := block_mass_nonnegative hu
  change 0≤C at hC
  have hlow := block_area_quadratic_lower hu
  have hku : -2≤runKey u := by unfold runKey; omega
  have hmassU : mass U=C+(M : Int)-H := by
    simp only [U,mass_append,mass_rep_false,mass_replicate_A]
    dsimp [C,H]
    omega
  have hkeyU : runKey U=runKey u+2*C^2-2*(H-C)^2+4*(M : Int)*(a : Int) := by
    dsimp [U]
    rw [runKey_append_S,runKey_append_A,runKey_append_S]
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    dsimp [C,H]
    grind
  have hsq : (H-C)^2≤C^2+(M : Int)^2 := by
    by_cases hh : H≤C
    · have hp := Int.mul_nonneg (show 0≤H by dsimp [H]; omega) (show 0≤2*C-H by omega)
      have hMM := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(M : Int) by omega)
      grind
    · have hp := Int.mul_nonneg (show 0≤(M : Int)-(H-C) by omega)
        (show 0≤(M : Int)+(H-C) by omega)
      have hCC := Int.mul_nonneg hC hC
      grind
  have hMa := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(a : Int) by omega)
  have hUlow : -2-2*(M : Int)^2≤runKey U := by grind
  rw [runKey_append,hv] at hk
  have hcross := Int.mul_nonneg hmU (show 0≤(cntF v : Int) by omega)
  have hquad : R^2≤(M : Int)^2+2 := by dsimp [R]; grind
  have hR : 3≤R := by dsimp [R]; omega
  by_cases hh : j+1≤M
  · exact hh
  · exfalso
    have hp := Int.mul_nonneg (show 0≤R-1-(M : Int) by dsimp [R]; omega)
      (show 0≤R-1+(M : Int) by omega)
    grind

theorem middle_clock_first_run (u : List Bool) (hu : BlockWord u)
    (h M m L s i T j : Nat) (hj : 2≤j) (hband : T≤i+j)
    (hm2 : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hmid : let q : Int := (i : Int)+(L : Int)-(s : Int)-1
      1≤q ∧ q≤(m : Int) ∧ (q+(s : Int))^2=2*(L : Int)*(s : Int)+1) : j+1≤M := by
  dsimp only at hmid
  let q : Int := (i : Int)+(L : Int)-(s : Int)-1
  have hq0 : 0≤q := by dsimp [q]; omega
  have hqN : (q.toNat : Int)=q := Int.toNat_of_nonneg hq0
  have hmass : mass (List.replicate q.toNat false++List.replicate L true++List.replicate s false)+
      (i : Int)=1 := by
    simp only [mass_append,mass_rep_false,mass_replicate_A,hqN]
    dsimp [q]
    omega
  have hkey : runKey (List.replicate q.toNat false++List.replicate L true++List.replicate s false)= -2 := by
    rw [runKey_S_A_S]
    rw [hqN]
    grind
  exact middle_S_tail_first_run u hu h M m L s i T j q.toNat (by omega) hj hband hmass hkey hm2 ha2

/-- With a small first run, every actual full-prefix supply on the final
band must be the single clock2, with no existence assumption for it. -/
theorem full_small_first_tail_clock (w : List Bool) (hw : BlockWord w)
    (t h M m L s i T j : Nat) (ht : t<w.length)
    (hj : 4≤j) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hband : T≤i+j) (hbudget : M+L+T≤j+10) (hM : M≤j)
    (hm2 : mass (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hc : Recaman.ThreeNonsuppliedData.localSupply
      (w++List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true) : i=2 := by
  have hh := full_old_target_two_clock w hw t h M m L s i T j ht hj hm hL hs hband hbudget hm2 ha2 hc
  simp only [twoClock,decide_eq_true_eq] at hh
  rcases hh with hi|hmiddle
  · exact hi
  · have hu := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
    have hb := middle_clock_first_run (w.drop t) hu h M m L s i T j (by omega) hband hm2 ha2 hmiddle
    omega

private theorem cN_length_bound (P : Nat → Prop) (n : Nat) : ∀ K, cN P n K≤K
  | 0 => Nat.le_refl 0
  | K+1 => by have hh := cN_succ_le P n K; have ih := cN_length_bound P n K; omega

theorem ray_count_band_bound (w : List Bool) (T j b : Nat) (Q : Nat → Prop)
    (hQ : cN Q 0 T≤b)
    (himp : ∀ i, i<T → T≤i+j →
      Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true)=true → Q i) :
    rayCount w T≤T-j+b := by
  let P := fun i => Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true)=true
  have hp := cN_add P 0 (T-j) (T-(T-j))
  have hq := cN_add Q 0 (T-j) (T-(T-j))
  simp only [Nat.zero_add,show T-j+(T-(T-j))=T by omega] at hp hq
  have hmono : cN P (T-j) (T-(T-j))≤cN Q (T-j) (T-(T-j)) := by
    apply cN_mono
    intro i hi hiT hh
    exact himp i (by omega) (by omega) hh
  have hfirst := cN_length_bound P 0 (T-j)
  change cN P 0 T≤T-j+b
  omega

private theorem middle_early_large_L (m L s i : Nat) (hs : 1≤s) (hi : i<2)
    (hp : let q : Int := (i : Int)+(L : Int)-(s : Int)-1
      1≤q ∧ q≤(m : Int) ∧ (q+(s : Int))^2=2*(L : Int)*(s : Int)+1) : 4≤L := by
  dsimp only at hp
  by_cases hL : 4≤L
  · exact hL
  · have hls : L=0 ∨ L=1 ∨ L=2 ∨ L=3 := by omega
    have his : i=0 ∨ i=1 := by omega
    rcases hls with rfl|rfl|rfl|rfl <;> rcases his with rfl|rfl <;>
      simp only [Int.natCast_zero,Int.natCast_one,Int.zero_add,Int.add_zero] at hp <;> grind

theorem twoClock_short_small_L (m L s i : Nat) (hs : 1≤s) (hL : L≤3) (hi : i<3)
    (hc : twoClock m L s i=true) : i=2 := by
  simp only [twoClock,decide_eq_true_eq] at hc
  rcases hc with hi2|hmiddle
  · exact hi2
  · by_cases hi2 : i=2
    · exact hi2
    · have hb := middle_early_large_L m L s i hs (by omega) hmiddle
      omega

private theorem middle_count_le_one (m L s T : Nat) :
    cN (fun i : Nat => let q : Int := (i : Int)+(L : Int)-(s : Int)-1
      1≤q ∧ q≤(m : Int) ∧ (q+(s : Int))^2=2*(L : Int)*(s : Int)+1) 0 T≤1 := by
  apply cN_le_one_of_unique
  intro i _ k _ hi hk
  dsimp only at hi hk
  have hz : ((i : Int)-(k : Int))*((i : Int)+(k : Int)+2*(L : Int)-2)=0 := by grind
  have hp : 0<(i : Int)+(k : Int)+2*(L : Int)-2 := by omega
  rcases Int.mul_eq_zero.mp hz with h|h <;> omega

/-- Numeric budgets here are consumed only after they have been supplied
by the actual two-run theorem. The same target word supplies every clock
restriction; no independently chosen old tags occur. -/
theorem old_target_count_charge (w : List Bool) (hw : BlockWord w)
    (t h M m L s T j F F3 : Nat) (ht : t<w.length)
    (hj : 4≤j) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hM : 1≤M)
    (hbudget : M+L+T≤j+10) (hlower : 2*(j+1)+1≤M+L+T)
    (hm2 : mass (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hhead : M+L≤2*F+1) (hhead5 : M+L≤F+5)
    (hpart : T≤F3+rayCount (w++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) T) : j+1≤F+F3 := by
  let v := w++List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false
  have htwo := full_old_target_ray_count_two w hw t h M m L s T j ht hj hm hL hs hbudget hm2 ha2
  change rayCount v T≤T-j+2 at htwo
  change T≤F3+rayCount v T at hpart
  have hone : M≤j → rayCount v T≤T-j+1 := by
    intro hMj
    apply ray_count_band_bound v T j 1 (fun i => i=2)
    · apply cN_le_one_of_unique
      intros
      omega
    · intro i hi hb hc
      exact full_small_first_tail_clock w hw t h M m L s i T j ht hj hm hL hs hb hbudget hMj hm2 ha2 hc
  by_cases hgood : j+1≤F+F3
  · exact hgood
  · exfalso
    by_cases hT : j≤T
    · by_cases hlarge : j+1≤M
      · omega
      · have hMj : M≤j := by omega
        have hb1 := hone hMj
        by_cases hML : 4≤M+L
        · omega
        · have hz : rayCount v T≤T-j+0 := by
            apply ray_count_band_bound v T j 0 (fun _ => False)
            · exact Nat.le_of_eq (cN_zero_of (fun _ => False) 0 T (by intros; simp))
            · intro i hi hb hc
              have hi2 := full_small_first_tail_clock w hw t h M m L s i T j ht hj hm hL hs hb
                hbudget hMj hm2 ha2 hc
              omega
          omega
    · have hj4 : j=4 := by omega
      have ht3 : T≤3 := by omega
      have hb1 : rayCount v T≤1 := by
        by_cases hT2 : T≤2
        · have hb : rayCount v T≤T-j+1 := by
            apply ray_count_band_bound v T j 1
              (fun i => let q : Int := (i : Int)+(L : Int)-(s : Int)-1
                1≤q ∧ q≤(m : Int) ∧ (q+(s : Int))^2=2*(L : Int)*(s : Int)+1)
            · exact middle_count_le_one m L s T
            · intro i hi hb hc
              have hh := full_old_target_two_clock w hw t h M m L s i T j ht hj hm hL hs hb hbudget hm2 ha2 hc
              simp only [twoClock,decide_eq_true_eq] at hh
              rcases hh with hi2|hmid
              · omega
              · exact hmid
          omega
        · have hT3 : T=3 := by omega
          by_cases hMj : M≤j
          · have hb := hone hMj
            omega
          · have hL3 : L≤3 := by omega
            have hb : rayCount v T≤T-j+1 := by
              apply ray_count_band_bound v T j 1 (fun i => i=2)
              · apply cN_le_one_of_unique
                intros
                omega
              · intro i hi hb hc
                have hh := full_old_target_two_clock w hw t h M m L s i T j ht hj hm hL hs hb hbudget hm2 ha2 hc
                exact twoClock_short_small_L m L s i hs hL3 (by omega) hh
            omega
      omega

theorem three_run_old_target_free_gap (f : Nat → Bool) (n t h M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T)
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
    (hwin : Win f t (n+h+M+m+L+s+T+j-t)) :
    j+1≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) := by
  by_cases hgood : j+1≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)
  · exact hgood
  · exfalso
    have hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1 := by omega
    have hr := Recaman.OldTargetAreaBudget.old_target_counterexample_band f n t h M m L s T j w hw hpre ht hs
      hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad hwin
    let B2 := h+M+m+L
    let B := B2+s
    let P := fun x => f x=true ∧ ¬EndN f 0 x
    let v := List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false
    have hv : seg f n B=v := by
      have hh := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0
        hS hA hS2 hA2 hS3 (by intro i hi; omega)
      simpa only [Nat.add_zero,List.replicate_zero,List.append_nil] using hh
    have hshape := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
    have hword : seg f n (h+M+m+L+s+T+j)=v++List.replicate T true++List.replicate j false := by
      rw [seg_add,show n+(h+M+m+L+s+T)=n+h+M+m+L+s+T by omega,
        seg_false f (n+h+M+m+L+s+T) j hgap,hshape]
      simp only [v,List.append_assoc]
    have ho := Recaman.OldTargetAreaBudget.actual_old_target_budget f n t h M m L s T j w hw hpre ht
      (by simpa only [v,List.append_assoc] using hword) hwin
    have hc10 := Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s T w hw hpre hs
      (by omega) hS hA hS2 hA2 hS3 hA3 hpos
    have hones := ones_seg_eq_count f n (h+M+m+L+s+T)
    rw [hshape] at hones
    simp only [ones_append,ones_replicate_S,ones_replicate_A] at hones
    have hpartall := addition_endable_partition f n (h+M+m+L+s+T)
    have hbudget : M+L+T≤j+10 := by omega
    have hlen : w.length=n := by rw [←hpre,seg_length]
    have hd := seg_drop f 0 n t (by omega)
    simp only [Nat.zero_add] at hd
    rw [hpre] at hd
    have htarget : seg f t (n-t+(B+T+j))=w.drop t++v++List.replicate T true++List.replicate j false := by
      rw [seg_add,show t+(n-t)=n by omega,←hd]
      have hh : seg f n (B+T+j)=v++List.replicate T true++List.replicate j false := hword
      rw [hh]
      simp only [List.append_assoc]
    have hwin' : Win f t (n+B+T+j-t) := by simpa only [B,B2,Nat.add_assoc] using hwin
    have hmass : mass (w.drop t++v++List.replicate T true++List.replicate j false)=1 := by
      rw [←htarget,seg_mass]
      have hh := hwin'.2.1
      rw [show t+(n+B+T+j-t)=n+B+T+j by omega] at hh
      rw [show t+(n-t+(B+T+j))=n+B+T+j by omega]
      omega
    have harea : areaW (w.drop t++v++List.replicate T true++List.replicate j false)=0 := by
      rw [←htarget,←Ar_areaW]
      have hh : n-t+(B+T+j)=n+B+T+j-t := by omega
      rw [hh]
      exact hwin'.2.2
    have hpre3 : seg f 0 (n+B)=w++v := by
      rw [seg_add,show 0+n=n by omega,hpre,hv]
    have hA3' : ∀ i, i<T → f (n+B+i)=true := by
      intro i hi
      simpa only [B,B2,Nat.add_assoc] using hA3 i hi
    have hrun := endable_A_run_count f (n+B) T (w++v) hpre3 hA3'
    have hp3 := addition_endable_partition f (n+B) T
    rw [count_A_run f (n+B) T hA3',hrun] at hp3
    have hhead := Recaman.ThreeRunSupplyBudget.two_run_additions_free_bound f n h M m L w hw hpre
      hS hA hS2 hA2 (by intro k hk hkB; exact hpos k hk (by omega))
    have hsupply := Recaman.ThreeRunSupplyBudget.two_run_supply_of_positive f n h M m L w hw hpre
      hS hA hS2 hA2 (by intro hk; exact hpos _ hk (by omega))
    have hheadword := Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0
      hS hA hS2 hA2 (by intro x hx hx0; omega) (by intro i hi; omega)
    have hheadones := ones_seg_eq_count f n (h+M+m+L)
    have hheadword' : seg f n (h+M+m+L)=List.replicate h false++List.replicate M true++
        List.replicate m false++List.replicate L true := by simpa using hheadword
    rw [hheadword'] at hheadones
    simp only [ones_append,ones_replicate_S,ones_replicate_A] at hheadones
    have hheadpart := addition_endable_partition f n (h+M+m+L)
    have hhead2 : M+L≤2*cN P n B2+1 := by dsimp [P,B2]; omega
    have hhead5 : M+L≤cN P n B2+5 := by dsimp [P,B2]; omega
    have hz : cN P (n+B2) s=0 := by
      apply cN_zero_of
      intro x hx hxs hh
      have hf := hS3 x (by dsimp [B2] at hx; omega) (by dsimp [B2] at hxs; omega)
      exact Bool.noConfusion (hh.1.symm.trans hf)
    have hsplit1 := cN_add P n B2 s
    have hsplit2 := cN_add P n B T
    have hF : cN P n (B+T)=cN P n B2+cN P (n+B) T := by
      change cN P n (B2+s)=cN P n B2+cN P (n+B2) s at hsplit1
      rw [hz] at hsplit1
      change cN P n (B+T)=cN P n B+cN P (n+B) T at hsplit2
      omega
    have hp := old_target_count_charge w hw t h M m L s T j (cN P n B2) (cN P (n+B) T)
      (by omega) hr.2.2.2.1 hm hL hs hM hbudget ho.2.2.2.2
      (by simpa only [v,List.append_assoc] using hmass)
      (by simpa only [v,List.append_assoc] using harea) hhead2 hhead5
      (by simpa only [P,v,List.append_assoc] using Nat.le_of_eq hp3)
    change cN P n (B+T)<j+1 at hbad
    omega

end Recaman.OldTargetMiddleCharge
