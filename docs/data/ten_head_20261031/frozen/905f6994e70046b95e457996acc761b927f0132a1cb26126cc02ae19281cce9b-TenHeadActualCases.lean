import Recaman.TenHeadTargetCases
import Recaman.OldSourceKeyOrder

namespace Recaman.TenHeadActualCases

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.TenHeadTargetCases Recaman.MomentBandOldClock Recaman.OldSourceKeyOrder

/-- Ten actual A signs under the original relative positivity force at
least four actual free signs, using the existing kernel-checked r3 bound. -/
theorem ten_head_free_four (f : Nat → Bool) (n : Nat) (w z : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hz : seg f n 20=z)
    (hm : mass z=0) (hS : cntF z=10)
    (hpos : ∀ k, 0<k → k≤20 → cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    4≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n 20 := by
  have hlen : z.length=20 := by rw [←hz,seg_length]
  have hones : ones z=10 := by have h:=mass_eq z; rw [hm,hlen] at h; omega
  have hA10 : cN (fun x=>f x=true) n 20=10 := by
    have h:=ones_seg_eq_count f n 20
    rw [hz,hones] at h
    omega
  by_cases hh : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n 20≤3
  · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
    have hb:=positive_r3_additions_free_bound f n 0 20 hw hpre0 hpos hh
    rw [hA10] at hb
    omega
  · omega

private theorem window_profile (f : Nat → Bool) (s l : Nat) (hw : Win f s l) :
    mass (seg f s l)=1 ∧ areaW (seg f s l)=0 := by
  refine ⟨?_,?_⟩
  · rw [seg_mass]
    have hm:=hw.2.1
    omega
  · rw [←Ar_areaW]
    exact hw.2.2

/-- A hypothetical actual counterexample supplies R>=5 and the two raw
cases internally. The source is a suffix of the unchanged whole prefix. -/
theorem actual_ten_head_target_cases (f : Nat → Bool) (n t v T j q i : Nat) (w z : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n) (hz : seg f n 20=z)
    (hmz : mass z=0) (hSz : cntF z=10) (B : Int) (haz : areaW z= -B)
    (hlo : 46≤B) (hhi : B≤64) (hv : 1≤v) (hq : 1≤q) (hqv : q≤v)
    (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n+20≤x → x<n+20+v → f x=false)
    (hA : ∀ k, k<T → f (n+20+v+k)=true)
    (hgap : ∀ x, n+20+v+T≤x → x<n+20+v+T+j → f x=false)
    (htarget : Win f t (n+20+v+T+j-t))
    (hlocal : Win f (n+20+v-q) (q+i))
    (hpos : ∀ k, 0<k → k≤20+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hcounter : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (20+v+T)<j+1) :
    w.drop t=[true] ∧ q=1 ∧ i=2 ∧
      ((v=1 ∧ T=5 ∧ j=4 ∧ B=46) ∨ (v=2 ∧ T=7 ∧ j=5 ∧ B=56)) := by
  have hF4:=ten_head_free_four f n w z hw hpre hz hmz hSz
    (fun k hk hk20=>hpos k hk (by omega))
  have hadd:=cN_add (fun x=>f x=true ∧ ¬EndN f 0 x) n 20 (v+T)
  have hR : 5≤j+1 := by omega
  have hn : w.length=n := by rw [←hpre,seg_length]
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hne : w.drop t≠[] := by
    intro he
    have hl : (w.drop t).length=w.length-t := List.length_drop
    rw [he,hn] at hl
    simp only [List.length_nil] at hl
    omega
  have hd:=seg_drop f 0 n t (by omega)
  simp only [Nat.zero_add,hpre] at hd
  have hfull : seg f t (n+20+v+T+j-t)=w.drop t++z++List.replicate v false++
      List.replicate T true++List.replicate j false := by
    rw [show n+20+v+T+j-t=(n-t)+(20+v+T+j) by omega,seg_add,
      show t+(n-t)=n by omega,←hd,seg_add,seg_add,seg_add,hz,
      seg_false f (n+20) v hS]
    have hAt : seg f (n+(20+v)) T=List.replicate T true := by
      apply seg_A
      intro x hx hxT
      have hh:=hA (x-(n+20+v)) (by omega)
      rw [show n+20+v+(x-(n+20+v))=x by omega] at hh
      exact hh
    rw [hAt]
    have hSt : seg f (n+(20+v+T)) j=List.replicate j false := by
      apply seg_false
      intro x hx hxj
      exact hgap x (by omega) (by omega)
    rw [hSt]
    simp only [List.append_assoc]
  have hloc : seg f (n+20+v-q) (q+i)=List.replicate q false++List.replicate i true := by
    rw [seg_add,show n+20+v-q+q=n+20+v by omega]
    have hs : seg f (n+20+v-q) q=List.replicate q false := by
      apply seg_false
      intro x hx hxq
      exact hS x (by omega) (by omega)
    have ha : seg f (n+20+v) i=List.replicate i true := by
      apply seg_A
      intro x hx hxi
      have hh:=hA (x-(n+20+v)) (by omega)
      rw [show n+20+v+(x-(n+20+v))=x by omega] at hh
      exact hh
    rw [hs,ha]
  obtain ⟨hm,ha⟩:=window_profile f t _ htarget
  obtain ⟨hlm,hla⟩:=window_profile f (n+20+v-q) _ hlocal
  rw [hfull] at hm ha
  rw [hloc] at hlm hla
  exact ten_head_target_cases (w.drop t) z hu hne B hmz hSz haz hlo hhi v T j q i hv hq hqv hi hband hR hm ha hlm hla

/-- The same target and the moment band exclude EVERY original old
supplier on the last A ray in either target-derived case. -/
theorem actual_two_cases_no_old (f : Nat → Bool) (n t v T j : Nat) (w z : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n) (hz : seg f n 20=z)
    (hmz : mass z=0) (hSz : cntF z=10) (B : Int) (haz : areaW z= -B)
    (hlo : 46≤B) (hhi : B≤64)
    (hc : (v=1 ∧ T=5 ∧ j=4) ∨ (v=2 ∧ T=7 ∧ j=5))
    (hS : ∀ x, n+20≤x → x<n+20+v → f x=false)
    (hA : ∀ k, k<T → f (n+20+v+k)=true)
    (hgap : ∀ x, n+20+v+T≤x → x<n+20+v+T+j → f x=false)
    (htarget : Win f t (n+20+v+T+j-t)) :
    ∀ k, k<T → ∀ s, s<n → ¬Win f s (n+20+v+k-s) := by
  intro k hk s hs hwin
  have hv : 1≤v := by rcases hc with h|h <;> omega
  have hclock:=actual_moment_band_old_clock f n (n+20) s v k w z hw hpre
    (by omega) hs (by simpa using hz) B hmz haz (by rw [hSz]; omega) (by rw [hSz]; omega)
    hv hS (fun l hl=>hA l (by omega)) hwin
  have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have horder:=actual_old_target_prior_clock f n s t (20+v) k T j hw' hs ht
    (by omega) (by rcases hc with h|h <;> omega)
    (by simpa only [Nat.add_assoc] using hA)
    (by simpa only [Nat.add_assoc] using hgap)
    (by simpa only [Nat.add_assoc] using hwin)
    (by simpa only [Nat.add_assoc] using htarget)
  rcases hc with h|h <;> omega

end Recaman.TenHeadActualCases
