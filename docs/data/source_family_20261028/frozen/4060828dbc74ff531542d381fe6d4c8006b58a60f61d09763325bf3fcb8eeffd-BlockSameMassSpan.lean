import Recaman.BlockSuffixSpectrum

namespace Recaman.BlockSameMassSpan

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay Recaman.RunSupplyKeys
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private def atoms : List (List Bool) := [[true],aasW,tripW]
private def smalls : List (List Bool) := [[],[true],[true,true],aasW]

private theorem low_mass_word {w : List Bool} (hw : BlockWord w) (hm : mass w≤2) : w∈smalls := by
  by_cases hz : w=[]
  · rw [hz]; decide
  · have hp := (sufPos_block hw [] w rfl hz).1
    by_cases h1 : mass w=1
    · rw [block_mass_one hw h1]; decide
    · have h2 : mass w=2 := by omega
      rcases block_mass_two hw h2 with hAA|hSA
      · rw [hAA]; decide
      · rw [hSA]; decide

private theorem atom_prefix_low (B : List Bool) (hB : B∈atoms) (k : Nat) : -2≤mass (B.take k) := by
  have hc : atoms.all (fun B => (List.range (B.length+1)).all
      (fun k => decide (-2≤mass (B.take k))))=true := by decide
  have get (q : Nat) (hq : q≤B.length) : -2≤mass (B.take q) := by
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hc B hB) q
      (List.mem_range.mpr (by omega)))
  by_cases hk : k≤B.length
  · exact get k hk
  · have h := get B.length (Nat.le_refl _)
    rw [List.take_of_length_le (Nat.le_refl _)] at h
    rw [List.take_of_length_le (by omega)]
    exact h

private theorem small_zero_control (w B : List Bool) (hw : w∈smalls) (hB : B∈atoms) (k : Nat)
    (hm : mass (w++B.take k)=0) :
    (w++B.take k).length≤6 ∧ -4≤areaW (w++B.take k) ∧ areaW (w++B.take k)≤4 := by
  have hc : smalls.all (fun w => atoms.all (fun B => (List.range (B.length+1)).all
      (fun k => decide (mass (w++B.take k)=0 →
        (w++B.take k).length≤6 ∧ -4≤areaW (w++B.take k) ∧ areaW (w++B.take k)≤4))))=true := by decide
  have get (q : Nat) (hq : q≤B.length) : mass (w++B.take q)=0 →
      (w++B.take q).length≤6 ∧ -4≤areaW (w++B.take q) ∧ areaW (w++B.take q)≤4 := by
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hc w hw) B hB) q
      (List.mem_range.mpr (by omega)))
  by_cases hk : k≤B.length
  · exact get k hk hm
  · have h := get B.length (Nat.le_refl _)
    rw [List.take_of_length_le (Nat.le_refl _)] at h
    rw [List.take_of_length_le (by omega)] at hm ⊢
    exact h hm

private theorem append_zero_prefix (w B : List Bool) (hw : BlockWord w) (hB : B∈atoms)
    (ih : ∀ k, mass (w.take k)=0 →
      (w.take k).length≤6 ∧ -4≤areaW (w.take k) ∧ areaW (w.take k)≤4)
    (k : Nat) (hm : mass ((w++B).take k)=0) :
    ((w++B).take k).length≤6 ∧ -4≤areaW ((w++B).take k) ∧ areaW ((w++B).take k)≤4 := by
  by_cases hk : k≤w.length
  · rw [List.take_append_of_le_length hk] at hm ⊢
    exact ih k hm
  · rw [List.take_append,List.take_of_length_le (by omega)] at hm ⊢
    have hv := atom_prefix_low B hB (k-w.length)
    have hw2 : mass w≤2 := by rw [mass_append] at hm; omega
    exact small_zero_control w B (low_mass_word hw hw2) hB (k-w.length) hm

/-- A zero-mass prefix of any BlockWord is short and has bounded area.
All atom counts and all history lengths are unrestricted. -/
theorem block_zero_mass_prefix (w : List Bool) (hw : BlockWord w) :
    ∀ k, mass (w.take k)=0 →
      (w.take k).length≤6 ∧ -4≤areaW (w.take k) ∧ areaW (w.take k)≤4 := by
  induction hw with
  | nil => intro k _; simp [areaW]
  | free hw ih => exact append_zero_prefix _ _ hw (by simp [atoms,aasW,tripW]) ih
  | aas hw ih => exact append_zero_prefix _ _ hw (by simp [atoms,aasW,tripW]) ih
  | triple hw ih => exact append_zero_prefix _ _ hw (by simp [atoms,aasW,tripW]) ih

private theorem ordered_suffix_bound (w : List Bool) (hw : BlockWord w) (t u : Nat)
    (htu : t≤u) (hu : u<w.length) (hm : mass (w.drop t)=mass (w.drop u)) :
    u-t≤6 ∧ -4≤areaW (w.drop t)-areaW (w.drop u) ∧
      areaW (w.drop t)-areaW (w.drop u)≤4 := by
  have hbt := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have he := List.take_append_drop (u-t) (w.drop t)
  rw [List.drop_drop,show t+(u-t)=u by omega] at he
  have hmass := mass_append ((w.drop t).take (u-t)) (w.drop u)
  rw [he] at hmass
  have hz : mass ((w.drop t).take (u-t))=0 := by omega
  have hb := block_zero_mass_prefix (w.drop t) hbt (u-t) hz
  have hl : ((w.drop t).take (u-t)).length=u-t := by
    simp only [List.length_take,List.length_drop]
    omega
  have ha := areaW_append ((w.drop t).take (u-t)) (w.drop u)
  rw [he,hz,Int.mul_zero,Int.add_zero] at ha
  rw [hl] at hb
  omega

/-- Same-mass old sources from one prefix lie within six clocks and their
required areas differ by at most four. Different-prefix spectra are not
combined here, and the mass itself has no fixed upper bound. -/
theorem block_same_mass_suffixes (w : List Bool) (hw : BlockWord w) (t u : Nat)
    (ht : t<w.length) (hu : u<w.length) (hm : mass (w.drop t)=mass (w.drop u)) :
    t≤u+6 ∧ u≤t+6 ∧ -4≤areaW (w.drop t)-areaW (w.drop u) ∧
      areaW (w.drop t)-areaW (w.drop u)≤4 := by
  by_cases htu : t≤u
  · have h := ordered_suffix_bound w hw t u htu hu hm
    omega
  · have h := ordered_suffix_bound w hw u t (by omega) ht hm.symm
    omega

/-- The existing trip example reaches area spread four; it is retained,
not cut by a stronger and false spread-three filter. -/
theorem trip_area_spread_boundary :
    BlockWord tripW ∧ mass tripW=mass (tripW.drop 4) ∧
      areaW tripW-areaW (tripW.drop 4) = -4 := by
  refine ⟨BlockWord.triple BlockWord.nil,?_,?_⟩ <;> decide

/-- A six-clock zero-mass prefix is attained, so the source radius is not
silently strengthened to five. -/
theorem six_clock_span_boundary :
    BlockWord (aasW++tripW) ∧
    mass (aasW++tripW)=mass ((aasW++tripW).drop 6) ∧
    (aasW++tripW).length>6 := by
  refine ⟨block_append (BlockWord.aas BlockWord.nil) (BlockWord.triple BlockWord.nil),?_,?_⟩ <;> decide

/-- Two actual old windows ending at the same level must demand old areas
within four of each other. All possible old masses are included. -/
theorem same_level_old_window_areas (f : Nat → Bool) (n a t u b c : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (ht : t<n) (hu : u<n) (hnb : n≤b) (hnc : n≤c)
    (hwb : Win f t (b-t)) (hwc : Win f u (c-u)) (hlevel : Fw f b=Fw f c) :
    t≤u+6 ∧ u≤t+6 ∧
    -4≤(Ar f n (b-n)+((b-n : Nat) : Int)*(Fw f n-Fw f b+1))-
        (Ar f n (c-n)+((c-n : Nat) : Int)*(Fw f n-Fw f c+1)) ∧
    (Ar f n (b-n)+((b-n : Nat) : Int)*(Fw f n-Fw f b+1))-
        (Ar f n (c-n)+((c-n : Nat) : Int)*(Fw f n-Fw f c+1))≤4 := by
  have hfull : BlockWord (seg f 0 n) := by
    rw [hpre]
    exact block_append hw (block_replicate_A a)
  have hft := hwb.2.1
  have hfu := hwc.2.1
  rw [show t+(b-t)=b by omega] at hft
  rw [show u+(c-u)=c by omega] at hfu
  have hdropT : (seg f 0 n).drop t=seg f t (n-t) := by
    simpa only [Nat.zero_add] using seg_drop f 0 n t (by omega)
  have hdropU : (seg f 0 n).drop u=seg f u (n-u) := by
    simpa only [Nat.zero_add] using seg_drop f 0 n u (by omega)
  have hm : mass ((seg f 0 n).drop t)=mass ((seg f 0 n).drop u) := by
    rw [hdropT,hdropU,seg_mass,seg_mass,show t+(n-t)=n by omega,show u+(n-u)=n by omega]
    omega
  have hb := block_same_mass_suffixes (seg f 0 n) hfull t u
    (by simpa only [seg_length] using ht) (by simpa only [seg_length] using hu) hm
  rw [hdropT,hdropU,←Ar_areaW,←Ar_areaW] at hb
  have hsplitb := area_split_at f t n b (by omega) hnb
  have hsplitc := area_split_at f u n c (by omega) hnc
  have hR1 : Fw f n-Fw f t=Fw f n-Fw f b+1 := by omega
  have hR2 : Fw f n-Fw f u=Fw f n-Fw f c+1 := by omega
  rw [hR1] at hsplitb
  rw [hR2] at hsplitc
  have hz1 := hwb.2.2
  have hz2 := hwc.2.2
  omega

end Recaman.BlockSameMassSpan
