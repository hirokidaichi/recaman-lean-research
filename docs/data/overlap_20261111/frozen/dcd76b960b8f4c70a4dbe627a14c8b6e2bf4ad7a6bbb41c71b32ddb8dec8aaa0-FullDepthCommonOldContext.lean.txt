import Recaman.OldWindowLocalReplacement
import Recaman.InitialSPaddingPositive

namespace Recaman.FullDepthCommonOldContext

open Recaman.OldWindowLocalReplacement Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction Recaman.LeadingRunSupply
open Recaman.InitialSPaddingPositive

/-- When the full tail stays within depth D, every original supply can
use a local start or an old start of mass at most D-2. -/
theorem full_floor_supply_origin (f : Nat → Bool) (n a b D : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n≤b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-(D : Int)≤Fw f i)
    (he : EndN f 0 b) :
    ∃ t, t<b ∧ Win f t (b-t) ∧ (n≤t ∨ Fw f n-Fw f t+2≤(D : Int)) := by
  obtain ⟨_,t,k,_,htk,hwin⟩ := he
  have hlt : t<b := by have := hwin.1; omega
  have hw' : Win f t (b-t) := by
    rw [show b-t=k by omega]
    exact hwin
  by_cases h : n≤t ∨ Fw f n-Fw f t+2≤(D : Int)
  · exact ⟨t,hlt,hw',h⟩
  · have ht : t<n := by
      by_cases hnt : n≤t
      · exact (h (Or.inl hnt)).elim
      · omega
    have hc : (D : Int)≤Fw f n-Fw f t+1 := by
      by_cases hc : Fw f n-Fw f t+2≤(D : Int)
      · exact (h (Or.inr hc)).elim
      · omega
    have hf (i : Nat) (hni : n≤i) (hib : i≤b) : Fw f t-1≤Fw f i := by
      have hh := hfloor i hni hib
      omega
    obtain ⟨u,hnu,hub,hu⟩ := replace_old_window_at_one_below f n a t b hw hpre ht hnb hw' hf
    exact ⟨u,hub,hu,Or.inl hnu⟩

/-- At full depth two, retaining only starts at or after the original
block boundary preserves the actual supply predicate. -/
theorem endable_at_full_depth_two (f : Nat → Bool) (n a b : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n≤b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-2≤Fw f i) :
    EndN f 0 b ↔ EndN f n b := by
  constructor
  · intro he
    obtain ⟨t,ht,hW,h⟩ := full_floor_supply_origin f n a b 2 hw hpre hnb hfloor he
    have hnt : n≤t := by
      by_cases htn : t<n
      · have hp := (block_suffix_positive_walk f 0 n a hw hpre t (Nat.zero_le _) (by omega)).1
        simp only [Nat.zero_add] at hp
        rcases h with hh | hh <;> omega
      · omega
    exact ⟨he.1,t,b-t,hnt,by omega,hW⟩
  · exact end_mono f 0 n b (Nat.zero_le _)

/-- A single old context from four explicit block suffixes preserves every
actual endpoint whose full preceding tail stays within depth four. -/
theorem full_depth_four_common_context (f : Nat → Bool) (n a : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true) :
    ∃ r ∈ [[],[true],[true,true],aasW], r.IsSuffix (seg f 0 n) ∧
      ∀ b, n≤b → (∀ i, n≤i → i≤b → Fw f n-4≤Fw f i) →
        (EndN f 0 b ↔ EndN f (n-r.length) b) := by
  obtain ⟨r,hr,hrs,hrep⟩ := finite_suffix_representative [[true],[true,true],aasW] (seg f 0 n)
  refine ⟨r,hr,hrs,?_⟩
  intro b hnb hfloor
  constructor
  · intro he
    obtain ⟨t,ht,hW,hSource⟩ := full_floor_supply_origin f n a b 4 hw hpre hnb hfloor he
    have hnt : n-r.length≤t := by
      by_cases htn : t<n
      · have hFull : BlockWord (seg f 0 n) := by
          rw [hpre]
          exact block_append hw (block_replicate_A a)
        have hsplit := suffix_split f 0 n t (Nat.zero_le _) (by omega)
        simp only [Nat.zero_add,Nat.sub_zero] at hsplit
        have hb := block_suffix hFull (seg f 0 t) (seg f t (n-t)) hsplit.symm
        have hS : (seg f t (n-t)).IsSuffix (seg f 0 n) := ⟨seg f 0 t,hsplit.symm⟩
        have hm := seg_mass f t (n-t)
        rw [show t+(n-t)=n by omega] at hm
        have hp := (block_suffix_positive_walk f 0 n a hw hpre t (Nat.zero_le _) (by omega)).1
        simp only [Nat.zero_add] at hp
        have hmem : seg f t (n-t) ∈ [[true],[true,true],aasW] := by
          by_cases h1 : mass (seg f t (n-t))=1
          · rw [block_mass_one hb h1]
            decide
          · have h2 : mass (seg f t (n-t))=2 := by
              rcases hSource with hh | hh <;> omega
            rcases block_mass_two hb h2 with h | h <;> rw [h] <;> decide
        have hlen := List.IsSuffix.length_le ((hrep _ hmem).mp hS)
        rw [seg_length] at hlen
        omega
      · omega
    exact ⟨he.1,t,b-t,hnt,by omega,hW⟩
  · exact end_mono f 0 (n-r.length) b (Nat.zero_le _)

private def sharpWord : List Bool := aasW++List.replicate 4 false++List.replicate 3 true

/-- Four old clocks can genuinely be required. The same full depth-four
history has a window at start zero and none starting from one or later. -/
theorem depth_four_old_context_sharp :
    let f := finiteSign sharpWord
    BlockWord (seg f 0 4) ∧ EndN f 0 11 ∧ ¬EndN f 1 11 ∧
      ∀ i, 4≤i → i≤11 → Fw f 4-4≤Fw f i := by
  dsimp only
  have hs : seg (finiteSign sharpWord) 0 4=aasW := by decide
  refine ⟨?_,⟨by decide,0,11,by decide,by decide,by unfold Win; decide⟩,?_,?_⟩
  · rw [hs]
    exact BlockWord.aas BlockWord.nil
  · intro h
    have hlocal := (localSupply_seg_iff (finiteSign sharpWord) 1 11 (by decide) (by decide)).mpr h
    have hn : Recaman.ThreeNonsuppliedData.localSupply (seg (finiteSign sharpWord) 1 (11-1))=false := by decide
    rw [hn] at hlocal
    cases hlocal
  · intro i hi hj
    have hcases : i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 := by omega
    rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

end Recaman.FullDepthCommonOldContext
