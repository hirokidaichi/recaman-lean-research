import Recaman.OldReturnOneBelow
import Recaman.OldSameLevelReturnCount

namespace Recaman.OldReturnNearFloorCount

open Recaman.OldReturnOneBelow Recaman.OldSameLevelReturnCount
open Recaman.RunSupplyBudget Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction Recaman.InitialSPaddingPositive

private theorem shifted_count (P : Nat → Prop) (s : Nat) :
    ∀ K, cN P s K = cN (fun i => P (s+i)) 0 K
  | 0 => rfl
  | K+1 => by
    by_cases h : P (s+K)
    · rw [cN_succ_pos P s K h,cN_succ_pos _ 0 K (by simpa only [Nat.zero_add] using h),
        shifted_count P s K]
    · rw [cN_succ_neg P s K h,cN_succ_neg _ 0 K (by simpa only [Nat.zero_add] using h),
        shifted_count P s K]

theorem count_le_two_of_no_ordered_triple (P : Nat → Prop) (s K : Nat)
    (h : ∀ b c d, s≤b → b<c → c<d → d<s+K → P b → P c → P d → False) :
    cN P s K≤2 := by
  induction K with
  | zero => simp [cN]
  | succ k ih =>
    by_cases hp : P (s+k)
    · have hu : cN P s k≤1 := by
        rw [shifted_count]
        apply cN_le_one_of_unique
        intro i hi j hj hpi hpj
        rcases Nat.lt_trichotomy i j with hlt | heq | hgt
        · exact (h (s+i) (s+j) (s+k) (by omega) (by omega) (by omega)
            (by omega) hpi hpj hp).elim
        · exact heq
        · exact (h (s+j) (s+i) (s+k) (by omega) (by omega) (by omega)
            (by omega) hpj hpi hp).elim
      rw [cN_succ_pos P s k hp]
      omega
    · rw [cN_succ_neg P s k hp]
      exact ih (fun b c d hsb hbc hcd hd hpb hpc hpd =>
        h b c d hsb hbc hcd (by omega) hpb hpc hpd)

/-- Three actual old suppliers at one height need a dip of at least two.
The middle endpoint would otherwise be a subtraction in the outer ASSA. -/
theorem three_old_need_dip (f : Nat → Bool) (n a b c d : Nat) (H : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n≤b) (hbc : b<c) (hcd : c<d)
    (hb : Fw f b=H ∧ f b=true ∧ ∃ u, u<n ∧ Win f u (b-u))
    (hc : Fw f c=H ∧ f c=true ∧ ∃ u, u<n ∧ Win f u (c-u))
    (hd : Fw f d=H ∧ f d=true ∧ ∃ u, u<n ∧ Win f u (d-u)) :
    ∃ i, b≤i ∧ i≤d ∧ Fw f i≤H-2 := by
  by_cases hdip : ∃ i, b≤i ∧ i≤d ∧ Fw f i≤H-2
  · exact hdip
  · have hf (i : Nat) (hi : b≤i) (hid : i≤d) : H-1≤Fw f i := by
      by_cases hh : H-1≤Fw f i
      · exact hh
      · exact (hdip ⟨i,hi,hid,by omega⟩).elim
    obtain ⟨hbH,hbA,u,hu,huW⟩ := hb
    obtain ⟨hcH,hcA,v,hv,hvW⟩ := hc
    obtain ⟨hdH,_,z,hz,hzW⟩ := hd
    have hbcd := old_return_gap_one_below f n a u z b d hw hpre hu hz hnb
      (by omega) huW hzW (hbH.trans hdH.symm) hbA
      (fun i hi => by rw [hbH]; exact hf _ (by omega) (by omega))
    have hbcg := old_return_gap_one_below f n a u v b c hw hpre hu hv hnb
      hbc huW hvW (hbH.trans hcH.symm) hbA
      (fun i hi => by rw [hbH]; exact hf _ (by omega) (by omega))
    have hcdg := old_return_gap_one_below f n a v z c d hw hpre hv hz (by omega)
      hcd hvW hzW (hcH.trans hdH.symm) hcA
      (fun i hi => by rw [hcH]; exact hf _ (by omega) (by omega))
    rcases hbcd with hh | ⟨h4,_,hS,_⟩
    · rcases hbcg with hh' | ⟨hh',_,_,_⟩ <;> omega
    · have hc2 : c=b+2 := by
        rcases hbcg with hh | ⟨hh,_,_,_⟩ <;> omega
      rw [hc2,hS] at hcA
      cases hcA

/-- The height-count bound remains two when the interval may go one step
below the height of the counted endpoints. -/
theorem old_supplies_near_floor_le_two (f : Nat → Bool) (n a s K : Nat) (H : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hns : n≤s) (hfloor : ∀ t, s≤t → t<s+K → H-1≤Fw f t) :
    cN (fun t => Fw f t=H ∧ f t=true ∧ ∃ u, u<n ∧ Win f u (t-u)) s K≤2 := by
  apply count_le_two_of_no_ordered_triple
  intro b c d hsb hbc hcd hd hb hc he
  obtain ⟨i,hib,hid,hlo⟩ := three_old_need_dip f n a b c d H hw hpre (by omega) hbc hcd hb hc he
  have hhi := hfloor i (by omega) (by omega)
  omega

private def forwardWord : List Bool :=
  [true,true]++tripW++List.replicate 6 false++[true]++List.replicate 8 false++
    List.replicate 8 true++[true,false,false,true]

private def reverseWord : List Bool :=
  tripW++List.replicate 2 false++[true]++List.replicate 8 false++
    List.replicate 6 true++[true,false,false,true]

/-- The four-clock boundary occurs with each ordering of the original
old starts. Both histories are checked with actual windows. -/
theorem one_below_order_boundaries :
    let f := finiteSign forwardWord
    let g := finiteSign reverseWord
    BlockWord (seg f 0 12) ∧ Win f 0 35 ∧ Win f 4 35 ∧
      Fw f 35=Fw f 39 ∧ seg f 35 4=[true,false,false,true] ∧ f 39=true ∧
    BlockWord (seg g 0 10) ∧ Win g 4 23 ∧ Win g 0 31 ∧
      Fw g 27=Fw g 31 ∧ seg g 27 4=[true,false,false,true] ∧ g 31=true := by
  dsimp only
  have hf : seg (finiteSign forwardWord) 0 12=[true,true]++tripW := by decide
  have hg : seg (finiteSign reverseWord) 0 10=tripW := by decide
  refine ⟨?_,by unfold Win; decide,by unfold Win; decide,by decide,by decide,by decide,
    ?_,by unfold Win; decide,by unfold Win; decide,by decide,by decide,by decide⟩
  · rw [hf]
    exact block_append (BlockWord.free (BlockWord.free BlockWord.nil)) (BlockWord.triple BlockWord.nil)
  · rw [hg]
    exact BlockWord.triple BlockWord.nil

end Recaman.OldReturnNearFloorCount
