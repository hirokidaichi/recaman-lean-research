import Recaman.OldTargetMassFive
import Recaman.BlockSameMassSpan

namespace Recaman.OldSourceKeyOrder

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.BlockSameMassSpan Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem prefix_difference (w : List Bool) (hw : BlockWord w) (k : Nat) (v : List Bool) :
    (0≤mass (w.take k) → -8≤runKey (w.take k++v)-runKey v) ∧
    (mass (w.take k)≤0 → runKey (w.take k++v)-runKey v≤8) := by
  have hb := block_prefix_key_bounds hw k
  rw [runKey_append]
  constructor
  · intro hm
    have hp := Int.mul_nonneg hm (show 0≤(cntF v : Int) by omega)
    grind
  · intro hm
    by_cases hz : mass (w.take k)=0
    · have ha := block_zero_mass_prefix w hw k hz
      unfold runKey
      rw [hz]
      omega
    · have hk := hb.2 (by omega)
      have hp := Int.mul_nonpos_of_nonpos_of_nonneg hm (show 0≤(cntF v : Int) by omega)
      grind

/-- Both sources are suffixes of one BlockWord; arbitrary independent
mass/area signatures do not satisfy this implication. -/
theorem old_key_mass_order (w v : List Bool) (hw : BlockWord w) (t s : Nat)
    (hkey : runKey (w.drop s++v)+9≤runKey (w.drop t++v)) :
    mass (w.drop s)<mass (w.drop t) := by
  by_cases hts : t≤s
  · have hbt := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
    have he := List.take_append_drop (s-t) (w.drop t)
    rw [List.drop_drop,show t+(s-t)=s by omega] at he
    have hm := mass_append ((w.drop t).take (s-t)) (w.drop s)
    rw [he] at hm
    have hd := (prefix_difference (w.drop t) hbt (s-t) (w.drop s++v)).2
    have hsplit : w.drop t++v=(w.drop t).take (s-t)++(w.drop s++v) := by
      rw [←List.append_assoc,he]
    rw [hsplit] at hkey
    by_cases hh : mass (w.drop s)<mass (w.drop t)
    · exact hh
    · have hb := hd (by omega)
      omega
  · have hbs := block_suffix hw (w.take s) (w.drop s) (List.take_append_drop s w)
    have he := List.take_append_drop (t-s) (w.drop s)
    rw [List.drop_drop,show s+(t-s)=t by omega] at he
    have hm := mass_append ((w.drop s).take (t-s)) (w.drop t)
    rw [he] at hm
    have hd := (prefix_difference (w.drop s) hbs (t-s) (w.drop t++v)).1
    have hsplit : w.drop s++v=(w.drop s).take (t-s)++(w.drop t++v) := by
      rw [←List.append_assoc,he]
    rw [hsplit] at hkey
    by_cases hh : mass (w.drop s)<mass (w.drop t)
    · exact hh
    · have hb := hd (by omega)
      omega

/-- An old source supplying the earlier A ray must precede the last j
A clocks if another old source supplies the endpoint after j S signs.
All old histories and the common internal word are unrestricted. -/
theorem old_target_prior_clock (w v : List Bool) (hw : BlockWord w) (t s i T j : Nat)
    (hj : 2≤j)
    (hm1 : mass (w.drop t++v++List.replicate i true)=1)
    (ha1 : areaW (w.drop t++v++List.replicate i true)=0)
    (hm2 : mass (w.drop s++v++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (w.drop s++v++List.replicate T true++List.replicate j false)=0) :
    mass (w.drop s)<mass (w.drop t) ∧ i+j<T := by
  have hk1 := source_key_before_gap (w.drop t++v) i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [List.replicate_zero,List.append_nil] using ha1)
  have hk2 := source_key_before_gap (w.drop s++v) T j hm2 ha2
  have hp := Int.mul_nonneg (show 0≤(j : Int)-2 by omega) (show 0≤(j : Int)+4 by omega)
  have hkey : runKey (w.drop s++v)+9≤runKey (w.drop t++v) := by grind
  have hm := old_key_mass_order w v hw t s hkey
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hm1 hm2
  exact ⟨hm,by omega⟩

private theorem source_splice (f : Nat → Bool) (n t B K : Nat) (ht : t≤n) :
    seg f t (n-t+B+K)=(seg f 0 n).drop t++seg f n B++seg f (n+B) K := by
  have hd : (seg f 0 n).drop t=seg f t (n-t) := by
    simpa only [Nat.zero_add] using seg_drop f 0 n t ht
  rw [seg_add,show t+(n-t+B)=n+B by omega,seg_add,show t+(n-t)=n by omega,hd]

theorem actual_old_target_prior_clock (f : Nat → Bool) (n t s B i T j : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hs : s<n) (hi : i≤T) (hj : 2≤j)
    (hA : ∀ k, k<T → f (n+B+k)=true)
    (hS : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (hW1 : Win f t (n+B+i-t)) (hW2 : Win f s (n+B+T+j-s)) :
    mass (seg f s (n-s))<mass (seg f t (n-t)) ∧ i+j<T := by
  have hAword (K : Nat) (hK : K≤T) : seg f (n+B) K=List.replicate K true := by
    apply seg_A
    intro x hx hxK
    simpa only [Nat.add_sub_cancel' hx] using hA (x-(n+B)) (by omega)
  have hp1 : seg f t (n+B+i-t)=(seg f 0 n).drop t++seg f n B++List.replicate i true := by
    rw [show n+B+i-t=n-t+B+i by omega,source_splice f n t B i (by omega),hAword i hi]
  have hp2 : seg f s (n+B+T+j-s)=(seg f 0 n).drop s++seg f n B++
      List.replicate T true++List.replicate j false := by
    rw [show n+B+T+j-s=(n-s+B+T)+j by omega,seg_add,
      show s+(n-s+B+T)=n+B+T by omega,seg_false f (n+B+T) j hS,
      source_splice f n s B T (by omega),hAword T (Nat.le_refl _)]
  have hm1 : mass ((seg f 0 n).drop t++seg f n B++List.replicate i true)=1 := by
    rw [←hp1,seg_mass]
    have hh := hW1.2.1
    rw [show t+(n+B+i-t)=n+B+i by omega] at hh
    rw [show t+(n+B+i-t)=n+B+i by omega]
    omega
  have ha1 : areaW ((seg f 0 n).drop t++seg f n B++List.replicate i true)=0 := by
    rw [←hp1,←Ar_areaW]
    exact hW1.2.2
  have hm2 : mass ((seg f 0 n).drop s++seg f n B++List.replicate T true++List.replicate j false)=1 := by
    rw [←hp2,seg_mass]
    have hh := hW2.2.1
    rw [show s+(n+B+T+j-s)=n+B+T+j by omega] at hh
    rw [show s+(n+B+T+j-s)=n+B+T+j by omega]
    omega
  have ha2 : areaW ((seg f 0 n).drop s++seg f n B++List.replicate T true++List.replicate j false)=0 := by
    rw [←hp2,←Ar_areaW]
    exact hW2.2.2
  have h := old_target_prior_clock (seg f 0 n) (seg f n B) hw t s i T j hj hm1 ha1 hm2 ha2
  have hd1 : (seg f 0 n).drop t=seg f t (n-t) := by simpa only [Nat.zero_add] using seg_drop f 0 n t (by omega)
  have hd2 : (seg f 0 n).drop s=seg f s (n-s) := by simpa only [Nat.zero_add] using seg_drop f 0 n s (by omega)
  rw [hd1,hd2] at h
  exact h

theorem old_target_tail_no_old (w v : List Bool) (hw : BlockWord w) (s T j i : Nat)
    (hj : 2≤j) (hi : T≤i+j)
    (hm : mass (w.drop s++v++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (w.drop s++v++List.replicate T true++List.replicate j false)=0) :
    ¬tailOldRay w v i := by
  rintro ⟨t,_,hmt,hkt⟩
  have hk2 := source_key_before_gap (w.drop s++v) T j hm ha
  have hk1 : runKey (w.drop t++v)= -2 := by rw [runKey_append]; exact hkt
  have hp := Int.mul_nonneg (show 0≤(j : Int)-2 by omega) (show 0≤(j : Int)+4 by omega)
  have hkey : runKey (w.drop s++v)+9≤runKey (w.drop t++v) := by grind
  have hmass := old_key_mass_order w v hw t s hkey
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hm
  omega

/-- On the final j A clocks, actual old sources can be removed, while
all local sources and the common prefix are retained. -/
theorem old_target_tail_local_iff (w v : List Bool) (hw : BlockWord w) (s T j i : Nat)
    (hj : 2≤j) (hi : T≤i+j)
    (hm : mass (w.drop s++v++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (w.drop s++v++List.replicate T true++List.replicate j false)=0) :
    Recaman.ThreeNonsuppliedData.localSupply ((w++v)++List.replicate i true)=true ↔
      Recaman.ThreeNonsuppliedData.localSupply (v++List.replicate i true)=true := by
  rw [ray_supply_append_iff]
  have hn := old_target_tail_no_old w v hw s T j i hj hi hm ha
  exact or_iff_right hn

/-- The base can be cut to n only on this proved final A segment,
under the actual old target window. No whole-history erasure is asserted. -/
theorem actual_old_target_tail_base (f : Nat → Bool) (n s B i T j : Nat)
    (hw : BlockWord (seg f 0 n)) (hs : s<n) (hi : i<T) (hj : 2≤j) (hband : T≤i+j)
    (hA : ∀ k, k<T → f (n+B+k)=true)
    (hS : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (hW : Win f s (n+B+T+j-s)) :
    EndN f 0 (n+B+i) ↔ EndN f n (n+B+i) := by
  constructor
  · rintro ⟨hAi,t,k,ht,he,hwin⟩
    have htn : n≤t := by
      by_cases hh : n≤t
      · exact hh
      · have hww : Win f t (n+B+i-t) := by
          have hk : k=n+B+i-t := by omega
          simpa only [hk] using hwin
        have hb := actual_old_target_prior_clock f n t s B i T j hw (by omega) hs (by omega) hj hA hS hww hW
        omega
    exact ⟨hAi,t,k,htn,he,hwin⟩
  · rintro ⟨hAi,t,k,ht,he,hwin⟩
    exact ⟨hAi,t,k,Nat.zero_le _,he,hwin⟩

/-- A key gap eight can occur at equal old mass, so the strict ordering
threshold is not silently weakened. This is not a C1 counterexample. -/
theorem eight_key_equal_mass_control :
    let w := [true,true]++tripW
    BlockWord w ∧ mass w=mass (w.drop 4) ∧ runKey w=runKey (w.drop 4)+8 := by
  dsimp only
  refine ⟨block_append (BlockWord.free (BlockWord.free BlockWord.nil))
    (BlockWord.triple BlockWord.nil),?_,?_⟩ <;> decide

/-- With no endpoint gap, the same old source can be reused unchanged. -/
theorem zero_gap_same_old_control :
    mass (tripW++List.replicate 8 false++List.replicate 5 true)=1 ∧
    areaW (tripW++List.replicate 8 false++List.replicate 5 true)=0 := by decide

end Recaman.OldSourceKeyOrder
