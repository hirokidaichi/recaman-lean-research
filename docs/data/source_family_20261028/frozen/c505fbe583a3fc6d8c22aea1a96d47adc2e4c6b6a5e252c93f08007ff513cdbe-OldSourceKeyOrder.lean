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

end Recaman.OldSourceKeyOrder
