import Recaman.OldTargetMassFive
import Recaman.BlockSameMassSpan

namespace Recaman.OldSourceKeyOrder

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.BlockSameMassSpan Recaman.RunSupplyKeys Recaman.ASourceReuse
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

end Recaman.OldSourceKeyOrder
