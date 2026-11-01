import Recaman.ThreeRunTargetSource

namespace Recaman.ASourceReuse

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Removing the trailing S gap from an actual mass-one/area-zero word
exposes the negative square key of that same source. -/
theorem source_key_before_gap (v : List Bool) (T j : Nat)
    (hm : mass (v++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (v++List.replicate T true++List.replicate j false)=0) :
    runKey v= -2*((j : Int)+1)^2 := by
  have hmass : mass (v++List.replicate T true)=(j : Int)+1 := by
    rw [mass_append,mass_rep_false] at hm
    omega
  have hk : runKey (v++List.replicate T true++List.replicate j false)= -2 := by
    unfold runKey
    rw [hm,ha]
    decide
  rw [runKey_append_S,hmass,runKey_append_A] at hk
  grind

/-- Reusing one A-run source across a later S gap obeys an exact relation.
The entire arbitrary internal word u is the same on both sides. -/
theorem A_source_reuse_equation (u : List Bool) (d e i T j : Nat)
    (hm1 : mass (List.replicate e true++u++List.replicate i true)=1)
    (ha1 : areaW (List.replicate e true++u++List.replicate i true)=0)
    (hm2 : mass (List.replicate d true++u++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (List.replicate d true++u++List.replicate T true++List.replicate j false)=0) :
    2*(cntF u : Int)*((e : Int)-(d : Int))=(j : Int)*((j : Int)+2) := by
  have hk1 := source_key_before_gap (List.replicate e true++u) i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [List.replicate_zero,List.append_nil] using ha1)
  have hk2 := source_key_before_gap (List.replicate d true++u) T j hm2 ha2
  rw [runKey_prepend_A] at hk1 hk2
  grind

/-- A positive endpoint gap forces a strictly earlier A-run start for the
previous supply and a positive number of intervening S signs. -/
theorem A_source_reuse_order (u : List Bool) (d e i T j : Nat) (hj : 1≤j)
    (hm1 : mass (List.replicate e true++u++List.replicate i true)=1)
    (ha1 : areaW (List.replicate e true++u++List.replicate i true)=0)
    (hm2 : mass (List.replicate d true++u++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (List.replicate d true++u++List.replicate T true++List.replicate j false)=0) :
    0<cntF u ∧ d<e := by
  have h := A_source_reuse_equation u d e i T j hm1 ha1 hm2 ha2
  have hpos := Int.mul_pos (show 0<(j : Int) by omega) (show 0<(j : Int)+2 by omega)
  have hS : 0<cntF u := by
    by_cases hz : cntF u=0
    · rw [hz] at h
      simp only [Int.natCast_zero,Int.mul_zero,Int.zero_mul] at h
      omega
    · omega
  have hde : d<e := by
    by_cases he : d<e
    · exact he
    · have hp := Int.mul_nonneg (show 0≤2*(cntF u : Int) by omega)
          (show 0≤(d : Int)-(e : Int) by omega)
      have hid : 2*(cntF u : Int)*((d : Int)-(e : Int))=
        -(2*(cntF u : Int)*((e : Int)-(d : Int))) := by grind
      rw [hid] at hp
      omega
  exact ⟨hS,hde⟩

/-- Nondivisibility rules out only this earlier source. It does not rule
out other runs, old sources, or the final target itself. -/
theorem A_source_reuse_divides (u : List Bool) (d e i T j : Nat)
    (hm1 : mass (List.replicate e true++u++List.replicate i true)=1)
    (ha1 : areaW (List.replicate e true++u++List.replicate i true)=0)
    (hm2 : mass (List.replicate d true++u++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (List.replicate d true++u++List.replicate T true++List.replicate j false)=0) :
    ∃ k : Int, (j : Int)*((j : Int)+2)=2*(cntF u : Int)*k := by
  exact ⟨(e : Int)-(d : Int),(A_source_reuse_equation u d e i T j hm1 ha1 hm2 ha2).symm⟩

/-- The first numeric count witness cannot reuse the first A-run to
supply any earlier clock of the last A run, for any initial history. -/
theorem first_numeric_source_not_reused (u : List Bool) (e i T : Nat)
    (hS : cntF u=7)
    (hm2 : mass (List.replicate 1 true++u++List.replicate T true++List.replicate 4 false)=1)
    (ha2 : areaW (List.replicate 1 true++u++List.replicate T true++List.replicate 4 false)=0) :
    ¬(mass (List.replicate e true++u++List.replicate i true)=1 ∧
      areaW (List.replicate e true++u++List.replicate i true)=0) := by
  rintro ⟨hm1,ha1⟩
  have h := A_source_reuse_equation u 1 e i T 4 hm1 ha1 hm2 ha2
  rw [hS] at h
  omega

private theorem source_suffix_segment (f : Nat → Bool) (a M e T j : Nat) (u : List Bool)
    (heM : e≤M)
    (hword : seg f a (M+u.length+T+j)=List.replicate M true++u++
      List.replicate T true++List.replicate j false) :
    seg f (a+M-e) (e+u.length+T+j)=List.replicate e true++u++
      List.replicate T true++List.replicate j false := by
  have hd := seg_drop f a (M+u.length+T+j) (M-e) (by omega)
  simp only [List.append_assoc] at hword
  rw [hword,List.drop_append,List.drop_replicate,List.length_replicate,show M-e-M=0 by omega,List.drop_zero] at hd
  simpa only [show M-(M-e)=e by omega,show a+(M-e)=a+M-e by omega,
    show M+u.length+T+j-(M-e)=e+u.length+T+j by omega,List.append_assoc] using hd.symm

/-- Both source starts are in one actual A run, followed by the same full
internal history. The original base0, both endpoint signs, both windows,
and the copied prefix are explicit. -/
theorem actual_A_source_reuse (f : Nat → Bool) (a M d e i T j : Nat) (u : List Bool)
    (hdM : d≤M) (heM : e≤M) (hi : i≤T)
    (hword : seg f a (M+u.length+T+j)=List.replicate M true++u++
      List.replicate T true++List.replicate j false)
    (hA1 : f (a+M+u.length+i)=true) (hA2 : f (a+M+u.length+T+j)=true)
    (hW1 : Win f (a+M-e) (e+u.length+i))
    (hW2 : Win f (a+M-d) (d+u.length+T+j)) :
    EndN f 0 (a+M+u.length+i) ∧ EndN f 0 (a+M+u.length+T+j) ∧
      2*(cntF u : Int)*((e : Int)-(d : Int))=(j : Int)*((j : Int)+2) := by
  have hdword := source_suffix_segment f a M d T j u hdM hword
  have heword := source_suffix_segment f a M e T j u heM hword
  have heprefix : seg f (a+M-e) (e+u.length+i)=List.replicate e true++u++List.replicate i true := by
    have htake := seg_take f (a+M-e) (e+u.length+T+j) (e+u.length+i) (by omega)
    have hseg : ((List.replicate e true++u)++(List.replicate T true++List.replicate j false)).take
        (e+u.length+i)=List.replicate e true++u++List.replicate i true := by
      rw [List.take_append,List.take_of_length_le (by simp only [List.length_append,List.length_replicate]; omega),
        show e+u.length+i-(List.replicate e true++u).length=i by simp only [List.length_append,List.length_replicate]; omega,
        List.take_append_of_le_length (by simpa only [List.length_replicate] using hi),
        List.take_replicate,Nat.min_eq_left hi]
    rw [heword] at htake
    rw [show List.replicate e true++u++List.replicate T true++List.replicate j false=
      (List.replicate e true++u)++(List.replicate T true++List.replicate j false) by rw [List.append_assoc],hseg] at htake
    exact htake.symm
  have hm1 : mass (List.replicate e true++u++List.replicate i true)=1 := by
    rw [←heprefix,seg_mass]
    have hh := hW1.2.1
    omega
  have ha1 : areaW (List.replicate e true++u++List.replicate i true)=0 := by
    rw [←heprefix,←Ar_areaW]
    exact hW1.2.2
  have hm2 : mass (List.replicate d true++u++List.replicate T true++List.replicate j false)=1 := by
    rw [←hdword,seg_mass]
    have hh := hW2.2.1
    omega
  have ha2 : areaW (List.replicate d true++u++List.replicate T true++List.replicate j false)=0 := by
    rw [←hdword,←Ar_areaW]
    exact hW2.2.2
  refine ⟨⟨hA1,a+M-e,e+u.length+i,Nat.zero_le _,by omega,hW1⟩,
    ⟨hA2,a+M-d,d+u.length+T+j,Nat.zero_le _,by omega,hW2⟩,?_⟩
  exact A_source_reuse_equation u d e i T j hm1 ha1 hm2 ha2

/-- Odd endpoint gaps cannot reuse the same A-run as a source for both
windows. Other source runs and old windows are deliberately retained. -/
theorem odd_gap_no_A_reuse (u : List Bool) (d e i T k : Nat)
    (hm2 : mass (List.replicate d true++u++List.replicate T true++List.replicate (2*k+1) false)=1)
    (ha2 : areaW (List.replicate d true++u++List.replicate T true++List.replicate (2*k+1) false)=0) :
    ¬(mass (List.replicate e true++u++List.replicate i true)=1 ∧
      areaW (List.replicate e true++u++List.replicate i true)=0) := by
  rintro ⟨hm1,ha1⟩
  have h := A_source_reuse_equation u d e i T (2*k+1) hm1 ha1 hm2 ha2
  have hleft : 2*(cntF u : Int)*((e : Int)-(d : Int))=
      2*((cntF u : Int)*((e : Int)-(d : Int))) := by grind
  have hright : ((2*k+1 : Nat) : Int)*(((2*k+1 : Nat) : Int)+2)=
      2*(2*(k : Int)^2+4*(k : Int)+1)+1 := by
    simp only [Int.natCast_add,Int.natCast_mul]
    grind
  rw [hleft,hright] at h
  omega

/-- The S-run version shifts the target source in the opposite direction.
All internal S/A patterns, lengths and earlier A-only clocks are retained. -/
theorem S_source_reuse_equation (u : List Bool) (d e i T j : Nat)
    (hm1 : mass (List.replicate e false++u++List.replicate i true)=1)
    (ha1 : areaW (List.replicate e false++u++List.replicate i true)=0)
    (hm2 : mass (List.replicate d false++u++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (List.replicate d false++u++List.replicate T true++List.replicate j false)=0) :
    ((d : Int)-(e : Int))*((d : Int)+(e : Int)+2*(cntF u : Int))=
      (j : Int)*((j : Int)+2) := by
  have hk1 := source_key_before_gap (List.replicate e false++u) i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [List.replicate_zero,List.append_nil] using ha1)
  have hk2 := source_key_before_gap (List.replicate d false++u) T j hm2 ha2
  rw [runKey_prepend_S] at hk1 hk2
  grind

theorem S_source_reuse_order (u : List Bool) (d e i T j : Nat) (hj : 1≤j)
    (hm1 : mass (List.replicate e false++u++List.replicate i true)=1)
    (ha1 : areaW (List.replicate e false++u++List.replicate i true)=0)
    (hm2 : mass (List.replicate d false++u++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (List.replicate d false++u++List.replicate T true++List.replicate j false)=0) : e<d := by
  have h := S_source_reuse_equation u d e i T j hm1 ha1 hm2 ha2
  have hpos := Int.mul_pos (show 0<(j : Int) by omega) (show 0<(j : Int)+2 by omega)
  by_cases hde : e<d
  · exact hde
  · have hp := Int.mul_nonneg (show 0≤(e : Int)-(d : Int) by omega)
        (show 0≤(d : Int)+(e : Int)+2*(cntF u : Int) by omega)
    have hid : ((e : Int)-(d : Int))*((d : Int)+(e : Int)+2*(cntF u : Int))=
      -(((d : Int)-(e : Int))*((d : Int)+(e : Int)+2*(cntF u : Int))) := by grind
    rw [hid] at hp
    omega

/-- S-source reuse across an odd gap is possible. This control prevents
extending the A-source parity exclusion to every source type. -/
theorem S_source_odd_gap_control :
    mass (List.replicate 1 false++List.replicate 2 true)=1 ∧
    areaW (List.replicate 1 false++List.replicate 2 true)=0 ∧
    mass (List.replicate 2 false++List.replicate 4 true++List.replicate 1 false)=1 ∧
    areaW (List.replicate 2 false++List.replicate 4 true++List.replicate 1 false)=0 := by decide

end Recaman.ASourceReuse
