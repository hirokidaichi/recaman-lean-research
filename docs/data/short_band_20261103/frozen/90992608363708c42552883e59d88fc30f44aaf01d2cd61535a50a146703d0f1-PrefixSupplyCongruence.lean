import Recaman.SingleWindowEquality

namespace Recaman.PrefixSupplyCongruence

open Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction Recaman.LineCapacityPeriodic

/-- A walk up to q uses signs strictly before q. -/
theorem walk_eq (f g : Nat → Bool) (q : Nat) (hfg : ∀ i, i<q → f i=g i) :
    ∀ k, k≤q → Fw f k=Fw g k
  | 0,_ => rfl
  | k+1,hk => by
      rw [Fw_succ,Fw_succ,walk_eq f g q hfg k (by omega),hfg k (by omega)]

theorem area_eq (f g : Nat → Bool) (q t : Nat) (hfg : ∀ i, i<q → f i=g i) :
    ∀ k, t+k≤q → Ar f t k=Ar g t k
  | 0,_ => rfl
  | k+1,hk => by
      rw [Ar_succ,Ar_succ,area_eq f g q t hfg k (by omega),
        walk_eq f g q hfg (t+k+1) (by omega),walk_eq f g q hfg t (by omega)]

theorem window_iff (f g : Nat → Bool) (q t k : Nat)
    (hfg : ∀ i, i<q → f i=g i) (htk : t+k≤q) : Win f t k ↔ Win g t k := by
  unfold Win
  rw [walk_eq f g q hfg (t+k) htk,walk_eq f g q hfg t (by omega),area_eq f g q t hfg k htk]

theorem endable_iff (f g : Nat → Bool) (q s b : Nat)
    (hfg : ∀ i, i<q → f i=g i) (hb : b<q) : EndN f s b ↔ EndN g s b := by
  constructor
  · rintro ⟨ha,t,k,hst,htk,hw⟩
    refine ⟨by rw [←hfg b hb]; exact ha,t,k,hst,htk,?_⟩
    exact (window_iff f g q t k hfg (by omega)).mp hw
  · rintro ⟨ha,t,k,hst,htk,hw⟩
    refine ⟨by rw [hfg b hb]; exact ha,t,k,hst,htk,?_⟩
    exact (window_iff f g q t k hfg (by omega)).mpr hw

theorem segment_eq (f g : Nat → Bool) (q n L : Nat)
    (hfg : ∀ i, i<q → f i=g i) (hL : n+L≤q) : seg f n L=seg g n L := by
  unfold seg
  apply List.map_congr_left
  intro i hi
  have hilt:=List.mem_range.mp hi
  exact hfg (n+i) (by omega)

theorem supply_count_eq (f g : Nat → Bool) (q s n L : Nat)
    (hfg : ∀ i, i<q → f i=g i) (hL : n+L≤q) :
    cN (EndN f s) n L=cN (EndN g s) n L := by
  apply cN_congr
  intro i hi hiL
  exact endable_iff f g q s i hfg (by omega)

theorem S_count_eq (f g : Nat → Bool) (q n L : Nat)
    (hfg : ∀ i, i<q → f i=g i) (hL : n+L≤q) :
    cN (fun i=>f i=false) n L=cN (fun i=>g i=false) n L := by
  apply cN_congr
  intro i hi hiL
  rw [hfg i (by omega)]

theorem free_count_eq (f g : Nat → Bool) (q s n L : Nat)
    (hfg : ∀ i, i<q → f i=g i) (hL : n+L≤q) :
    cN (fun i=>f i=true ∧ ¬EndN f s i) n L=
      cN (fun i=>g i=true ∧ ¬EndN g s i) n L := by
  apply cN_congr
  intro i hi hiL
  rw [hfg i (by omega),endable_iff f g q s i hfg (by omega)]

/-- A primitive SAA window does not force the current endpoint sign. -/
theorem window_without_endpoint_A :
    ∃ f : Nat → Bool, Win f 0 3 ∧ ¬EndN f 0 3 := by
  let f:=fun i : Nat=>if i=1 ∨ i=2 then true else false
  refine ⟨f,?_,?_⟩
  · unfold Win
    decide
  · intro he
    have ha:=he.1
    change false=true at ha
    contradiction

end Recaman.PrefixSupplyCongruence
