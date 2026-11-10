import Recaman.FloorSupplyPotential

namespace Recaman.FloorSupplyDistinctCharge

open Recaman.FloorSupplyPotential Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

private theorem latest_floor_charge (f : Nat → Bool) (n a t : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnt : n≤t) (hfloor : ∀ i, n≤i → i≤t → m≤Fw f i)
    (htop : Fw f t=m+2) (he : EndN f 0 t) :
    ∃ q, n≤q ∧ q<t ∧ Fw f q=m ∧
      floorPotential f n m (q-1)=floorPotential f n m t ∧
      ∀ j, q<j → j<t → ¬(Fw f j=m ∧
        floorPotential f n m (j-1)=floorPotential f n m t) := by
  let Q := fun q => Fw f q=m ∧ floorPotential f n m (q-1)=floorPotential f n m t
  obtain ⟨q,hqn,hqt,hqF,hqP,_⟩ := actual_floor_supply_downcross f n a t m hw hpre hnt hfloor htop he
  obtain ⟨d,hdt,hm,hafter⟩ := last_markN Q n (t-n)
  rcases hm with hd | hm
  · have hz := hafter (q-n) (by omega) (by omega)
    rw [Nat.add_sub_cancel' (show n≤q by omega)] at hz
    exact (hz ⟨hqF,hqP⟩).elim
  · have hdn : 0<d := by
      by_cases hd : d=0
      · have hz := hafter (q-n) (by omega) (by omega)
        rw [Nat.add_sub_cancel' (show n≤q by omega)] at hz
        exact (hz ⟨hqF,hqP⟩).elim
      · omega
    refine ⟨n+d-1,by omega,by omega,hm.1,hm.2,?_⟩
    intro j hj hlt
    have hz := hafter (j-n) (by omega) (by omega)
    rw [Nat.add_sub_cancel' (show n≤j by omega)] at hz
    exact hz

/-- Original supplies at two levels above the floor have an injective
assignment to earlier original free additions at the floor. -/
theorem actual_floor_supply_injection (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hfloor : ∀ i, n≤i → i≤n+K → m≤Fw f i) :
    ∃ q : Nat → Nat,
      (∀ t, n≤t → t<n+K → Fw f t=m+2 → EndN f 0 t →
        n≤q t ∧ q t<t ∧ Fw f (q t)=m ∧ f (q t)=true ∧ ¬EndN f 0 (q t)) ∧
      (∀ t u, n≤t → t<u → u<n+K → Fw f t=m+2 → Fw f u=m+2 →
        EndN f 0 t → EndN f 0 u → q t≠q u) := by
  classical
  let P := fun t => n≤t ∧ t<n+K ∧ Fw f t=m+2 ∧ EndN f 0 t
  have hex (t : Nat) (ht : P t) := latest_floor_charge f n a t m hw hpre ht.1
    (fun i hi hit => hfloor i hi (by have := ht.2.1; omega)) ht.2.2.1 ht.2.2.2
  let q := fun t => if h : P t then Classical.choose (hex t h) else n
  have hq (t : Nat) (ht : P t) :
      n≤q t ∧ q t<t ∧ Fw f (q t)=m ∧
      floorPotential f n m (q t-1)=floorPotential f n m t ∧
      ∀ j, q t<j → j<t → ¬(Fw f j=m ∧
        floorPotential f n m (j-1)=floorPotential f n m t) := by
    simp only [q,dif_pos ht]
    exact Classical.choose_spec (hex t ht)
  refine ⟨q,?_,?_⟩
  · intro t hnt htt htop he
    obtain ⟨hn,hlt,hF,_,_⟩ := hq t ⟨hnt,htt,htop,he⟩
    have hqA : f (q t)=true := by
      have h := hfloor (q t+1) (by omega) (by omega)
      rcases fw_cases f (q t) with ⟨_,hA⟩ | ⟨hS,_⟩
      · exact hA
      · omega
    have hno := block_prefix_low_clock_not_endable f n a (q t) hw hpre hn m
      (fun i hi hj => hfloor i hi (by omega)) (by omega)
    exact ⟨hn,hlt,hF,hqA,hno⟩
  · intro t u hnt htu huK hFt hFu ht hu hsame
    obtain ⟨_,hqt,_,hPt,_⟩ := hq t ⟨hnt,by omega,hFt,ht⟩
    obtain ⟨_,_,_,hPu,hAfter⟩ := hq u ⟨by omega,huK,hFu,hu⟩
    rw [hsame] at hPt
    have hEq : floorPotential f n m t=floorPotential f n m u := by omega
    have hStep := floor_potential_step f n (u-1) m (by omega)
    rw [show u-1+1=u by omega,hFu] at hStep
    obtain ⟨j,htj,hju,hF,hP,_⟩ :=
      floor_potential_downcross f n t (u-1) m (floorPotential f n m u)
        hnt (by omega) (fun i hi hj => hfloor i hi (by omega)) (by omega) (by omega)
    exact hAfter j (by omega) (by omega) ⟨hF,hP⟩

end Recaman.FloorSupplyDistinctCharge
