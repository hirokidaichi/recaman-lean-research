import Recaman.SupplyAreaCrossings
import Recaman.FloorSupplyFreeBudget

namespace Recaman.FloorSupplyPairCharge

open Recaman.SupplyAreaCrossings Recaman.FloorSupplyPotential Recaman.FloorSupplyFreeBudget
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

private def lowA (f : Nat → Bool) (m : Int) (t : Nat) : Prop :=
  Fw f t≤m+1 ∧ f t=true

private def exitA (f : Nat → Bool) (m : Int) (t : Nat) : Prop :=
  Fw f t=m+1 ∧ f t=true

private theorem earliest_exit (f : Nat → Bool) (q t : Nat) (m : Int)
    (hqt : q<t) (hq : Fw f q=m) (ht : Fw f t=m+2) :
    ∃ d, q<d ∧ d<t ∧ exitA f m d ∧ ∀ i, q≤i → i<d → ¬exitA f m i := by
  let P := fun i => q≤i ∧ exitA f m i
  obtain ⟨i,hqi,hit,hiF,hiA⟩ := ivt f t (m+2) (by omega) (t-q) q (by omega) (by omega)
  obtain ⟨d,hd,hdp,hfirst⟩ := first_mark P (t-1) ⟨i,by omega,hqi,by omega,hiA⟩
  have hh := hdp.1
  have hF := hdp.2.1
  exact ⟨d,by
    by_cases h : q=d
    · rw [←h,hq] at hF
      omega
    · omega,by omega,hdp.2,fun i hqi hid hi => hfirst i hid ⟨hqi,hi⟩⟩

private theorem potential_constant (f : Nat → Bool) (n a : Nat) (m : Int)
    (hna : n≤a) :
    ∀ K : Nat, (∀ i, 0<i → i≤K → Fw f (a+i)=m+1) →
      floorPotential f n m (a+K)=floorPotential f n m a := by
  intro K
  induction K with
  | zero => simp
  | succ k ih =>
    intro h
    have hi := ih (fun i hi hle => h i hi (by omega))
    have hs := floor_potential_step f n (a+k) m (by omega)
    rw [show a+k+1=a+(k+1) by omega,h (k+1) (by omega) (by omega)] at hs
    omega

private theorem consecutive_floor_visits_drop_one (f : Nat → Bool)
    (n q z d : Nat) (m : Int) (hnq : n≤q) (hqz : q<z) (hzd : z≤d)
    (hFq : Fw f q=m) (hFz : Fw f z=m)
    (hfloor : ∀ i, q≤i → i≤z → m≤Fw f i)
    (hskip : ∀ i, q<i → i<z → Fw f i≠m)
    (hfirst : ∀ i, q≤i → i<d → ¬exitA f m i) :
    floorPotential f n m q-floorPotential f n m z=1 := by
  have hb (i : Nat) (hi : 0<i) (hiz : i≤z-q-1) : Fw f (q+i)=m+1 := by
    have hmin := hfloor (q+i) (by omega) (by omega)
    have hn := hskip (q+i) (by omega) (by omega)
    by_cases h : m+2≤Fw f (q+i)
    · obtain ⟨u,hqu,hui,hF,hA⟩ := ivt f (q+i) (m+2) h i q (by omega) (by omega)
      exact (hfirst u hqu (by omega) ⟨by omega,hA⟩).elim
    · omega
  have hh := potential_constant f n q m hnq (z-q-1) hb
  rw [show q+(z-q-1)=z-1 by omega] at hh
  have hs := floor_potential_step f n (z-1) m (by omega)
  rw [show z-1+1=z by omega,hFz] at hs
  omega

/-- Each floor-plus-two supply has two separate original low free A
positions. The next floor visit, or the first exit if there is no next
floor visit, is distinct from the payments of all other supplies. -/
theorem floor_supply_pair_charge_after_cut (f : Nat → Bool) (n a K c : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hfloor : ∀ i, n≤i → i≤n+K → m≤Fw f i)
    (hcut : ∀ i, n≤i → i<c → Fw f i≠m) :
    2*cN (fun t => Fw f t=m+2 ∧ EndN f 0 t) n K≤
      cN (fun t => c≤t ∧ Fw f t≤m+1 ∧ f t=true ∧ ¬EndN f 0 t) n K := by
  classical
  let p := floorPotential f n m
  let P := fun t => Fw f t=m+2 ∧ EndN f 0 t
  let D := fun t => n≤t ∧ t<n+K ∧ P t
  let Q := fun t => c≤t ∧ Fw f t≤m+1 ∧ f t=true ∧ ¬EndN f 0 t
  have hex (t : Nat) (ht : D t) :
      ∃ q z, n<q ∧ q<z ∧ z<t ∧ Fw f q=m ∧ p q=p t-1 ∧
        (∀ i, q<i → i<t → ¬areaCrossesDown p (p t) i) ∧
        lowA f m q ∧ lowA f m z ∧
        (∀ i, q<i → i<z → Fw f i≠m) ∧
        (∀ i, q≤i → i<z → ¬exitA f m i) := by
    obtain ⟨hnt,htK,hF,he⟩ := ht
    obtain ⟨q,hqn,hqt,hqF,hcross,hafter⟩ :=
      latest_actual_supply_area_crossing f n a t (m+1) hw hpre hnt (by omega) he
    have hm : m+1-1=m := by omega
    rw [hm] at hcross hafter
    have hLow := hfloor q (by omega) (by omega)
    have hqH : Fw f q=m := by omega
    have floorA (i : Nat) (hni : n≤i) (hit : i<t) (hiF : Fw f i=m) : lowA f m i := by
      have h := hfloor (i+1) (by omega) (by omega)
      rcases fw_cases f i with ⟨_,ha⟩ | ⟨hs,_⟩
      · exact ⟨by omega,ha⟩
      · omega
    have hs := floor_potential_step f n (q-1) m (by omega)
    rw [show q-1+1=q by omega,hqH] at hs
    change p q=p (q-1)+m-(m+1) at hs
    have hc1 : p q<p t := hcross.1
    have hc2 : p t≤p (q-1) := hcross.2
    obtain ⟨d,hqd,hdt,hd,hfirst⟩ := earliest_exit f q t m hqt hqH hF
    let Mark := fun i => q<i ∧ (Fw f i=m ∨ i=d)
    obtain ⟨z,hzd,hz,hZ⟩ := first_mark Mark d ⟨d,by omega,hqd,Or.inr rfl⟩
    have hqz := hz.1
    have hAt : lowA f m z := by
      rcases hz.2 with h | h
      · exact floorA z (by omega) (by omega) h
      · rw [h]
        exact ⟨by have := hd.1; omega,hd.2⟩
    exact ⟨q,z,hqn,hqz,by omega,hqH,by omega,hafter,
      floorA q (by omega) hqt hqH,hAt,
      fun i hi hj hp => hZ i hj ⟨hi,Or.inl hp⟩,
      fun i hi hj => hfirst i hi (by omega)⟩
  let q := fun t => if h : D t then Classical.choose (hex t h) else n
  let z := fun t => if h : D t then Classical.choose (Classical.choose_spec (hex t h)) else n
  have data (t : Nat) (ht : D t) :
      n<q t ∧ q t<z t ∧ z t<t ∧ Fw f (q t)=m ∧ p (q t)=p t-1 ∧
        (∀ i, q t<i → i<t → ¬areaCrossesDown p (p t) i) ∧
        lowA f m (q t) ∧ lowA f m (z t) ∧
        (∀ i, q t<i → i<z t → Fw f i≠m) ∧
        (∀ i, q t≤i → i<z t → ¬exitA f m i) := by
    simp only [q,z,dif_pos ht]
    exact Classical.choose_spec (Classical.choose_spec (hex t ht))
  have hcutQ (t : Nat) (ht : D t) : c≤q t := by
    obtain ⟨hn,hqz,hzt,hF,_,_,_,_,_,_⟩ := data t ht
    by_cases h : c≤q t
    · exact h
    · exact (hcut (q t) (by omega) (by omega) hF).elim
  have hQ (i : Nat) (hci : c≤i) (hni : n≤i) (hiK : i<n+K) (ha : lowA f m i) : Q i :=
    ⟨hci,ha.1,ha.2,block_prefix_low_clock_not_endable f n a i hw hpre hni m
      (fun j hj hji => hfloor j hj (by omega)) ha.1⟩
  have separated (t u : Nat) (htu : t<u) (ht : D t) (hu : D u) :
      z t<q u ∨ z u<q t := by
    obtain ⟨hnt,hqzt,hzt,hFt,hpt,_,_,_,hskipT,hexitT⟩ := data t ht
    obtain ⟨hnu,hqzu,hzu,hFu,hpu,hafter,_,_,hskipU,hexitU⟩ := data u hu
    have hspacing (hq : q u≤t) : p t+3≤p u := by
      have hm : m+1-1=m := by omega
      have h := supply_potential_spacing_after_last_crossing f n t u (q u) (m+1)
        ht.1 htu hq (by have := ht.2.2.1; omega) (by have := hu.2.2.1; omega)
        ht.2.2.2.1 (by rwa [hm])
      rwa [hm] at h
    rcases Nat.lt_trichotomy (q t) (q u) with hlt | heq | hgt
    · left
      by_cases hz : z t<q u
      · exact hz
      · have heq : z t=q u := by
          by_cases hh : q u<z t
          · exact (hskipT (q u) hlt hh hFu).elim
          · omega
        have hh := consecutive_floor_visits_drop_one f n (q t) (q u) (z t) m
          (by omega) hlt (by omega) hFt hFu
          (fun i hi hj => hfloor i (by omega) (by have := hu.2.1; omega))
          (fun i hi hj => hskipT i hi (by omega)) hexitT
        change p (q t)-p (q u)=1 at hh
        have hp := hspacing (by omega)
        omega
    · have hp := hspacing (by omega)
      rw [heq] at hpt
      omega
    · right
      by_cases hz : z u<q t
      · exact hz
      · have heq : z u=q t := by
          by_cases hh : q t<z u
          · exact (hskipU (q t) hgt hh hFt).elim
          · omega
        have hh := consecutive_floor_visits_drop_one f n (q u) (q t) (z u) m
          (by omega) hgt (by omega) hFu hFt
          (fun i hi hj => hfloor i (by omega) (by have := ht.2.1; omega))
          (fun i hi hj => hskipU i hi (by omega)) hexitU
        change p (q u)-p (q t)=1 at hh
        have hp := hspacing (by omega)
        omega
  let Hit := fun i => ∃ t, D t ∧ q t=i
  have h1 : cN P n K≤cN (fun i => Q i ∧ Hit i) n K := by
    apply count_le_of_interval_injection P _ n K q
    · intro t hnt htK ht
      have hD : D t := ⟨hnt,htK,ht⟩
      obtain ⟨hn,hqz,hzt,_,_,_,ha,_,_,_⟩ := data t hD
      exact ⟨by omega,by omega,hQ _ (hcutQ t hD) (by omega) (by omega) ha,t,hD,rfl⟩
    · intro t u hn htu hu ht he hsame
      have h := separated t u htu ⟨hn,by omega,ht⟩ ⟨by omega,hu,he⟩
      have ht' := (data t ⟨hn,by omega,ht⟩).2.1
      have hu' := (data u ⟨by omega,hu,he⟩).2.1
      rcases h with h | h <;> omega
  have h2 : cN P n K≤cN (fun i => Q i ∧ ¬Hit i) n K := by
    apply count_le_of_interval_injection P _ n K z
    · intro t hnt htK ht
      have hD : D t := ⟨hnt,htK,ht⟩
      obtain ⟨hn,hqz,hzt,_,_,_,_,ha,_,_⟩ := data t hD
      refine ⟨by omega,by omega,hQ _ (by have := hcutQ t hD; omega) (by omega) (by omega) ha,?_⟩
      rintro ⟨u,hu,hEq⟩
      have hu' := (data u hu).2.1
      rcases Nat.lt_trichotomy t u with h | h | h
      · rcases separated t u h hD hu with h | h <;> omega
      · subst u
        omega
      · rcases separated u t h hu hD with h | h <;> omega
    · intro t u hn htu hu ht he hsame
      have h := separated t u htu ⟨hn,by omega,ht⟩ ⟨by omega,hu,he⟩
      have ht' := (data t ⟨hn,by omega,ht⟩).2.1
      have hu' := (data u ⟨by omega,hu,he⟩).2.1
      rcases h with h | h <;> omega
  have hQpart := cN_split Q Hit n K
  change 2*cN P n K≤cN Q n K
  omega

/-- The original count is the cut-at-boundary specialization. -/
theorem floor_supply_pair_charge (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hfloor : ∀ i, n≤i → i≤n+K → m≤Fw f i) :
    2*cN (fun t => Fw f t=m+2 ∧ EndN f 0 t) n K≤
      cN (fun t => Fw f t≤m+1 ∧ f t=true ∧ ¬EndN f 0 t) n K := by
  have h := floor_supply_pair_charge_after_cut f n a K n m hw hpre hfloor
    (fun i hi hj => by omega)
  have he : cN (fun t => n≤t ∧ Fw f t≤m+1 ∧ f t=true ∧ ¬EndN f 0 t) n K=
      cN (fun t => Fw f t≤m+1 ∧ f t=true ∧ ¬EndN f 0 t) n K := by
    apply cN_congr
    intro t hnt _
    exact ⟨And.right,fun ht => ⟨hnt,ht⟩⟩
  rw [he] at h
  exact h

end Recaman.FloorSupplyPairCharge
