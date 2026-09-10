import Recaman.BoundedPeriodicSupply

namespace Recaman.NestedReservoirCapacity

open LeadingRunSupply BoundedExcessReservoir SupplyReservoirGeometry
open SharpPeriodicSupply BoundedPeriodicSupply

/-! Explicit rank charges for nested reservoirs. No multiplicity bound is assumed. -/

theorem used_targets_length_le (U S C : List Nat) (f : Nat → Nat) (hS : S.Nodup)
    (hlocal : ∀ u, u ∈ U → f u ∈ S → u ∈ C) :
    (S.filter (fun q => decide (q ∈ U.map f))).length ≤ C.length := by
  have hn : (S.filter (fun q => decide (q ∈ U.map f))).Nodup := hS.filter _
  have hsub : S.filter (fun q => decide (q ∈ U.map f)) ⊆ C.map f := by
    intro q hq
    have hq' := List.mem_filter.mp hq
    have hmem : q ∈ U.map f := by simpa using hq'.2
    obtain ⟨u,hu,heq⟩ := List.mem_map.mp hmem
    exact List.mem_map.mpr ⟨u, hlocal u hu (by rw [heq]; exact hq'.1), heq⟩
  have hlen := hn.length_le_of_subset hsub
  simpa using hlen

def freeReservoir (e : Int → Bool) (p : Nat) (I : List Nat) (t : Int) (m : Nat) : List Nat :=
  ((reservoir p t m).filter (fun q : Nat => !(e q))).filter (fun q => !decide (q ∈ I))

theorem free_reservoir_count (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (t : Int) (m B L : Nat) (hmp : m ≤ p)
    (hcount : ((reservoir p t m).filter (fun q : Nat => e q)).length ≤ B)
    (U : List Nat) (off : Nat → Nat)
    (hUrange : ∀ u, u ∈ U → u < p) (hUA : ∀ u, u ∈ U → e u = true)
    (hOff : ∀ u, u ∈ U → 1 ≤ off u ∧ off u ≤ L) :
    m-1 ≤ 2*B+L+(freeReservoir e p (U.map (fun u : Nat => phase p ((u : Int)-off u))) t m).length := by
  let f := fun u : Nat => phase p ((u : Int)-off u)
  let S := (reservoir p t m).filter (fun q : Nat => !(e q))
  let C := (reservoir p t m).filter (fun q : Nat => e q) ++ rightWing p (t-m) L
  have hSn : S.Nodup := (reservoir_nodup p hp t m hmp).filter _
  have hused := used_targets_length_le U S C f hSn (by
    intro u hu hf
    exact short_source_in_candidates e p hp t m L u (off u) (hUrange u hu)
      (hUA u hu) (hOff u hu).1 (hOff u hu).2 (List.mem_filter.mp hf).1)
  have hpart := filter_partition_length (fun q : Nat => e q) (reservoir p t m)
  have hpart₂ := filter_partition_length (fun q => decide (q ∈ U.map f)) S
  have hlen := reservoir_length p t m
  have hClen : C.length ≤ B+L := by
    dsimp [C]
    simp only [List.length_append, rightWing, List.length_map, List.length_range]
    omega
  have hSlen : S.length = ((reservoir p t m).filter (fun q : Nat => !(e q))).length := rfl
  change m-1 ≤ 2*B+L+(S.filter (fun q => !decide (q ∈ U.map f))).length
  omega

theorem reservoir_word_ones (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (m : Nat) :
    ones (past e (t-m) (m-1)) =
      (((reservoir p t m).filter (fun q : Nat => e q)).length : Int) := by
  have hword : (reservoir p t m).map (fun q : Nat => e q) = past e (t-m) (m-1) := by
    simp only [reservoir, List.map_map, past]
    apply List.map_congr_left
    intro i _
    exact phase_value e p hp hper _
  rw [← hword, ones_map_eq_filter_length]

/-- A common middle point forces equal run starts under the density bound.
There is no P2 or supply-multiplicity premise. -/
theorem common_point_same_start (e : Int → Bool) (t u x : Int) (m n B : Nat)
    (hsizet : B < m+1) (hsizeu : B < n+1)
    (htA : e t = true) (huA : e u = true)
    (hat : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hau : ∀ i, i < n → e (u-((i+1 : Nat) : Int)) = true)
    (htS : e (t-m-1) = false) (huS : e (u-n-1) = false)
    (htcount : ones (past e (t-m) (m-1)) ≤ B)
    (hucount : ones (past e (u-n) (n-1)) ≤ B)
    (hxt : t-2*m+1 ≤ x ∧ x ≤ t-m-1)
    (hxu : u-2*n+1 ≤ x ∧ x ≤ u-n-1) : t-m = u-n := by
  by_cases htu : t < u
  · by_cases ho : u-n ≤ t
    · exact same_run_start e t u m n htu htA huA hat hau htS huS ho
    · have h := reservoir_contains_run_count e t u m n htA hat (by omega) (by omega)
      omega
  · by_cases hut : u < t
    · by_cases ho : t-m ≤ u
      · exact (same_run_start e u t n m hut huA htA hau hat huS htS ho).symm
      · have h := reservoir_contains_run_count e u t n m huA hau (by omega) (by omega)
        omega
    · have htu : t = u := by omega
      subst u
      by_cases hmn : m < n
      · have h := run_value e t (t-m-1) n htA hau (by omega) (by omega)
        rw [htS] at h
        contradiction
      · by_cases hnm : n < m
        · have h := run_value e t (t-n-1) m htA hat (by omega) (by omega)
          rw [huS] at h
          contradiction
        · omega


theorem common_phase_same_start_mod (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t u : Int) (y : Nat) (m n B : Nat)
    (hsizet : B < m+1) (hsizeu : B < n+1)
    (htA : e t = true) (huA : e u = true)
    (hat : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hau : ∀ i, i < n → e (u-((i+1 : Nat) : Int)) = true)
    (htS : e (t-m-1) = false) (huS : e (u-n-1) = false)
    (htcount : ((reservoir p t m).filter (fun q : Nat => e q)).length ≤ B)
    (hucount : ((reservoir p u n).filter (fun q : Nat => e q)).length ≤ B)
    (hyt : y ∈ reservoir p t m) (hyu : y ∈ reservoir p u n) :
    (t-m) % p = (u-n) % p := by
  obtain ⟨i,hi,hiy⟩ := List.mem_map.mp hyt
  obtain ⟨j,hj,hjy⟩ := List.mem_map.mp hyu
  have hi' := List.mem_range.mp hi
  have hj' := List.mem_range.mp hj
  have hmod := phase_eq_mod p hp (t-m-((i+1 : Nat) : Int))
    (u-n-((j+1 : Nat) : Int)) (by omega)
  obtain ⟨k,hk⟩ := lift_equal_mod p _ _ hmod
  have hcur : e (u+k*p) = true := by rw [LagElevenPeriodic.e_shift e p hper]; exact huA
  have hS : e (u+k*p-n-1) = false := by
    have htime : u+k*p-n-1 = (u-n-1)+k*p := by omega
    rw [htime, LagElevenPeriodic.e_shift e p hper]
    exact huS
  have hlead := leading_shift e p hper u k n hau
  have hcountt : ones (past e (t-m) (m-1)) ≤ B := by
    rw [reservoir_word_ones e p hp hper]
    omega
  have hcountu : ones (past e (u+k*p-n) (n-1)) ≤ B := by
    have htime : u+k*p-n = (u-n)+k*p := by omega
    rw [htime, past_shift e p hper, reservoir_word_ones e p hp hper]
    omega
  have heq := common_point_same_start e t (u+k*p) (t-m-((i+1 : Nat) : Int)) m n B
    hsizet hsizeu htA hcur hat hlead htS hS hcountt hcountu
    (by constructor <;> omega) (by constructor <;> omega)
  have htime : u+k*p-n = (u-n)+k*p := by omega
  rw [heq, htime]
  simp [Int.add_emod]

theorem phase_sub_of_equal_mod (p : Nat) (a b c : Int) (h : a % p = b % p) :
    phase p (a-c) = phase p (b-c) := by
  obtain ⟨k,hk⟩ := lift_equal_mod p a b h
  have heq : a-c = (b-c)+k*p := by omega
  rw [heq]
  simp [phase, Int.add_emod]

theorem reservoir_prefix (p : Nat) (t u : Int) (m n : Nat) (hmn : m ≤ n)
    (hstart : (t-m) % p = (u-n) % p) :
    ∃ tail, reservoir p u n = reservoir p t m ++ tail := by
  have htake : (reservoir p u n).take (m-1) = reservoir p t m := by
    simp only [reservoir, ← List.map_take, List.take_range]
    rw [Nat.min_eq_left (by omega)]
    apply List.map_congr_left
    intro i _
    exact phase_sub_of_equal_mod p (u-n) (t-m) _ hstart.symm
  refine ⟨(reservoir p u n).drop (m-1), ?_⟩
  rw [← htake, List.take_append_drop]

theorem free_reservoir_prefix (e : Int → Bool) (p : Nat) (I : List Nat)
    (t u : Int) (m n : Nat) (hmn : m ≤ n)
    (hstart : (t-m) % p = (u-n) % p) :
    ∃ tail, freeReservoir e p I u n = freeReservoir e p I t m ++ tail := by
  obtain ⟨tail,htail⟩ := reservoir_prefix p t u m n hmn hstart
  unfold freeReservoir
  rw [htail, List.filter_append, List.filter_append]
  exact ⟨_,rfl⟩


def rankCharge (e : Int → Bool) (p : Nat) (I : List Nat) (M : Nat)
    (t : Int) (m : Nat) : Nat := (freeReservoir e p I t m).getD (m-M) 0

theorem rank_charge_member (e : Int → Bool) (p : Nat) (I : List Nat)
    (M : Nat) (t : Int) (m : Nat)
    (hrank : m-M < (freeReservoir e p I t m).length) :
    rankCharge e p I M t m ∈ reservoir p t m ∧
    e (rankCharge e p I M t m) = false ∧ rankCharge e p I M t m ∉ I := by
  have hmem : rankCharge e p I M t m ∈ freeReservoir e p I t m := by
    unfold rankCharge
    rw [← List.getElem_eq_getD (h := hrank) 0]
    exact List.getElem_mem hrank
  have h₁ := List.mem_filter.mp hmem
  have h₂ := List.mem_filter.mp h₁.1
  exact ⟨h₂.1, by simpa using h₂.2, by simpa using h₁.2⟩

theorem rank_charge_same_start_injective (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (I : List Nat) (M : Nat) (t u : Int) (m n : Nat)
    (hm : M ≤ m) (hn : M ≤ n) (hmp : m ≤ p) (hnp : n ≤ p)
    (hrankt : m-M < (freeReservoir e p I t m).length)
    (hranku : n-M < (freeReservoir e p I u n).length)
    (hstart : (t-m) % p = (u-n) % p)
    (heq : rankCharge e p I M t m = rankCharge e p I M u n) : m = n := by
  have hordered : ∀ (t u : Int) (m n : Nat), m ≤ n → M ≤ m → M ≤ n → n ≤ p →
      m-M < (freeReservoir e p I t m).length →
      n-M < (freeReservoir e p I u n).length →
      (t-m) % p = (u-n) % p →
      rankCharge e p I M t m = rankCharge e p I M u n → m = n := by
    intro a b r s hrs hMr hMs hsp hr hs hbase hcharge
    obtain ⟨tail,htail⟩ := free_reservoir_prefix e p I a b r s hrs hbase
    have hindex : r-M < (freeReservoir e p I b s).length := by rw [htail]; simp; omega
    have hnodup : (freeReservoir e p I b s).Nodup :=
      ((reservoir_nodup p hp b s hsp).filter _).filter _
    have hprefix : (freeReservoir e p I b s).getD (r-M) 0 =
        (freeReservoir e p I a r).getD (r-M) 0 := by
      rw [htail]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hr]
    have hinj := (List.getD_inj hindex hs hnodup).mp
      (show (freeReservoir e p I b s).getD (r-M) 0 =
        (freeReservoir e p I b s).getD (s-M) 0 by
        rw [hprefix]; exact hcharge)
    omega
  by_cases hmn : m ≤ n
  · exact hordered t u m n hmn hm hn hnp hrankt hranku hstart heq
  · exact (hordered u t n m (by omega) hn hm hmp hranku hrankt hstart.symm heq.symm).symm


/-- Capacity for every long-run source with a sparse middle reservoir.
Multiple Q sources in one run are handled by explicit, distinct ranks. -/
theorem density_periodic_capacity_extension (e : Int → Bool) (p L B : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (hp : 0 < p)
    (U Q : List Nat) (run off : Nat → Nat)
    (hUnodup : U.Nodup) (hQnodup : Q.Nodup)
    (hUrange : ∀ u, u ∈ U → u < p) (hQrange : ∀ t, t ∈ Q → t < p)
    (hUA : ∀ u, u ∈ U → e u = true)
    (hOff : ∀ u, u ∈ U → 1 ≤ off u ∧ off u ≤ L)
    (hUS : ∀ u, u ∈ U → e (phase p ((u : Int)-off u)) = false)
    (hUinj : ∀ u v, u ∈ U → v ∈ U →
      phase p ((u : Int)-off u) = phase p ((v : Int)-off v) → u = v)
    (hRun : ∀ t, t ∈ Q → 2*B+L+2 ≤ run t ∧ e t = true ∧
      (∀ i, i < run t → e ((t : Int)-((i+1 : Nat) : Int)) = true) ∧
      e ((t : Int)-run t-1) = false ∧
      ((reservoir p t (run t)).filter (fun q : Nat => e q)).length ≤ B) :
    U.length + Q.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  let M := 2*B+L+2
  let f := fun u : Nat => phase p ((u : Int)-off u)
  let g := fun t : Nat => rankCharge e p (U.map f) M t (run t)
  have hmp : ∀ t, t ∈ Q → run t ≤ p := by
    intro t ht
    have h := hRun t ht
    have hb := exact_run_lt_period e p hp hper t (run t) h.2.1 h.2.2.1 h.2.2.2.1
    omega
  have hrank : ∀ t, t ∈ Q → run t-M < (freeReservoir e p (U.map f) t (run t)).length := by
    intro t ht
    have h := hRun t ht
    have hc := free_reservoir_count e p hp t (run t) B L (hmp t ht) h.2.2.2.2
      U off hUrange hUA hOff
    dsimp [M,f] at *
    omega
  have hg : ∀ t, t ∈ Q → g t ∈ reservoir p t (run t) ∧ e (g t) = false ∧ g t ∉ U.map f := by
    intro t ht
    exact rank_charge_member e p (U.map f) M t (run t) (hrank t ht)
  have hfn : (U.map f).Nodup := LagElevenPeriodic.nodup_map_of_inj hUnodup hUinj
  have hgn : (Q.map g).Nodup := by
    apply LagElevenPeriodic.nodup_map_of_inj hQnodup
    intro t u ht hu heq
    have htR := hRun t ht
    have huR := hRun u hu
    have htlarge := htR.1
    have hularge := huR.1
    have hstart := common_phase_same_start_mod e p hp hper t u (g t) (run t) (run u) B
      (by omega) (by omega) htR.2.1 huR.2.1 htR.2.2.1 huR.2.2.1
      htR.2.2.2.1 huR.2.2.2.1 htR.2.2.2.2 huR.2.2.2.2
      (hg t ht).1 (by rw [heq]; exact (hg u hu).1)
    have hrun := rank_charge_same_start_injective e p hp (U.map f) M t u (run t) (run u)
      htR.1 huR.1 (hmp t ht) (hmp u hu) (hrank t ht) (hrank u hu) hstart heq
    obtain ⟨k,hk⟩ := lift_equal_mod p _ _ hstart
    have htu : (t : Int) = u+k*p := by omega
    have hmod : (t : Int) % p = (u : Int) % p := by rw [htu]; simp [Int.add_emod]
    have htlt := hQrange t ht
    have hult := hQrange u hu
    rw [Int.emod_eq_of_lt (by omega) (by omega),
      Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  have hdisj : ∀ a, a ∈ U.map f → a ∉ Q.map g := by
    intro a ha hb
    obtain ⟨t,ht,heq⟩ := List.mem_map.mp hb
    exact (hg t ht).2.2 (by rw [heq]; exact ha)
  have hnodup := LagElevenPeriodic.nodup_append hfn hgn hdisj
  have hsubset : U.map f ++ Q.map g ⊆ LagElevenPeriodic.subPhases e 0 p := by
    intro y hy
    apply (LagElevenPeriodic.mem_subPhases e 0 p y).mpr
    rcases List.mem_append.mp hy with hU | hQ
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hU
      exact ⟨phase_lt p hp _, by simpa [f] using hUS u hu⟩
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hQ
      have hgt := hg t ht
      obtain ⟨i,hi,heq⟩ := List.mem_map.mp hgt.1
      refine ⟨?_, ?_⟩
      · rw [← heq]
        exact phase_lt p hp _
      · simpa using hgt.2.1
  have hlen := hnodup.length_le_of_subset hsubset
  simpa using hlen

/-- P2 bounded-excess specialization with a linear run threshold, uniform in R. -/
theorem bounded_excess_periodic_capacity_extension (e : Int → Bool) (p L R : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (hp : 0 < p)
    (U Q : List Nat) (run off : Nat → Nat)
    (hUnodup : U.Nodup) (hQnodup : Q.Nodup)
    (hUrange : ∀ u, u ∈ U → u < p) (hQrange : ∀ t, t ∈ Q → t < p)
    (hUA : ∀ u, u ∈ U → e u = true)
    (hOff : ∀ u, u ∈ U → 1 ≤ off u ∧ off u ≤ L)
    (hUS : ∀ u, u ∈ U → e (phase p ((u : Int)-off u)) = false)
    (hUinj : ∀ u v, u ∈ U → v ∈ U →
      phase p ((u : Int)-off u) = phase p ((v : Int)-off v) → u = v)
    (hRun : ∀ t, t ∈ Q → 3 ≤ run t ∧ 4*R+L+2 ≤ run t ∧ e t = true ∧
      (∀ i, i < run t → e ((t : Int)-((i+1 : Nat) : Int)) = true) ∧
      e ((t : Int)-run t-1) = false ∧
      ∃ d, ShortPeriodicSupply.P2 e t d ∧ (d : Int) ≤ 4*run t-1+4*R) :
    U.length + Q.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  apply density_periodic_capacity_extension e p L (2*R) hper hp U Q run off
    hUnodup hQnodup hUrange hQrange hUA hOff hUS hUinj
  intro t ht
  have h := hRun t ht
  obtain ⟨d,hP,hhi⟩ := h.2.2.2.2.2
  refine ⟨by omega,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  exact reservoir_A_count e p hp hper t d (run t) R h.1 h.2.2.2.1 hP hhi

end Recaman.NestedReservoirCapacity
