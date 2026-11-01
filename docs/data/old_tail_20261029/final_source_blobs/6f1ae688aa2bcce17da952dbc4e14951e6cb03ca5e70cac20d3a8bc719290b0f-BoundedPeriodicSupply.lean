import Recaman.SupplyReservoirGeometry
import Recaman.SharpPeriodicSupply

namespace Recaman.BoundedPeriodicSupply

open LeadingRunSupply BoundedExcessSupply BoundedExcessReservoir
open SupplyReservoirGeometry SharpPeriodicSupply

/-! Periodic bounded-excess capacity through disjoint S reservoirs. -/

theorem equal_mod_of_close (a b : Int) (p : Nat) (_hp : 0 < p)
    (hlo : -(p : Int) < a-b) (hhi : a-b < p)
    (heq : a % p = b % p) : a = b := by
  by_cases hab : b ≤ a
  · have h := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp heq
    rw [Int.emod_eq_of_lt (by omega) hhi] at h
    omega
  · have h := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp heq.symm
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
    omega

theorem exact_run_lt_period (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (m : Nat)
    (htA : e t = true)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (htS : e (t-m-1) = false) : m+1 < p := by
  by_cases hlt : m+1 < p
  · exact hlt
  · have hA := run_value e t (t-m-1+p) m htA ha (by omega) (by omega)
    rw [hper] at hA
    rw [htS] at hA
    contradiction

def reservoir (p : Nat) (t : Int) (m : Nat) : List Nat :=
  (List.range (m-1)).map (fun i => phase p (t-m-((i+1 : Nat) : Int)))

theorem reservoir_length (p : Nat) (t : Int) (m : Nat) :
    (reservoir p t m).length = m-1 := by simp [reservoir]

theorem reservoir_nodup (p : Nat) (hp : 0 < p) (t : Int) (m : Nat) (hm : m ≤ p) :
    (reservoir p t m).Nodup := by
  apply LagElevenPeriodic.nodup_map_of_inj List.nodup_range
  intro i j hi hj heq
  have hi' := List.mem_range.mp hi
  have hj' := List.mem_range.mp hj
  have hmod := phase_eq_mod p hp (t-m-((i+1 : Nat) : Int))
    (t-m-((j+1 : Nat) : Int)) heq
  have h := equal_mod_of_close (t-m-((i+1 : Nat) : Int))
    (t-m-((j+1 : Nat) : Int)) p hp (by omega) (by omega) hmod
  omega

theorem phase_value (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) : e (phase p t) = e t := by
  rw [phase_cast p hp]
  have h : t = t % p+(t/p)*p := by have := Int.ediv_mul_add_emod t (p : Int); omega
  calc
    e (t % p) = e (t % p+(t/p)*p) := (LagElevenPeriodic.e_shift e p hper _ _).symm
    _ = e t := congrArg e h.symm


theorem reservoirs_common_phase_eq_mod (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t u : Int) (y : Nat)
    (m n R d d₂ : Nat)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hthresholdt : R*(R+1) < m) (hthresholdu : R*(R+1) < n)
    (hsizet : 2*R < m+1) (hsizeu : 2*R < n+1)
    (htA : e t = true) (huA : e u = true)
    (hat : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hau : ∀ i, i < n → e (u-((i+1 : Nat) : Int)) = true)
    (htS : e (t-m-1) = false) (huS : e (u-n-1) = false)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u d₂)
    (htlo : 4*(m : Int)-1 ≤ d) (hthi : (d : Int) ≤ 4*m-1+4*R)
    (hulo : 4*(n : Int)-1 ≤ d₂) (huhi : (d₂ : Int) ≤ 4*n-1+4*R)
    (hyt : y ∈ reservoir p t m) (hyu : y ∈ reservoir p u n) : t % p = u % p := by
  obtain ⟨i, hi, hiy⟩ := List.mem_map.mp hyt
  obtain ⟨j, hj, hjy⟩ := List.mem_map.mp hyu
  have hi' := List.mem_range.mp hi
  have hj' := List.mem_range.mp hj
  have hmod := phase_eq_mod p hp (t-m-((i+1 : Nat) : Int))
    (u-n-((j+1 : Nat) : Int)) (by omega)
  obtain ⟨k, hk⟩ := lift_equal_mod p _ _ hmod
  have hcur : e (u+k*p) = true := by rw [LagElevenPeriodic.e_shift e p hper]; exact huA
  have hS : e (u+k*p-n-1) = false := by
    have htime : u+k*p-n-1 = (u-n-1)+k*p := by omega
    rw [htime, LagElevenPeriodic.e_shift e p hper]
    exact huS
  have hlead := leading_shift e p hper u k n hau
  have hP := (p2_shift e p hper u k d₂).mpr huP
  have heq := reservoirs_common_point_eq e t (u+k*p) (t-m-((i+1 : Nat) : Int))
    m n R d d₂ hm hn hthresholdt hthresholdu hsizet hsizeu htA hcur hat hlead htS hS
    htP hP htlo hthi hulo huhi (by constructor <;> omega) (by constructor <;> omega)
  rw [heq]
  simp [Int.add_emod]

theorem ones_map_eq_filter_length {α : Type} (f : α → Bool) (l : List α) :
    ones (l.map f) = ((l.filter f).length : Int) := by
  induction l with
  | nil => simp [ones]
  | cons a l ih => cases hf : f a <;> simp [hf, ones, ih] <;> omega

theorem filter_partition_length {α : Type} (f : α → Bool) (l : List α) :
    (l.filter f).length + (l.filter (fun a => !(f a))).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases hf : f a <;> simp [hf] <;> omega

theorem reservoir_A_count (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (d m R : Nat) (hm : 3 ≤ m)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hP : ShortPeriodicSupply.P2 e t d) (hupper : (d : Int) ≤ 4*m-1+4*R) :
    ((reservoir p t m).filter (fun q : Nat => e q)).length ≤ 2*R := by
  have hword : (reservoir p t m).map (fun q : Nat => e q) = past e (t-m) (m-1) := by
    simp only [reservoir, List.map_map, past]
    apply List.map_congr_left
    intro i _
    exact phase_value e p hp hper _
  have hbound := stream_middle_As e t d m R hm ha hP hupper
  rw [← hword, ones_map_eq_filter_length] at hbound
  omega


def rightWing (p : Nat) (b : Int) (L : Nat) : List Nat :=
  (List.range L).map (fun i : Nat => phase p (b+i))

theorem short_source_in_candidates (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (t : Int) (m L u j : Nat) (hult : u < p) (huA : e u = true)
    (hj : 1 ≤ j) (hjL : j ≤ L)
    (hcharge : phase p ((u : Int)-j) ∈ reservoir p t m) :
    u ∈ (reservoir p t m).filter (fun q : Nat => e q) ++ rightWing p (t-m) L := by
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp hcharge
  have hi' := List.mem_range.mp hi
  let q := t-m-((i+1 : Nat) : Int)
  have hmod := phase_eq_mod p hp ((u : Int)-j) q heq.symm
  have hsource : u = phase p (q+j) := by
    have hself : phase p (u : Int) = u := by
      unfold phase
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      simp
    rw [← hself]
    apply congrArg Int.toNat
    change (u : Int) % p = (q+j) % p
    calc
      (u : Int) % p = (((u : Int)-j)+j) % p := by congr 1; omega
      _ = ((((u : Int)-j) % p)+(j : Int) % p) % p := Int.add_emod _ _ _
      _ = (q % p+(j : Int) % p) % p := congrArg (fun z => (z+(j : Int) % p) % p) hmod
      _ = (q+j) % p := (Int.add_emod _ _ _).symm
  by_cases hleft : q+j < t-m
  · apply List.mem_append_left
    apply List.mem_filter.mpr
    refine ⟨?_, huA⟩
    let a := (t-m-(q+j)-1).toNat
    have ha : (a : Int) = t-m-(q+j)-1 := Int.toNat_of_nonneg (by omega)
    have halt : a < m-1 := by dsimp [q] at *; omega
    apply List.mem_map.mpr
    refine ⟨a, List.mem_range.mpr halt, ?_⟩
    have htime : t-m-((a+1 : Nat) : Int) = q+j := by omega
    rw [htime]
    exact hsource.symm
  · apply List.mem_append_right
    let a := (q+j-(t-m)).toNat
    have ha : (a : Int) = q+j-(t-m) := Int.toNat_of_nonneg (by omega)
    have halt : a < L := by dsimp [q] at *; omega
    apply List.mem_map.mpr
    refine ⟨a, List.mem_range.mpr halt, ?_⟩
    have htime : t-m+(a : Int) = q+j := by omega
    rw [htime]
    exact hsource.symm

/-- A finite function cannot cover more distinct targets than candidate sources. -/
theorem exists_unused_target (U B C : List Nat) (f : Nat → Nat) (hB : B.Nodup)
    (hsmall : C.length < B.length)
    (hlocal : ∀ u, u ∈ U → f u ∈ B → u ∈ C) :
    ∃ b, b ∈ B ∧ b ∉ U.map f := by
  classical
  by_cases hex : ∃ b, b ∈ B ∧ b ∉ U.map f
  · exact hex
  · have hsub : B ⊆ C.map f := by
      intro b hb
      have himage : b ∈ U.map f := by
        by_cases hmem : b ∈ U.map f
        · exact hmem
        · exact False.elim (hex ⟨b,hb,hmem⟩)
      obtain ⟨u, hu, heq⟩ := List.mem_map.mp himage
      exact List.mem_map.mpr ⟨u, hlocal u hu (by rw [heq]; exact hb), heq⟩
    have hlen := hB.length_le_of_subset hsub
    simp only [List.length_map] at hlen
    omega

theorem reservoir_has_unused_S (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (m R L d : Nat)
    (hm : 3 ≤ m) (hlarge : 4*R+L+2 ≤ m)
    (htA : e t = true)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (htS : e (t-m-1) = false)
    (hP : ShortPeriodicSupply.P2 e t d) (hupper : (d : Int) ≤ 4*m-1+4*R)
    (U : List Nat) (off : Nat → Nat)
    (hUrange : ∀ u, u ∈ U → u < p) (hUA : ∀ u, u ∈ U → e u = true)
    (hOff : ∀ u, u ∈ U → 1 ≤ off u ∧ off u ≤ L) :
    ∃ q, q ∈ reservoir p t m ∧ e q = false ∧
      q ∉ U.map (fun u : Nat => phase p ((u : Int)-off u)) := by
  let B := (reservoir p t m).filter (fun q : Nat => !(e q))
  let C := (reservoir p t m).filter (fun q : Nat => e q) ++ rightWing p (t-m) L
  have hmlt := exact_run_lt_period e p hp hper t m htA ha htS
  have hB : B.Nodup := (reservoir_nodup p hp t m (by omega)).filter _
  have hcount := reservoir_A_count e p hp hper t d m R hm ha hP hupper
  have hpart := filter_partition_length (fun q : Nat => e q) (reservoir p t m)
  have hlen := reservoir_length p t m
  have hsmall : C.length < B.length := by
    dsimp [C,B]
    simp only [List.length_append, rightWing, List.length_map, List.length_range]
    omega
  have hlocal : ∀ u, u ∈ U → phase p ((u : Int)-off u) ∈ B → u ∈ C := by
    intro u hu hf
    exact short_source_in_candidates e p hp t m L u (off u) (hUrange u hu)
      (hUA u hu) (hOff u hu).1 (hOff u hu).2 (List.mem_filter.mp hf).1
  obtain ⟨q,hq,hunused⟩ := exists_unused_target U B C _ hB hsmall hlocal
  have hq' := List.mem_filter.mp hq
  exact ⟨q,hq'.1, by simpa using hq'.2,hunused⟩


/-- A short injective A-to-S charge extends to all eligible bounded-excess
sources. The new S choices and their injectivity are conclusions of the proof. -/
theorem periodic_capacity_extension (e : Int → Bool) (p L R : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (hp : 0 < p)
    (U Q : List Nat) (run off : Nat → Nat)
    (hUnodup : U.Nodup) (hQnodup : Q.Nodup)
    (hUrange : ∀ u, u ∈ U → u < p) (hQrange : ∀ t, t ∈ Q → t < p)
    (hUA : ∀ u, u ∈ U → e u = true)
    (hOff : ∀ u, u ∈ U → 1 ≤ off u ∧ off u ≤ L)
    (hUS : ∀ u, u ∈ U → e (phase p ((u : Int)-off u)) = false)
    (hUinj : ∀ u v, u ∈ U → v ∈ U →
      phase p ((u : Int)-off u) = phase p ((v : Int)-off v) → u = v)
    (hRun : ∀ t, t ∈ Q → 3 ≤ run t ∧ R*(R+1) < run t ∧ 4*R+L+2 ≤ run t ∧
      e t = true ∧
      (∀ i, i < run t → e ((t : Int)-((i+1 : Nat) : Int)) = true) ∧
      e ((t : Int)-run t-1) = false ∧
      ∃ d, ShortPeriodicSupply.P2 e t d ∧ 4*(run t : Int)-1 ≤ d ∧
        (d : Int) ≤ 4*run t-1+4*R) :
    U.length + Q.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  classical
  let f := fun u : Nat => phase p ((u : Int)-off u)
  have hfree : ∀ t, t ∈ Q → ∃ q, q ∈ reservoir p t (run t) ∧ e q = false ∧ q ∉ U.map f := by
    intro t ht
    have h := hRun t ht
    obtain ⟨d,hP,hlo,hhi⟩ := h.2.2.2.2.2.2
    exact reservoir_has_unused_S e p hp hper t (run t) R L d h.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 hP hhi U off hUrange hUA hOff
  let g := fun t : Nat => if ht : t ∈ Q then Classical.choose (hfree t ht) else 0
  have hg : ∀ t, t ∈ Q → g t ∈ reservoir p t (run t) ∧ e (g t) = false ∧ g t ∉ U.map f := by
    intro t ht
    dsimp [g]
    rw [dif_pos ht]
    exact Classical.choose_spec (hfree t ht)
  have hfn : (U.map f).Nodup := LagElevenPeriodic.nodup_map_of_inj hUnodup hUinj
  have hgn : (Q.map g).Nodup := by
    apply LagElevenPeriodic.nodup_map_of_inj hQnodup
    intro t u ht hu heq
    have htR := hRun t ht
    have huR := hRun u hu
    obtain ⟨d,htP,htlo,hthi⟩ := htR.2.2.2.2.2.2
    obtain ⟨d₂,huP,hulo,huhi⟩ := huR.2.2.2.2.2.2
    have htlarge := htR.2.2.1
    have hularge := huR.2.2.1
    have hmod := reservoirs_common_phase_eq_mod e p hp hper t u (g t)
      (run t) (run u) R d d₂ htR.1 huR.1 htR.2.1 huR.2.1
      (by omega) (by omega) htR.2.2.2.1 huR.2.2.2.1
      htR.2.2.2.2.1 huR.2.2.2.2.1 htR.2.2.2.2.2.1 huR.2.2.2.2.2.1
      htP huP htlo hthi hulo huhi (hg t ht).1 (by rw [heq]; exact (hg u hu).1)
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

end Recaman.BoundedPeriodicSupply
