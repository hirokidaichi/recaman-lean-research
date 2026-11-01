import Recaman.LocalParityPeriodic
import Recaman.ShortReservoirCapacity

namespace Recaman.ShortLocalParityCapacity

open LeadingRunSupply ParitySupply LocalParitySupply LocalParityPeriodic
open ShortPeriodicSupply LagElevenPeriodic ShortReservoirCapacity SharpPeriodicSupply
open ParityPeriodicSupply (chargePhase)

def offsetAt (e : Int → Bool) (t : Int) : Nat :=
  if supplied (window e t) then phi7Off (window e t)
  else LagElevenSupply.charge (LagElevenSupply.typeOf (maskAt e t))

theorem offsetAt_nat (e : Int → Bool) (u : Nat) : offsetAt e u = shortOff e u := rfl

theorem maskAux_congr (e f : Int → Bool) (t u : Int) (n : Nat)
    (h : ∀ i : Nat, 0 < i → i ≤ n → e (t-i) = f (u-i)) :
    maskAux e t n = maskAux f u n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [maskAux, h (n+1) (by omega) (by omega),
      ih (fun i hi hin => h i hi (by omega))]

theorem offsetAt_congr (e f : Int → Bool) (t u : Int)
    (h : ∀ i : Nat, 0 < i → i ≤ 11 → e (t-i) = f (u-i)) :
    offsetAt e t = offsetAt f u := by
  have h1 := h 1 (by decide) (by decide)
  have h2 := h 2 (by decide) (by decide)
  have h3 := h 3 (by decide) (by decide)
  have h4 := h 4 (by decide) (by decide)
  have h5 := h 5 (by decide) (by decide)
  have h6 := h 6 (by decide) (by decide)
  have h7 := h 7 (by decide) (by decide)
  have hw : window e t = window f u := by
    simp only [Int.cast_ofNat_Int] at h1 h2 h3 h4 h5 h6 h7
    simp only [window, h1,h2,h3,h4,h5,h6,h7]
  have hm := maskAux_congr e f t u 11 h
  simp only [offsetAt, hw, maskAt, hm]

theorem offsetAt_shift (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (t z : Int) :
    offsetAt e (t+z*p) = offsetAt e t := by
  apply offsetAt_congr
  intro i hi hin
  have htime : t+z*p-(i : Int) = (t-i)+z*p := by omega
  rw [htime,e_shift e p hper]

theorem shortOff_bounds_three (e : Int → Bool) (p u : Nat)
    (hu : u ∈ shortPhases e p) : 3 ≤ shortOff e u ∧ shortOff e u ≤ 11 := by
  by_cases hs : supplied (window e u) = true
  · have hb := phi7Off_bounds hs
    simp only [shortOff, hs, ↓reduceIte]
    omega
  · have hmin : LagElevenSupply.minLag11 (maskAt e u) = true := by
      rcases List.mem_append.mp hu with h7 | h11
      · exact False.elim (hs (by simpa using ((mem_u7Phases e 0 p u).mp h7).2.2))
      · simpa using ((mem_u11Phases e 0 p u).mp h11).2.2
    have hm := (typeOf_spec _ (maskAt_lt e u) hmin).1
    have hb := of_decide_eq_true (List.all_eq_true.mp LagElevenSupply.charge_bounds _ hm)
    simp only [shortOff, hs, Bool.false_eq_true, ↓reduceIte]
    omega

theorem global_evenBackA (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (n : Int) (d : Nat) : EvenBackA e (2*n+1) d := by
  intro i hi hid heven
  have htime : 2*n+1-(i : Int) = 2*(n-((i/2 : Nat) : Int))+1 := by omega
  rw [htime]
  exact hfixed _

theorem global_short_offset (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (t : Int) (d : Nat) (hd : d ≤ 11) (hP : ShortPeriodicSupply.P2 e t d) :
    offsetAt e t = (d+3)/2 := by
  obtain ⟨n,rfl⟩ := supplied_phase_is_odd e hfixed t d hP
  obtain ⟨k,rfl,hA,hS⟩ := local_P2_necessary e (2*n+1) d
    (global_evenBackA e hfixed n d) hP
  have hke : k = 0 ∨ k = 1 := by omega
  have heven (i : Nat) : e (2*n+1-((2*i : Nat) : Int)) = true := by
    have htime : 2*n+1-((2*i : Nat) : Int) = 2*(n-i)+1 := by omega
    rw [htime]
    exact hfixed _
  rcases hke with rfl | rfl
  · have h1 : e (2*n+1-1) = true := by simpa using hA
    have h2 : e (2*n+1-2) = true := by simpa using heven 1
    have h3 : e (2*n+1-3) = false := by simpa using hS 1 (by decide) (by decide)
    have hs : supplied (window e (2*n+1)) = true :=
      (supplied_window_iff e (2*n+1)).mpr ⟨3,by decide,by decide,hP⟩
    have hwin : isLag3Win (window e (2*n+1)) = true := by
      simp only [isLag3Win, window_bit e _ 0 (by decide),
        window_bit e _ 1 (by decide),window_bit e _ 2 (by decide)]
      simpa using And.intro (And.intro h1 h2) h3
    simp [offsetAt,hs,phi7Off,hwin]
  · have h1 : e (2*n+1-1) = false := by simpa using hS 0 (by decide) (by decide)
    have h2 : e (2*n+1-2) = true := by simpa using heven 1
    have h3 : e (2*n+1-3) = true := by simpa using hA
    have h4 : e (2*n+1-4) = true := by simpa using heven 2
    have h5 : e (2*n+1-5) = false := by simpa using hS 2 (by decide) (by decide)
    have h6 : e (2*n+1-6) = true := by simpa using heven 3
    have h7 : e (2*n+1-7) = false := by simpa using hS 3 (by decide) (by decide)
    have h8 : e (2*n+1-8) = true := by simpa using heven 4
    have h9 : e (2*n+1-9) = false := by simpa using hS 4 (by decide) (by decide)
    have h10 : e (2*n+1-10) = true := by simpa using heven 5
    have h11 : e (2*n+1-11) = false := by simpa using hS 5 (by decide) (by decide)
    have hs : supplied (window e (2*n+1)) = false := by
      cases hb : supplied (window e (2*n+1))
      · rfl
      · obtain ⟨s,hs0,hs7,hsP⟩ := (supplied_window_iff e (2*n+1)).mp hb
        have hh := P2_lag_unique e hfixed n 11 s hP hsP
        omega
    have hm : maskAt e (2*n+1) = 1361 := by
      have h0 : e (2*n) = false := by simpa using h1
      simp [maskAt,maskAux,h0,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
    rw [offsetAt,hs]
    simp only [Bool.false_eq_true, ↓reduceIte,hm]
    decide

theorem global_line_charge_injective (e : Int → Bool)
    (hfixed : ∀ n : Int, e (2*n+1) = true) (t u : Int) (d s : Nat)
    (hP : ShortPeriodicSupply.P2 e t d) (hS : ShortPeriodicSupply.P2 e u s)
    (heq : t-(((d+3)/2 : Nat) : Int) = u-(((s+3)/2 : Nat) : Int)) :
    t = u ∧ d = s := by
  obtain ⟨n,ht⟩ := supplied_phase_is_odd e hfixed t d hP
  obtain ⟨m,hu⟩ := supplied_phase_is_odd e hfixed u s hS
  have hat : EvenBackA e t d := by rw [ht]; exact global_evenBackA e hfixed n d
  have hau : EvenBackA e u s := by rw [hu]; exact global_evenBackA e hfixed m s
  obtain ⟨k,rfl,hkA,hkS⟩ := local_P2_necessary e t d hat hP
  obtain ⟨l,rfl,hlA,hlS⟩ := local_P2_necessary e u s hau hS
  have hkl := local_charge_injective e t u k l hkA hkS hlA hlS (by omega)
  constructor <;> omega

/-- A short source sharing the long charge would have its full eleven-bit
history inside the long clean window, where the two charge rules coincide. -/
theorem line_images_ne (e : Int → Bool) (t u : Int) (d s : Nat)
    (hd : 19 ≤ d) (ha : EvenBackA e t d) (hP : ShortPeriodicSupply.P2 e t d)
    (hs : s ≤ 11) (hPs : ShortPeriodicSupply.P2 e u s)
    (hoff : 3 ≤ offsetAt e u ∧ offsetAt e u ≤ 11) :
    t-(((d+3)/2 : Nat) : Int) ≠ u-(offsetAt e u : Int) := by
  intro heq
  obtain ⟨k,hdform,_,_⟩ := local_P2_necessary e t d ha hP
  have hk : 2 ≤ k := by omega
  have hlo : t-d ≤ u-11 := by omega
  have hhi : u ≤ t := by omega
  let f := extension e t
  have hf : ∀ n : Int, f (2*n+1) = true := extension_odd e t
  have hlong : ShortPeriodicSupply.P2 f 1 d := by
    rw [← past_p2_iff, extension_past e t d ha]
    exact (past_p2_iff e t d).mpr hP
  have hshort : ShortPeriodicSupply.P2 f (u-t+1) s := by
    rw [← past_p2_iff, extension_subwindow e t u d s ha (by omega) hhi]
    exact (past_p2_iff e u s).mpr hPs
  have hoffeq : offsetAt f (u-t+1) = offsetAt e u := by
    apply offsetAt_congr
    intro i hi hi11
    have h := extension_agrees e t (u-i) d ha (by omega) (by omega)
    have htime : u-(i : Int)-t+1 = u-t+1-i := by omega
    rwa [htime] at h
  have hshortoff := global_short_offset f hf (u-t+1) s hs hshort
  have hcoll := global_line_charge_injective f hf 1 (u-t+1) d s hlong hshort (by omega)
  omega

theorem short_clean_images_ne (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (u : Nat) (t : Int) (d : Nat)
    (hu : u ∈ shortPhases e p) (hd : 19 ≤ d)
    (ha : EvenBackA e t d) (hP : ShortPeriodicSupply.P2 e t d) :
    phase p ((u : Int)-shortOff e u) ≠ chargePhase p t d := by
  intro heq
  have hmod := phase_eq_mod p hp (t-(((d+3)/2 : Nat) : Int))
    ((u : Int)-shortOff e u) heq.symm
  obtain ⟨z,hz⟩ := lift_equal_mod p _ _ hmod
  obtain ⟨s,hs,hPs⟩ := ((mem_shortPhases e p u).mp hu).2.2
  have hPs' := (p2_shift e p hper u z s).mpr hPs
  have hoffshift : offsetAt e ((u : Int)+z*p) = shortOff e u :=
    offsetAt_shift e p hper u z
  have hbounds : 3 ≤ offsetAt e ((u : Int)+z*p) ∧ offsetAt e ((u : Int)+z*p) ≤ 11 := by
    rw [hoffshift]
    exact shortOff_bounds_three e p u hu
  exact line_images_ne e t ((u : Int)+z*p) d s hd ha hP hs hPs' hbounds (by omega)

/-- The complete old short class and every chosen long clean supplied A phase
fit simultaneously into the S phases, without a global parity assumption. -/
theorem short_plus_clean_capacity (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x)
    (Q : List Nat) (hQnodup : Q.Nodup) (hQrange : ∀ t, t ∈ Q → t < p)
    (hQ : ∀ t, t ∈ Q → e t = true ∧ ∃ d : Nat,
      19 ≤ d ∧ ShortPeriodicSupply.P2 e t d ∧ EvenBackA e t d) :
    suppliedCount e 0 p + u11Count e 0 p + Q.length ≤ subtractionCount e 0 p := by
  classical
  let lag := fun t : Nat => if ht : t ∈ Q then Classical.choose (hQ t ht).2 else 0
  have hlag : ∀ t, t ∈ Q → 19 ≤ lag t ∧
      ShortPeriodicSupply.P2 e t (lag t) ∧ EvenBackA e t (lag t) := by
    intro t ht
    dsimp [lag]
    rw [dif_pos ht]
    exact Classical.choose_spec (hQ t ht).2
  let f := fun u : Nat => phase p ((u : Int)-shortOff e u)
  let g := fun t : Nat => chargePhase p t (lag t)
  have hf : ((shortPhases e p).map f).Nodup :=
    nodup_map_of_inj (shortPhases_nodup e p)
      (fun u v hu hv heq => short_phase_injective e p hp hper u v hu hv heq)
  have hg : (Q.map g).Nodup := by
    apply nodup_map_of_inj hQnodup
    intro t u ht hu heq
    have hmod := charge_mod_injective e p hp hper t u (lag t) (lag u)
      (hlag t ht).2.2 (hlag u hu).2.2 (hlag t ht).2.1 (hlag u hu).2.1 heq
    have htr := hQrange t ht
    have hur := hQrange u hu
    rw [Int.emod_eq_of_lt (by omega) (by omega),
      Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  have hdis : ∀ q, q ∈ (shortPhases e p).map f → q ∉ Q.map g := by
    intro q hq hq'
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hq
    obtain ⟨t,ht,heq⟩ := List.mem_map.mp hq'
    exact short_clean_images_ne e p hp hper u t (lag t) hu
      (hlag t ht).1 (hlag t ht).2.2 (hlag t ht).2.1 heq.symm
  have hnodup := nodup_append hf hg hdis
  have hsub : (shortPhases e p).map f ++ Q.map g ⊆ subPhases e 0 p := by
    intro q hq
    apply (mem_subPhases e 0 p q).mpr
    rcases List.mem_append.mp hq with hshort | hlong
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hshort
      exact ⟨phase_lt p hp _,by simpa using short_image_is_S e p hp hper u hu⟩
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hlong
      exact ⟨phase_lt p hp _,by simpa [g] using (charge_is_S e p hp hper t (lag t)
          (hlag t ht).2.2 (hlag t ht).2.1)⟩
  have hlen := hnodup.length_le_of_subset hsub
  simpa [shortPhases,suppliedCount_eq_filter,u11Count_eq_filter,
    subtractionCount_eq_filter,Nat.add_assoc] using hlen

end Recaman.ShortLocalParityCapacity
