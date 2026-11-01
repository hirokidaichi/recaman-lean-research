import Recaman.ParitySupply

namespace Recaman.LocalParitySupply

open LeadingRunSupply ParitySupply

/-! Localizing the fixed-parity classification to an individual supply window. -/

def EvenBackA (e : Int → Bool) (t : Int) (d : Nat) : Prop :=
  ∀ i : Nat, 0 < i → i ≤ d → i % 2 = 0 → e (t-i) = true

def extension (e : Int → Bool) (t x : Int) : Bool :=
  if x % 2 = 1 then true else e (t-1+x)

theorem extension_odd (e : Int → Bool) (t n : Int) : extension e t (2*n+1) = true := by
  have h : (2*n+1) % 2 = 1 := by omega
  simp [extension,h]

theorem extension_even (e : Int → Bool) (t n : Int) : extension e t (2*n) = e (t-1+2*n) := by
  have h : (2*n) % 2 = 0 := by omega
  simp [extension,h]

theorem extension_agrees (e : Int → Bool) (t x : Int) (d : Nat)
    (ha : EvenBackA e t d) (hlo : t-d ≤ x) (hhi : x < t) :
    extension e t (x-t+1) = e x := by
  unfold extension
  by_cases hodd : (x-t+1) % 2 = 1
  · rw [if_pos hodd]
    let i := (t-x).toNat
    have hi : (i : Int) = t-x := Int.toNat_of_nonneg (by omega)
    have hisign := ha i (by omega) (by omega) (by omega)
    have htime : t-(i : Int) = x := by omega
    rw [htime] at hisign
    exact hisign.symm
  · rw [if_neg hodd]
    congr 1
    omega

theorem extension_past (e : Int → Bool) (t : Int) (d : Nat) (ha : EvenBackA e t d) :
    past (extension e t) 1 d = past e t d := by
  unfold past
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have h := extension_agrees e t (t-((i+1 : Nat) : Int)) d ha (by omega) (by omega)
  have htime : t-((i+1 : Nat) : Int)-t+1 = 1-((i+1 : Nat) : Int) := by omega
  rwa [htime] at h

theorem extension_subwindow (e : Int → Bool) (t u : Int) (d s : Nat)
    (ha : EvenBackA e t d) (hlo : t-d ≤ u-s) (hhi : u ≤ t) :
    past (extension e t) (u-t+1) s = past e u s := by
  unfold past
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have h := extension_agrees e t (u-((i+1 : Nat) : Int)) d ha (by omega) (by omega)
  have htime : u-((i+1 : Nat) : Int)-t+1 = u-t+1-((i+1 : Nat) : Int) := by omega
  rwa [htime] at h

theorem local_P2_necessary (e : Int → Bool) (t : Int) (d : Nat)
    (ha : EvenBackA e t d) (hP : ShortPeriodicSupply.P2 e t d) :
    ∃ k : Nat, d = 8*k+3 ∧ e (t-((2*k+1 : Nat) : Int)) = true ∧
      ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → e (t-((2*j+1 : Nat) : Int)) = false := by
  have hPe : ShortPeriodicSupply.P2 (extension e t) 1 d := by
    rw [← past_p2_iff, extension_past e t d ha]
    exact (past_p2_iff e t d).mpr hP
  have hPe' : ShortPeriodicSupply.P2 (extension e t) (2*0+1) d := by simpa using hPe
  obtain ⟨k,hd,hA,hS⟩ := odd_P2_necessary (extension e t) (extension_odd e t) 0 d hPe'
  refine ⟨k,hd,?_,?_⟩
  · change extension e t (2*(0-(k : Int))) = true at hA
    rw [extension_even] at hA
    have htime : t-1+2*(0-(k : Int)) = t-((2*k+1 : Nat) : Int) := by omega
    rwa [htime] at hA
  · intro j hj hjk
    have hs := hS j hj hjk
    change extension e t (2*(0-(j : Int))) = false at hs
    rw [extension_even] at hs
    have htime : t-1+2*(0-(j : Int)) = t-((2*j+1 : Nat) : Int) := by omega
    rwa [htime] at hs

theorem local_P2_sufficient (e : Int → Bool) (t : Int) (k : Nat)
    (ha : EvenBackA e t (8*k+3)) (hA : e (t-((2*k+1 : Nat) : Int)) = true)
    (hS : ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → e (t-((2*j+1 : Nat) : Int)) = false) :
    ShortPeriodicSupply.P2 e t (8*k+3) := by
  have hPe := odd_P2_sufficient (extension e t) (extension_odd e t) 0 k (by
    change extension e t (2*(0-(k : Int))) = true
    rw [extension_even]
    have htime : t-1+2*(0-(k : Int)) = t-((2*k+1 : Nat) : Int) := by omega
    rwa [htime]) (by
    intro j hj hjk
    change extension e t (2*(0-(j : Int))) = false
    rw [extension_even]
    have htime : t-1+2*(0-(j : Int)) = t-((2*j+1 : Nat) : Int) := by omega
    rw [htime]
    exact hS j hj hjk)
  have hpast := (past_p2_iff (extension e t) (2*0+1) (8*k+3)).mpr hPe
  change P2 (past (extension e t) 1 (8*k+3)) at hpast
  rw [extension_past e t (8*k+3) ha] at hpast
  exact (past_p2_iff e t (8*k+3)).mp hpast

theorem local_P2_iff (e : Int → Bool) (t : Int) (d : Nat) (ha : EvenBackA e t d) :
    ShortPeriodicSupply.P2 e t d ↔
    ∃ k : Nat, d = 8*k+3 ∧ e (t-((2*k+1 : Nat) : Int)) = true ∧
      ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → e (t-((2*j+1 : Nat) : Int)) = false := by
  constructor
  · exact local_P2_necessary e t d ha
  · rintro ⟨k,rfl,hA,hS⟩
    exact local_P2_sufficient e t k ha hA hS

/-- A clean witness is automatically the minimum P2 witness, even among
shorter windows with no separately supplied cleanliness premise. -/
theorem clean_is_minimum (e : Int → Bool) (t : Int) (d s : Nat)
    (ha : EvenBackA e t d) (hP : ShortPeriodicSupply.P2 e t d)
    (hs : s ≤ d) (hPs : ShortPeriodicSupply.P2 e t s) : s = d := by
  have has : EvenBackA e t s := fun i hi his heven => ha i hi (by omega) heven
  have hlong : ShortPeriodicSupply.P2 (extension e t) 1 d := by
    rw [← past_p2_iff, extension_past e t d ha]
    exact (past_p2_iff e t d).mpr hP
  have hshort : ShortPeriodicSupply.P2 (extension e t) 1 s := by
    rw [← past_p2_iff, extension_past e t s has]
    exact (past_p2_iff e t s).mpr hPs
  exact P2_lag_unique (extension e t) (extension_odd e t) 0 s d hshort hlong

theorem clean_lag_unique (e : Int → Bool) (t : Int) (d s : Nat)
    (had : EvenBackA e t d) (has : EvenBackA e t s)
    (hdP : ShortPeriodicSupply.P2 e t d) (hsP : ShortPeriodicSupply.P2 e t s) : d = s := by
  by_cases hds : d ≤ s
  · exact clean_is_minimum e t s d has hsP hds hdP
  · exact (clean_is_minimum e t d s had hdP (by omega) hsP).symm

theorem local_charge_S (e : Int → Bool) (t : Int) (k : Nat)
    (hS : ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → e (t-((2*j+1 : Nat) : Int)) = false) :
    e (t-4*k-3) = false := by
  have h := hS (2*k+1) (by omega) (by omega)
  have htime : t-((2*(2*k+1)+1 : Nat) : Int) = t-4*k-3 := by omega
  rwa [htime] at h

/-- The parity origins align automatically when the charge positions agree. -/
theorem local_charge_injective (e : Int → Bool) (t u : Int) (k l : Nat)
    (hkA : e (t-((2*k+1 : Nat) : Int)) = true)
    (hkS : ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → e (t-((2*j+1 : Nat) : Int)) = false)
    (hlA : e (u-((2*l+1 : Nat) : Int)) = true)
    (hlS : ∀ j : Nat, j ≤ 4*l+1 → j ≠ l → e (u-((2*j+1 : Nat) : Int)) = false)
    (heq : t-4*k-3 = u-4*l-3) : t = u ∧ k = l := by
  by_cases hkl : k < l
  · have h := hlS (2*l-k) (by omega) (by omega)
    have htime : u-((2*(2*l-k)+1 : Nat) : Int) = t-((2*k+1 : Nat) : Int) := by omega
    rw [htime,hkA] at h
    contradiction
  · by_cases hlk : l < k
    · have h := hkS (2*k-l) (by omega) (by omega)
      have htime : t-((2*(2*k-l)+1 : Nat) : Int) = u-((2*l+1 : Nat) : Int) := by omega
      rw [htime,hlA] at h
      contradiction
    · constructor <;> omega

end Recaman.LocalParitySupply
