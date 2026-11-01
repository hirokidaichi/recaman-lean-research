import Recaman.PeriodicTailRepresentation

namespace Recaman.NonpositivePeriodDrift

open LeadingRunSupply PositivePeriodLag EventualPeriodicSupply CanonicalSSFreeSupply

/-! Value nonnegativity, rather than candidate nonnegativity, rules out a
nonpositive eventual period mass. The walk need not obey a greedy rule. -/

theorem value_window (x : Nat → Nat) (e : Int → Bool) (N u d : Nat)
    (hstep : ∀ n, N ≤ n → (x (n+1) : Int) = x n+((n+1 : Nat) : Int)*ShortPeriodicSupply.sign (e n))
    (hu : N ≤ u) :
    (x (u+d) : Int)-x u = ((u+d+1 : Nat) : Int)*mass (past e (u+d : Nat) d)-
      moment (past e (u+d : Nat) d) := by
  induction d with
  | zero => simp [past,moment]
  | succ d ih =>
    have h := hstep (u+d) (by omega)
    have htime : ((u+(d+1) : Nat) : Int)-1=((u+d : Nat) : Int) := by omega
    have hn : u+(d+1)=u+d+1 := by omega
    rw [ParitySupply.past_succ,htime]
    simp only [mass_cons,moment,hn]
    have hc : ((u+d+1+1 : Nat) : Int) = ((u+d+1 : Nat) : Int)+1 := by omega
    rw [hc]
    grind

theorem repeated_value_polynomial (x : Nat → Nat) (e : Int → Bool) (N n p q : Nat)
    (hstep : ∀ j, N ≤ j → (x (j+1) : Int) = x j+((j+1 : Nat) : Int)*ShortPeriodicSupply.sign (e j))
    (hn : N ≤ n) (hper : ∀ t : Int, e (t+p)=e t) :
    2*(x (n+q*p) : Int) = 2*(x n : Int)+
      2*(q : Int)*(((n+1 : Nat) : Int)*mass (past e n p)-moment (past e n p))+
      (p : Int)*mass (past e n p)*q*(q+1) := by
  have hw := value_window x e N n (q*p) hstep hn
  have hpast := periodic_past_blocks e p hper (n+q*p : Nat) q 0
  have hz : past e (n+q*p : Nat) 0=[] := rfl
  simp only [Nat.add_zero,hz,List.append_nil] at hpast
  have htime : ((n+q*p : Nat) : Int) = (n : Int)+(q : Int)*p := by simp
  have hs := SharpPeriodicSupply.past_shift e p hper n q p
  rw [← htime] at hs
  rw [hs] at hpast
  rw [hpast,blocks_mass] at hw
  have hM := blocks_moment (past e n p) q
  have hl : (past e n p).length=p := by simp [past]
  rw [hl] at hM
  have hcast : ((n+q*p+1 : Nat) : Int) = ((n+1 : Nat) : Int)+(q : Int)*p := by simp; grind
  rw [hcast] at hw
  grind

/-- A negative quadratic leading coefficient cannot stay nonnegative on all
natural q. Its lower-order coefficient is unrestricted. -/
theorem nonnegative_quadratic_mass (X : Nat) (L S : Int) (p : Nat) (hp : 0 < p)
    (h : ∀ q : Nat, 0 ≤ 2*(X : Int)+2*(q : Int)*L+(p : Int)*S*q*(q+1)) : 0 ≤ S := by
  by_cases hs : 0 ≤ S
  · exact hs
  · let k : Nat := L.toNat
    let q : Nat := 2*X+2*k+4
    have hL : L ≤ (k : Int) := by dsimp [k]; omega
    have hq : (q : Int)=2*(X : Int)+2*(k : Int)+4 := by simp [q]
    have hpS : (p : Int)*S ≤ -1 := by
      have hm := Int.mul_le_mul_of_nonneg_right (show S ≤ -1 by omega) (show 0 ≤ (p : Int) by omega)
      have heq : S*(p : Int)=(p : Int)*S := Int.mul_comm _ _
      omega
    have hquad := Int.mul_le_mul_of_nonneg_right hpS
      (Int.mul_nonneg (show 0 ≤ (q : Int) by omega) (show 0 ≤ (q : Int)+1 by omega))
    have hlin := Int.mul_le_mul_of_nonneg_left hL (show 0 ≤ 2*(q : Int) by omega)
    have hqprod := Int.mul_le_mul_of_nonneg_left
      (show 1 ≤ (q : Int)+1-2*k by omega) (show 0 ≤ (q : Int) by omega)
    have hh := h q
    have heq : 2*(X : Int)+2*(q : Int)*k-(q : Int)*(q+1) =
      2*(X : Int)-(q : Int)*(q+1-2*k) := by grind
    have hquad' : (p : Int)*S*q*(q+1) ≤ -(q : Int)*(q+1) := by grind
    have hneg : -(q : Int)*(q+1) = -((q : Int)*(q+1)) := by grind
    omega

theorem period_mass_nonnegative (x : Nat → Nat) (e : Int → Bool) (N p : Nat) (hp : 0 < p)
    (hstep : ∀ n, N ≤ n → (x (n+1) : Int) = x n+((n+1 : Nat) : Int)*ShortPeriodicSupply.sign (e n))
    (hper : ∀ t : Int, e (t+p)=e t) : 0 ≤ mass (past e 0 p) := by
  have h := nonnegative_quadratic_mass (x N)
    (((N+1 : Nat) : Int)*mass (past e N p)-moment (past e N p))
    (mass (past e N p)) p hp (by
      intro q
      have heq := repeated_value_polynomial x e N N p q hstep (by omega) hper
      omega)
  rw [period_mass_constant e p hp hper] at h
  exact h

theorem balanced_moment_nonpositive (x : Nat → Nat) (e : Int → Bool) (N p n : Nat) (hp : 0 < p)
    (hstep : ∀ j, N ≤ j → (x (j+1) : Int) = x j+((j+1 : Nat) : Int)*ShortPeriodicSupply.sign (e j))
    (hn : N ≤ n) (hper : ∀ t : Int, e (t+p)=e t) (hS : mass (past e 0 p)=0) :
    moment (past e n p) ≤ 0 := by
  have hs : mass (past e n p)=0 := (period_mass_constant e p hp hper n).trans hS
  have h := repeated_value_polynomial x e N n p (x n+1) hstep hn hper
  rw [hs] at h
  simp only [Int.mul_zero,Int.zero_mul,Int.zero_sub,Int.add_zero,Int.natCast_add,Int.cast_ofNat_Int] at h
  by_cases hB : moment (past e n p) ≤ 0
  · exact hB
  · have hpB := Int.mul_le_mul_of_nonneg_left (show 1 ≤ moment (past e n p) by omega)
      (show 0 ≤ (x n : Int)+1 by omega)
    grind

theorem sum_map_add {α : Type} (xs : List α) (f g : α → Int) :
    (xs.map fun x => f x+g x).sum = (xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

theorem sum_map_mul {α : Type} (xs : List α) (c : Int) (f : α → Int) :
    (xs.map fun x => c*f x).sum = c*(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; grind

theorem sum_map_zero {α : Type} (xs : List α) : (xs.map fun _ => (0 : Int)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa using ih

theorem sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Int) :
    (xs.map fun x => (ys.map (f x)).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil => simp [sum_map_zero]
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; exact (sum_map_add ys _ _).symm

theorem signSum_map (e : Int → Bool) (t : Int) (d : Nat) :
    ShortPeriodicSupply.signSum e t d =
      ((List.range d).map fun i : Nat => ShortPeriodicSupply.sign (e (t+i))).sum := by
  induction d with
  | zero => rfl
  | succ d ih => simp [ShortPeriodicSupply.signSum,List.range_succ,ih]

theorem shifted_period_sign_sum (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ t : Int, e (t+p)=e t) (c : Int) :
    ((List.range p).map fun t : Nat => ShortPeriodicSupply.sign (e ((t : Int)+c))).sum =
      mass (past e 0 p) := by
  let f : Int → Bool := fun x => e (x+c)
  have hw := (FiniteP2Semantics.window_prefix_identities f 0 p).1
  simp only [Nat.zero_add,ShortPeriodicSupply.signSum,Int.sub_zero] at hw
  have heq : past f p p = past e ((p : Int)+c) p := by
    unfold past
    apply List.map_congr_left
    intro i _
    dsimp [f]
    congr 1
    omega
  rw [heq,period_mass_constant e p hp hper] at hw
  rw [signSum_map] at hw
  have hm : ((List.range p).map fun i : Nat => ShortPeriodicSupply.sign (f (0+i))).sum =
      ((List.range p).map fun i : Nat => ShortPeriodicSupply.sign (e ((i : Int)+c))).sum := by simp [f]
  rw [hm] at hw
  exact hw.symm

/-- Exact balanced value-moment average; no candidate drift is used. -/
theorem balanced_phase_moment_sum (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ t : Int, e (t+p)=e t) (hS : mass (past e 0 p)=0) :
    ((List.range p).map fun t : Nat => moment (past e t p)).sum = 0 := by
  have hm (t : Nat) : moment (past e t p) =
      ((List.range p).map fun i : Nat => ((i+1 : Nat) : Int)*ShortPeriodicSupply.sign
        (e ((t : Int)-((i+1 : Nat) : Int)))).sum := moment_map_range _ _
  have houter := List.map_congr_left (l:=List.range p) (fun t _ => hm t)
  rw [houter,sum_swap]
  have hz (i : Nat) : ((List.range p).map fun t : Nat => ((i+1 : Nat) : Int)*
      ShortPeriodicSupply.sign (e ((t : Int)-((i+1 : Nat) : Int)))).sum = 0 := by
    rw [sum_map_mul]
    have hs := shifted_period_sign_sum e p hp hper (-((i+1 : Nat) : Int))
    simp only [← Int.sub_eq_add_neg,hS] at hs
    rw [hs]; simp
  have heq := List.map_congr_left (l:=List.range p) (fun i _ => hz i)
  rw [heq]
  exact sum_map_zero _

theorem sum_nonpositive (xs : List Int) (h : ∀ x ∈ xs, x ≤ 0) : xs.sum ≤ 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [List.sum_cons]
    omega

theorem member_zero_of_nonpositive_sum (xs : List Int) (h : ∀ x ∈ xs, x ≤ 0)
    (hs : xs.sum=0) (y : Int) (hy : y ∈ xs) : y=0 := by
  induction xs with
  | nil => simp at hy
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ z ∈ xs, z ≤ 0 := by intro z hz; exact h z (by simp [hz])
    have hts := sum_nonpositive xs ht
    simp only [List.sum_cons] at hs
    have hx0 : x=0 := by omega
    have hts0 : xs.sum=0 := by omega
    rcases List.mem_cons.mp hy with heq | hmem
    · omega
    · exact ih ht hts0 hmem

theorem period_moment_succ (e : Int → Bool) (p : Nat)
    (hper : ∀ t : Int, e (t+p)=e t) (t : Int) :
    moment (past e (t+1) p)-moment (past e t p) =
      mass (past e t p)-(p : Int)*ShortPeriodicSupply.sign (e t) := by
  have hl := congrArg moment (ParitySupply.past_succ e (t+1) p)
  have hr := congrArg moment (past_append e (t+1) p 1)
  have ht : t+1-1=t := by omega
  rw [ht] at hl
  simp only [moment] at hl
  rw [moment_append] at hr
  have hpast : (past e (t+1) p).length=p := by simp [past]
  rw [hpast] at hr
  have he := hper (t-p)
  have heq : t-(p : Int)+p=t := by omega
  rw [heq] at he
  have hs : past e (t+1-p) 1 = [e t] := by
    have htime : t+1-(p : Int)-1=t-p := by omega
    simp [past,htime,he]
  rw [hs] at hr
  simp only [moment,mass_cons,mass_nil,Int.add_zero] at hr
  omega

theorem period_mass_positive (x : Nat → Nat) (e : Int → Bool) (N p : Nat) (hp : 0 < p)
    (hstep : ∀ n, N ≤ n → (x (n+1) : Int) = x n+((n+1 : Nat) : Int)*ShortPeriodicSupply.sign (e n))
    (hper : ∀ t : Int, e (t+p)=e t) : 1 ≤ mass (past e 0 p) := by
  have hnonneg := period_mass_nonnegative x e N p hp hstep hper
  by_cases hpos : 1 ≤ mass (past e 0 p)
  · exact hpos
  · have hS : mass (past e 0 p)=0 := by omega
    have hB (t : Nat) : moment (past e t p) ≤ 0 := by
      let n := t+(N+1)*p
      have hm := Nat.le_mul_of_pos_right (N+1) hp
      have hn : N ≤ n := by dsimp [n]; omega
      have h := balanced_moment_nonpositive x e N p n hp hstep hn hper hS
      have hnc : (n : Int)=(t : Int)+((N+1 : Nat) : Int)*p := by simp [n]
      rw [hnc,SharpPeriodicSupply.past_shift e p hper] at h
      exact h
    have hsum := balanced_phase_moment_sum e p hp hper hS
    have hzero (t : Nat) (ht : t < p) : moment (past e t p)=0 := by
      apply member_zero_of_nonpositive_sum _ ?_ hsum _ ?_
      · intro y hy
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy
        exact hB j
      · exact List.mem_map.mpr ⟨t,List.mem_range.mpr ht,rfl⟩
    have h0 := hzero 0 hp
    change moment (past e 0 p)=0 at h0
    have hl := hzero (p-1) (by omega)
    have hlast := period_moment_succ e p hper ((p-1 : Nat) : Int)
    have heq : ((p-1 : Nat) : Int)+1=(p : Int) := by omega
    rw [heq,hl,period_mass_constant e p hp hper,hS] at hlast
    have hshift := SharpPeriodicSupply.past_shift e p hper 0 1 p
    simp only [Int.one_mul,Int.zero_add] at hshift
    rw [hshift,h0] at hlast
    cases hb : e ((p-1 : Nat) : Int) <;> simp [hb,ShortPeriodicSupply.sign] at hlast <;> omega

theorem canonical_signed_step (n : Nat) :
    (a (n+1) : Int) = a n+((n+1 : Nat) : Int)*ShortPeriodicSupply.sign (canonicalSign n) := by
  have hs := FiniteP2Semantics.canonical_value_prefix (n+1)
  have hn := FiniteP2Semantics.canonical_value_prefix n
  simp only [ShortPeriodicSupply.signSum,FiniteP2Semantics.weightedPrefix,Int.zero_add] at hs
  have hcast : ((n+1 : Nat) : Int) = (n : Int)+1 := by omega
  rw [hcast]
  grind

/-- Nonpositive drift is ruled out from natural eventual periodicity alone. -/
theorem canonical_eventual_mass_positive (N p : Nat) (hp : 0 < p)
    (hper : ∀ n : Nat, N ≤ n → canonicalSign ((n+p : Nat) : Int)=canonicalSign n) :
    1 ≤ mass (past canonicalSign ((N+p : Nat) : Int) p) := by
  let e := PeriodicTailRepresentation.extension (fun n : Nat => canonicalSign n) N p
  have he : ∀ n : Nat, N ≤ n → canonicalSign n=e n := by
    intro n hn
    exact (PeriodicTailRepresentation.extension_agrees (fun n : Nat => canonicalSign n) N p hp hper n hn).symm
  have hep : ∀ t : Int, e (t+p)=e t := PeriodicTailRepresentation.extension_periodic _ N p
  have hstep : ∀ n, N ≤ n → (a (n+1) : Int)=a n+((n+1 : Nat) : Int)*ShortPeriodicSupply.sign (e n) := by
    intro n hn
    have h := canonical_signed_step n
    rw [he n hn] at h
    exact h
  have hs := period_mass_positive a e N p hp hstep hep
  have hw := past_agrees e N (N+p) p he (by omega) (by omega)
  rw [hw,period_mass_constant e p hp hep]
  exact hs

/-- Complete canonical eventual-periodic reduction, with all three possible
sign sums handled and with the original complete finite lag cutoff. -/
theorem canonical_eventual_supply (N p : Nat) (hp : 0 < p)
    (hper : ∀ n : Nat, N ≤ n → canonicalSign ((n+p : Nat) : Int)=canonicalSign n) :
    let e := PeriodicTailRepresentation.extension (fun n : Nat => canonicalSign n) N p
    1 ≤ mass (past e 0 p) ∧
    ∀ t : Int, e t=true → ∃ d : Nat, 0<d ∧ d<p*(p+1) ∧ ShortPeriodicSupply.P2 e t d := by
  let e := PeriodicTailRepresentation.extension (fun n : Nat => canonicalSign n) N p
  have he : ∀ n : Nat, N ≤ n → canonicalSign n=e n := by
    intro n hn
    exact (PeriodicTailRepresentation.extension_agrees (fun n : Nat => canonicalSign n) N p hp hper n hn).symm
  have hep : ∀ t : Int, e (t+p)=e t := PeriodicTailRepresentation.extension_periodic _ N p
  have hs := canonical_eventual_mass_positive N p hp hper
  have hw := past_agrees e N (N+p) p he (by omega) (by omega)
  have hs0 : 1 ≤ mass (past e 0 p) := by
    rw [hw,period_mass_constant e p hp hep] at hs
    exact hs
  exact ⟨hs0,PeriodicTailRepresentation.canonical_natural_eventual_supply N p hp hper hs⟩

end Recaman.NonpositivePeriodDrift
