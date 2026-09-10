import Recaman.NonpositivePeriodDrift
import Recaman.SeededReplay

namespace Recaman.FiniteSeedPeriodicSupply

open LeadingRunSupply PositivePeriodLag EventualPeriodicSupply NonpositivePeriodDrift

/-! Exact finite-seed reduction, using the repository's actual seeded greedy
continuation. Arbitrary finite histories and absolute starting clocks are allowed. -/

theorem past_agrees_general (g e : Int → Bool) (N t d : Nat)
    (he : ∀ n : Nat, N ≤ n → g n=e n) (hd : d ≤ t) (hN : N ≤ t-d) :
    past g t d=past e t d := by
  unfold past
  apply List.map_congr_left
  intro i hi
  have hi' : i<d := List.mem_range.mp hi
  have hpos : (t : Int)-((i+1 : Nat) : Int)=((t-(i+1) : Nat) : Int) := by omega
  rw [hpos]
  exact he _ (by omega)

theorem general_prefix_blocks (g e : Int → Bool) (b N t p q : Nat)
    (he : ∀ n : Nat, N ≤ n → g n=e n) (hb : b ≤ N)
    (hper : ∀ z : Int, e (z+p)=e z) (ht : N+q*p ≤ t) :
    past g t (t-b) = blocks (past e t p) q ++ past g ((t : Int)-(q*p : Nat)) (t-b-q*p) := by
  have hd : q*p+(t-b-q*p)=t-b := by omega
  have h := past_append g t (q*p) (t-b-q*p)
  rw [hd] at h
  rw [h,past_agrees_general g e N t (q*p) he (by omega) (by omega)]
  have hblock := periodic_past_blocks e p hper t q 0
  have hz : past e (t : Int) 0=[] := rfl
  simp only [Nat.add_zero,hz,List.append_nil] at hblock
  rw [hblock]

theorem general_candidate_growth (x : Nat → Nat) (g e : Int → Bool) (b N p t : Nat)
    (hp : 0<p) (hb : b ≤ N) (ht : N ≤ t)
    (hstep : ∀ n, b ≤ n → (x (n+1) : Int)=x n+((n+1 : Nat) : Int)*ShortPeriodicSupply.sign (g n))
    (he : ∀ n : Nat, N ≤ n → g n=e n) (hper : ∀ z : Int, e (z+p)=e z)
    (hS : 1 ≤ mass (past e 0 p)) (hq : 4*(N+p)+4 ≤ (t-N)/p) :
    (((t-N)/p : Nat) : Int) ≤ (x t : Int)-((t+1 : Nat) : Int) := by
  let q := (t-N)/p
  have hdiv : q*p+(t-N)%p=t-N := by simpa [q,Nat.mul_comm] using Nat.div_add_mod (t-N) p
  have hr : (t-N)%p<p := Nat.mod_lt _ hp
  have htq : N+q*p ≤ t := by omega
  have hw := general_prefix_blocks g e b N t p q he hb hper htq
  have hlen : (blocks (past e t p) q ++ past g ((t : Int)-(q*p : Nat)) (t-b-q*p)).length=t-b := by
    rw [← hw]; simp [past]
  have hs : 1 ≤ mass (past e t p) := by rw [period_mass_constant e p hp hper]; exact hS
  have hg := repeated_word_candidate_growth (past e t p)
    (past g ((t : Int)-(q*p : Nat)) (t-b-q*p)) q (N+p) (t+1 : Nat)
    (by simpa [past] using hp) (by simp [past]) (by simp [past]; omega) hq hs (by rw [hlen]; omega)
  rw [← hw] at hg
  have hv := value_window x g b b (t-b) hstep (by omega)
  have htime : b+(t-b)=t := by omega
  rw [htime] at hv
  have heq : ((t+1 : Nat) : Int)*(mass (past g t (t-b))-1)-moment (past g t (t-b)) =
      (x t : Int)-x b-((t+1 : Nat) : Int) := by grind
  rw [heq] at hg
  omega

def finiteBound (x : Nat → Nat) (N : Nat) (seed : List Nat) : Nat :=
  seed.sum+((List.range (N+1)).map x).sum

theorem nat_member_le_sum (xs : List Nat) (y : Nat) (hy : y ∈ xs) : y ≤ xs.sum := by
  induction xs with
  | nil => simp at hy
  | cons z xs ih =>
    rcases List.mem_cons.mp hy with heq | hmem
    · simp only [List.sum_cons]; omega
    · have h := ih hmem; simp only [List.sum_cons]; omega

theorem seed_le_bound (x : Nat → Nat) (N : Nat) (seed : List Nat) (z : Nat) (hz : z ∈ seed) :
    z ≤ finiteBound x N seed := by
  have h := nat_member_le_sum seed z hz
  dsimp [finiteBound]
  omega

theorem prefix_le_bound (x : Nat → Nat) (N : Nat) (seed : List Nat) (u : Nat) (hu : u ≤ N) :
    x u ≤ finiteBound x N seed := by
  have hm : x u ∈ (List.range (N+1)).map x := List.mem_map.mpr ⟨u,List.mem_range.mpr (by omega),rfl⟩
  have h := nat_member_le_sum _ _ hm
  dsimp [finiteBound]
  omega

/-- The blocker premise is an explicit necessary consequence of the exact
greedy update; the final seeded theorem derives it rather than assuming it. -/
theorem general_late_A_P2 (x : Nat → Nat) (g e : Int → Bool) (seed : List Nat) (b N p t : Nat)
    (hp : 0<p) (hb : b ≤ N) (ht : N ≤ t)
    (hstep : ∀ n, b ≤ n → (x (n+1) : Int)=x n+((n+1 : Nat) : Int)*ShortPeriodicSupply.sign (g n))
    (hblock : ∀ n, b ≤ n → g n=true → x n ≤ n+1 ∨
      (∃ z ∈ seed, x n=z+n+1) ∨ (∃ u, b ≤ u ∧ u ≤ n ∧ x n=x u+n+1))
    (he : ∀ n : Nat, N ≤ n → g n=e n) (hper : ∀ z : Int, e (z+p)=e z)
    (hS : 1 ≤ mass (past e 0 p))
    (hq : finiteBound x N seed+4*(N+p)+5 ≤ (t-N)/p)
    (hlate : (lagBound p : Int)*(lagBound p+4)<4*((t+1 : Nat) : Int)) (hA : e t=true) :
    ∃ d : Nat, 0<d ∧ d<p*(p+1) ∧ ShortPeriodicSupply.P2 e t d := by
  have hg := general_candidate_growth x g e b N p t hp hb ht hstep he hper hS (by omega)
  have hA' : g t=true := (he t ht).trans hA
  have hblk := hblock t (by omega) hA'
  have hu : ∃ u, N ≤ u ∧ u ≤ t ∧ x t=x u+t+1 := by
    rcases hblk with hlow | ⟨z,hz,hzv⟩ | ⟨u,hbu,hut,huv⟩
    · omega
    · have hzB := seed_le_bound x N seed z hz; omega
    · have hNu : N ≤ u := by
        by_cases h : N ≤ u
        · exact h
        · have hB := prefix_le_bound x N seed u (by omega); omega
      exact ⟨u,hNu,hut,huv⟩
  obtain ⟨u,hNu,hut,huv⟩ := hu
  have hd : 0<t-u := by
    by_cases h : u=t
    · rw [h] at huv; omega
    · omega
  have hv := value_window x g b u (t-u) hstep (by omega)
  have htime : u+(t-u)=t := by omega
  rw [htime,past_agrees_general g e N t (t-u) he (by omega) (by omega)] at hv
  have huv' : (x t : Int)-x u=((t+1 : Nat) : Int) := by omega
  have hc : moment (past e t (t-u))=((t+1 : Nat) : Int)*(mass (past e t (t-u))-1) := by grind
  have hs : 1 ≤ mass (past e t p) := by rw [period_mass_constant e p hp hper]; exact hS
  have hP := late_periodic_collision_P2 e p hp hper t (t-u) (t+1 : Nat) hs (by omega) hc hlate
  exact ⟨t-u,hd,(PeriodicTailRepresentation.positive_period_P2_cutoff e p hp hper hS t (t-u) hP).2,hP⟩

theorem exists_large_phase (e : Int → Bool) (p L : Nat) (hp : 0<p)
    (hper : ∀ z : Int, e (z+p)=e z) (t : Int) :
    ∃ n : Nat, L ≤ n ∧ e n=e t ∧
      ∀ d : Nat, ShortPeriodicSupply.P2 e n d ↔ ShortPeriodicSupply.P2 e t d := by
  let r : Nat := (t%(p : Int)).toNat
  let n : Nat := r+(L+1)*p
  have hrc : (r : Int)=t%p := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hnc : (n : Int)=(r : Int)+((L+1 : Nat) : Int)*p := by simp [n]
  have htc : t=(r : Int)+(t/p)*p := by have h:=Int.ediv_mul_add_emod t (p : Int); omega
  have hn : L ≤ n := by have h:=Nat.le_mul_of_pos_right (L+1) hp; dsimp [n]; omega
  refine ⟨n,hn,?_,?_⟩
  · rw [hnc,htc,LagElevenPeriodic.e_shift e p hper,LagElevenPeriodic.e_shift e p hper]
  · intro d
    rw [hnc,htc,SharpPeriodicSupply.p2_shift e p hper,SharpPeriodicSupply.p2_shift e p hper]

theorem general_finite_history_supply (x : Nat → Nat) (g e : Int → Bool) (seed : List Nat) (b N p : Nat)
    (hp : 0<p) (hb : b ≤ N)
    (hstep : ∀ n, b ≤ n → (x (n+1) : Int)=x n+((n+1 : Nat) : Int)*ShortPeriodicSupply.sign (g n))
    (hblock : ∀ n, b ≤ n → g n=true → x n ≤ n+1 ∨
      (∃ z ∈ seed, x n=z+n+1) ∨ (∃ u, b ≤ u ∧ u ≤ n ∧ x n=x u+n+1))
    (he : ∀ n : Nat, N ≤ n → g n=e n) (hper : ∀ z : Int, e (z+p)=e z) :
    1 ≤ mass (past e 0 p) ∧
    ∀ t : Int, e t=true → ∃ d : Nat, 0<d ∧ d<p*(p+1) ∧ ShortPeriodicSupply.P2 e t d := by
  have hS := period_mass_positive x e N p hp (by
    intro n hn
    have h := hstep n (by omega)
    rw [he n hn] at h
    exact h) hper
  refine ⟨hS,?_⟩
  intro t hA
  let Q := finiteBound x N seed+4*(N+p)+5
  let L := N+Q*p+lagBound p*(lagBound p+4)+1
  obtain ⟨n,hn,hne,hPn⟩ := exists_large_phase e p L hp hper t
  have hnN : N ≤ n := by dsimp [L] at hn; omega
  have hq : finiteBound x N seed+4*(N+p)+5 ≤ (n-N)/p := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    change Q*p ≤ n-N
    dsimp [L] at hn
    omega
  have hlate : (lagBound p : Int)*(lagBound p+4)<4*((n+1 : Nat) : Int) := by
    have hnat : lagBound p*(lagBound p+4)<n := by dsimp [L] at hn; omega
    have hc : ((lagBound p*(lagBound p+4) : Nat) : Int)=(lagBound p : Int)*(lagBound p+4) := by simp
    omega
  obtain ⟨d,hd,hcut,hP⟩ := general_late_A_P2 x g e seed b N p n hp hb hnN
    hstep hblock he hper hS hq hlate (hne.trans hA)
  exact ⟨d,hd,hcut,(hPn d).mp hP⟩

def absoluteValue (b : Nat) (s : State) (n : Nat) : Nat := (SeededReplay.run b s (n-b)).value

def absoluteSign (b : Nat) (s : State) (t : Int) : Bool :=
  decide (¬ CanSubtract (t.toNat+1) (SeededReplay.run b s (t.toNat-b)))

theorem absoluteSign_nat (b : Nat) (s : State) (n : Nat) :
    absoluteSign b s n=decide (¬ CanSubtract (n+1) (SeededReplay.run b s (n-b))) := by
  simp [absoluteSign]

theorem absolute_run_succ (b : Nat) (s : State) (n : Nat) (hn : b ≤ n) :
    SeededReplay.run b s (n+1-b)=step (n+1) (SeededReplay.run b s (n-b)) := by
  have ht : n+1-b=(n-b)+1 := by omega
  rw [ht,SeededReplay.run]
  have hc : b+(n-b)+1=n+1 := by omega
  rw [hc]

theorem seeded_signed_step (b : Nat) (s : State) (n : Nat) (hn : b ≤ n) :
    (absoluteValue b s (n+1) : Int)=absoluteValue b s n+
      ((n+1 : Nat) : Int)*ShortPeriodicSupply.sign (absoluteSign b s n) := by
  rw [absoluteSign_nat]
  unfold absoluteValue
  rw [absolute_run_succ b s n hn]
  by_cases hcan : CanSubtract (n+1) (SeededReplay.run b s (n-b))
  · rw [step_of_subtract hcan]
    have hp := hcan.1
    simp [hcan,ShortPeriodicSupply.sign]
    omega
  · simp [step,nextValue,hcan,ShortPeriodicSupply.sign]

theorem seeded_history_cases (b : Nat) (s : State) (k z : Nat)
    (hz : z ∈ (SeededReplay.run b s k).seen) :
    z ∈ s.seen ∨ ∃ j, j ≤ k ∧ z=(SeededReplay.run b s j).value := by
  induction k with
  | zero => exact Or.inl hz
  | succ k ih =>
    change z ∈ nextValue (b+k+1) (SeededReplay.run b s k) :: (SeededReplay.run b s k).seen at hz
    rcases List.mem_cons.mp hz with hnew | hold
    · exact Or.inr ⟨k+1,by omega,hnew⟩
    · rcases ih hold with hseed | ⟨j,hj,hjv⟩
      · exact Or.inl hseed
      · exact Or.inr ⟨j,by omega,hjv⟩

theorem seeded_addition_obstruction (b : Nat) (s : State) (n : Nat) (hn : b ≤ n)
    (hA : absoluteSign b s n=true) :
    absoluteValue b s n ≤ n+1 ∨
      (∃ z ∈ s.seen, absoluteValue b s n=z+n+1) ∨
      (∃ u, b ≤ u ∧ u ≤ n ∧ absoluteValue b s n=absoluteValue b s u+n+1) := by
  rw [absoluteSign_nat] at hA
  have hnot : ¬ CanSubtract (n+1) (SeededReplay.run b s (n-b)) := of_decide_eq_true hA
  by_cases hlo : absoluteValue b s n ≤ n+1
  · exact Or.inl hlo
  · have hseen : absoluteValue b s n-(n+1) ∈ (SeededReplay.run b s (n-b)).seen := by
      by_cases hm : absoluteValue b s n-(n+1) ∈ (SeededReplay.run b s (n-b)).seen
      · exact hm
      · exact False.elim (hnot ⟨by change n+1 < absoluteValue b s n; omega,hm⟩)
    rcases seeded_history_cases b s (n-b) _ hseen with hseed | ⟨j,hj,hjv⟩
    · exact Or.inr (Or.inl ⟨absoluteValue b s n-(n+1),hseed,by omega⟩)
    · have hval : absoluteValue b s (b+j)=(SeededReplay.run b s j).value := by simp [absoluteValue]
      exact Or.inr (Or.inr ⟨b+j,by omega,by omega,by omega⟩)

/-- Full finite-state version of E-065. Arbitrary finite initial history,
starting value, starting clock, and later preperiod are permitted. -/
theorem seeded_eventual_supply (b : Nat) (s : State) (N p : Nat) (hb : b ≤ N) (hp : 0<p)
    (hper : ∀ n : Nat, N ≤ n → absoluteSign b s ((n+p : Nat) : Int)=absoluteSign b s n) :
    let e := PeriodicTailRepresentation.extension (fun n : Nat => absoluteSign b s n) N p
    1 ≤ mass (past e 0 p) ∧
    ∀ t : Int, e t=true → ∃ d : Nat, 0<d ∧ d<p*(p+1) ∧ ShortPeriodicSupply.P2 e t d := by
  let e := PeriodicTailRepresentation.extension (fun n : Nat => absoluteSign b s n) N p
  have he : ∀ n : Nat, N ≤ n → absoluteSign b s n=e n := by
    intro n hn
    exact (PeriodicTailRepresentation.extension_agrees (fun n : Nat => absoluteSign b s n) N p hp hper n hn).symm
  exact general_finite_history_supply (absoluteValue b s) (absoluteSign b s) e s.seen b N p hp hb
    (seeded_signed_step b s) (seeded_addition_obstruction b s) he
    (PeriodicTailRepresentation.extension_periodic _ N p)

theorem canonical_seed_run (n : Nat) : SeededReplay.run 0 initial n=stateAt n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [SeededReplay.run,stateAt,ih]

theorem canonical_seed_sign (n : Nat) : absoluteSign 0 initial n=CanonicalSSFreeSupply.canonicalSign n := by
  rw [absoluteSign_nat,CanonicalSSFreeSupply.canonicalSign_nat]
  simp [canonical_seed_run]

end Recaman.FiniteSeedPeriodicSupply
