import Recaman.TwoRunSupply

namespace Recaman.RunSupplyBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem runKey_prepend_A (k : Nat) (v : List Bool) :
    runKey (List.replicate k true++v)=runKey v+4*(k : Int)*(cntF v : Int) := by
  have ha := twice_area_replicate_A k
  have hc := cntF_int v
  have hm := mass_eq v
  simp only [runKey,areaW_append,mass_append,mass_replicate_A]
  grind

theorem runKey_prepend_S (k : Nat) (v : List Bool) :
    runKey (List.replicate k false++v)=runKey v-4*(k : Int)*(cntF v : Int)-2*(k : Int)^2 := by
  have ha := twice_area_replicate_S k
  have hc := cntF_int v
  have hm := mass_eq v
  simp only [runKey,areaW_append,mass_append,mass_rep_false]
  grind

/-- A fixed constant run contributes at most one suffix with key-2. -/
theorem constant_run_root_unique (b : Bool) (k l : Nat) (v : List Bool)
    (hk : 1≤k) (hl : 1≤l)
    (hkeyk : runKey (List.replicate k b++v)=-2)
    (hkeyl : runKey (List.replicate l b++v)=-2) : k=l := by
  cases b
  · rw [runKey_prepend_S] at hkeyk hkeyl
    have hz : ((k : Int)-(l : Int))*(4*(cntF v : Int)+2*((k : Int)+(l : Int)))=0 := by grind
    have hp : 0<4*(cntF v : Int)+2*((k : Int)+(l : Int)) := by omega
    rcases Int.mul_eq_zero.mp hz with h|h <;> omega
  · rw [runKey_prepend_A] at hkeyk hkeyl
    have hc : 0<(cntF v : Int) := by
      have hb := runKey_count_lower v
      by_cases h0 : cntF v=0
      · rw [h0] at hkeyk hb
        simp at hkeyk hb
        omega
      · omega
    have hz : ((k : Int)-(l : Int))*(4*(cntF v : Int))=0 := by grind
    rcases Int.mul_eq_zero.mp hz with h|h <;> omega

theorem cN_or_le (P Q : Nat → Prop) (K : Nat) :
    cN (fun i => P i ∨ Q i) 0 K≤cN P 0 K+cN Q 0 K := by
  classical
  induction K with
  | zero => simp [cN]
  | succ K ih =>
      by_cases hp : P K <;> by_cases hq : Q K <;>
        simp [cN,Nat.zero_add,hp,hq] <;> omega

theorem cN_le_one_of_unique (P : Nat → Prop) (K : Nat)
    (hu : ∀ i, i<K → ∀ j, j<K → P i → P j → i=j) : cN P 0 K≤1 := by
  induction K with
  | zero => simp [cN]
  | succ K ih =>
      by_cases hp : P K
      · have hz : cN P 0 K=0 := by
          apply cN_zero_of
          intro i _ hi hpi
          have he := hu i (by omega) K (by omega) hpi hp
          omega
        rw [cN_succ_pos P 0 K (by simpa using hp),hz]
        omega
      · rw [cN_succ_neg P 0 K (by simpa using hp)]
        exact ih (fun i hi j hj hpi hpj => hu i (by omega) j (by omega) hpi hpj)

private theorem ray_supply_const_iff (b : Bool) (N : Nat) (v : List Bool) (i : Nat) :
    Recaman.ThreeNonsuppliedData.localSupply ((List.replicate N b++v)++List.replicate i true)=true ↔
      (∃ k, 1≤k ∧ k≤N ∧ mass (List.replicate k b++v)+(i : Int)=1 ∧
        runKey (List.replicate k b++v)=-2) ∨
      Recaman.ThreeNonsuppliedData.localSupply (v++List.replicate i true)=true := by
  let P := fun w : List Bool => mass w+(i : Int)=1 ∧ runKey w=-2
  have h1 : Recaman.ThreeNonsuppliedData.localSupply
      ((List.replicate N b++v)++List.replicate i true)=true ↔
      ∃ t, t<(List.replicate N b++v).length ∧ P ((List.replicate N b++v).drop t) := by
    simpa [P] using localSupply_A_S_iff (List.replicate N b++v) i 0
  have h2 : Recaman.ThreeNonsuppliedData.localSupply (v++List.replicate i true)=true ↔
      ∃ t, t<v.length ∧ P (v.drop t) := by
    simpa [P] using localSupply_A_S_iff v i 0
  rw [h1,exists_drop_append _ _ P]
  have hrep : (∃ t, t<(List.replicate N b).length ∧ P ((List.replicate N b).drop t++v)) ↔
      ∃ k, 1≤k ∧ k≤N ∧ P (List.replicate k b++v) := by
    simp only [List.length_replicate,List.drop_replicate]
    constructor
    · rintro ⟨t,ht,hp⟩
      exact ⟨N-t,by omega,by omega,hp⟩
    · rintro ⟨k,hk,hkN,hp⟩
      exact ⟨N-k,by omega,by simpa only [show N-(N-k)=k by omega] using hp⟩
  rw [hrep,←h2]

noncomputable def rayCount (w : List Bool) (K : Nat) : Nat :=
  cN (fun i => Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true)=true) 0 K

/-- Removing one constant prefix block reduces the A-ray supply budget by
at most one, regardless of the block's length. -/
theorem rayCount_const_append (b : Bool) (N : Nat) (v : List Bool) (K : Nat) :
    rayCount (List.replicate N b++v) K≤1+rayCount v K := by
  let P := fun i : Nat => ∃ k, 1≤k ∧ k≤N ∧ mass (List.replicate k b++v)+(i : Int)=1 ∧
    runKey (List.replicate k b++v)=-2
  let Q := fun i : Nat => Recaman.ThreeNonsuppliedData.localSupply (v++List.replicate i true)=true
  have he : rayCount (List.replicate N b++v) K=cN (fun i => P i ∨ Q i) 0 K := by
    unfold rayCount
    apply cN_congr
    intro i _ _
    exact ray_supply_const_iff b N v i
  have hP : cN P 0 K≤1 := by
    apply cN_le_one_of_unique
    intro i _ j _ hi hj
    obtain ⟨k,hk,hkN,hmk,hkk⟩ := hi
    obtain ⟨l,hl,hlN,hml,hkl⟩ := hj
    have hkl' := constant_run_root_unique b k l v hk hl hkk hkl
    subst l
    omega
  have hu := cN_or_le P Q K
  change rayCount (List.replicate N b++v) K≤1+cN Q 0 K
  omega

def runWord : List (Bool × Nat) → List Bool
  | [] => []
  | (b,N)::rs => List.replicate N b++runWord rs

theorem rayCount_nil (K : Nat) : rayCount [] K=0 := by
  apply cN_zero_of
  intro i _ _ hi
  have hroot := (localSupply_A_S_iff [] i 0).mp (by simpa using hi)
  obtain ⟨t,ht,_,_⟩ := hroot
  simp at ht

/-- Supply during an all-A continuation is paid by a chosen constant-block
partition of the full prefix; no length or free-count upper bound. -/
theorem rayCount_runWord (rs : List (Bool × Nat)) (K : Nat) :
    rayCount (runWord rs) K≤rs.length := by
  induction rs with
  | nil => simp only [runWord,rayCount_nil,List.length_nil]; omega
  | cons r rs ih =>
      obtain ⟨b,N⟩ := r
      have hb := rayCount_const_append b N (runWord rs) K
      simp only [runWord,List.length_cons]
      omega

private theorem cN_shift (P : Nat → Prop) (s K : Nat) :
    cN P s K=cN (fun i => P (s+i)) 0 K := by
  classical
  induction K with
  | zero => rfl
  | succ K ih => simp only [cN,Nat.zero_add,ih]

theorem seg_A (f : Nat → Bool) (s : Nat) :
    ∀ K : Nat, (∀ i, s≤i → i<s+K → f i=true) → seg f s K=List.replicate K true
  | 0,_ => by simp [seg]
  | K+1,h => by
      rw [seg_succ,seg_A f s K (fun i h1 h2 => h i h1 (by omega)),
        h (s+K) (by omega) (by omega),List.replicate_succ']

/-- The computed A-ray count equals actual EndN from the unchanged base0. -/
theorem endable_A_run_count (f : Nat → Bool) (n K : Nat) (w : List Bool)
    (hw : seg f 0 n=w) (hA : ∀ i, i<K → f (n+i)=true) :
    cN (EndN f 0) n K=rayCount w K := by
  rw [cN_shift]
  unfold rayCount
  apply cN_congr
  intro i _ hi
  have hs := seg_add f 0 n i
  simp only [Nat.zero_add,hw] at hs
  have ha : seg f n i=List.replicate i true := by
    apply seg_A
    intro t hnt hti
    simpa only [Nat.add_sub_cancel' hnt] using hA (t-n) (by omega)
  rw [ha] at hs
  have he := localSupply_seg_iff f 0 (n+i) (Nat.zero_le _) (hA i (by omega))
  simp only [Nat.sub_zero,hs] at he
  exact he.symm

theorem count_A_run (f : Nat → Bool) (n K : Nat)
    (hA : ∀ i, i<K → f (n+i)=true) : cN (fun x => f x=true) n K=K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [cN_succ_pos (fun x => f x=true) n K (hA K (by omega)),
        ih (fun i hi => hA i (by omega))]

/-- Consecutive A signs consume free-A budget or at most one supply per
chosen constant block of the full past. Run lengths and K are unbounded. -/
theorem A_run_free_budget (f : Nat → Bool) (n K : Nat) (rs : List (Bool × Nat))
    (hw : seg f 0 n=runWord rs) (hA : ∀ i, i<K → f (n+i)=true) :
    K≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n K+rs.length := by
  have he := endable_A_run_count f n K (runWord rs) hw hA
  have hc := rayCount_runWord rs K
  have hp := addition_endable_partition f n K
  rw [count_A_run f n K hA,he] at hp
  omega

open Classical in
theorem A_run_free_budget_int (e : Int → Bool) (p : Int) (n K : Nat)
    (rs : List (Bool × Nat)) (hw : segment e p n=runWord rs)
    (hA : ∀ i, i<K → e (p+(n : Int)+(i : Int))=true) :
    K≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) K+rs.length := by
  rw [segment_seg e p p 0 (by simp)] at hw
  rw [nonsupplied_count_shift]
  apply A_run_free_budget (fun i => e (p+(i : Int))) n K rs hw
  intro i hi
  simpa only [Int.natCast_add,Int.add_assoc] using hA i hi

end Recaman.RunSupplyBudget
