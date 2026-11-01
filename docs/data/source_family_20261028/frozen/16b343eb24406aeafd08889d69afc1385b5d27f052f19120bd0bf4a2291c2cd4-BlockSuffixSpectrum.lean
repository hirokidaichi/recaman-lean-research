import Recaman.ThreeRunFiniteContext

namespace Recaman.BlockSuffixSpectrum

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Every pair belongs to the same actual prefix; order and duplicates are
irrelevant to membership. R bounds mass, never the history length. -/
def spectrum (R : Nat) (w : List Bool) : List (Int × Int) :=
  ((List.range w.length).map (fun t => (mass (w.drop t),areaW (w.drop t)))).filter
    (fun p => decide (0<p.1 ∧ p.1≤(R : Int)))

def advance (R : Nat) (s : List (Int × Int)) (v : List Bool) : List (Int × Int) :=
  ((s.map (fun p => (p.1+mass v,p.2+(v.length : Int)*p.1+areaW v))).filter
    (fun p => decide (0<p.1 ∧ p.1≤(R : Int))))++spectrum R v

theorem mem_spectrum (R : Nat) (w : List Bool) (r a : Int) :
    (r,a)∈spectrum R w ↔ 0<r ∧ r≤(R : Int) ∧
      ∃ t, t<w.length ∧ mass (w.drop t)=r ∧ areaW (w.drop t)=a := by
  simp only [spectrum,List.mem_filter,decide_eq_true_eq,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨t,ht,hm,ha⟩,hp⟩
    exact ⟨hp.1,hp.2,t,ht,hm,ha⟩
  · rintro ⟨hr,hR,t,ht,hm,ha⟩
    exact ⟨⟨t,ht,hm,ha⟩,hr,hR⟩

/-- Exact all-mass append rule, using the same old prefix on every query.
Positive BlockWord suffixes and nonnegative whole-atom mass justify dropping
old pairs above R, even though an atom may contain internal S signs. -/
theorem spectrum_append (R : Nat) (w v : List Bool) (hw : BlockWord w) (hv : 0≤mass v)
    (r a : Int) :
    (r,a)∈spectrum R (w++v) ↔ (r,a)∈advance R (spectrum R w) v := by
  rw [mem_spectrum]
  simp only [advance,List.mem_append,List.mem_filter,List.mem_map,Prod.mk.injEq,decide_eq_true_eq]
  constructor
  · rintro ⟨hr,hR,t,ht,hm,ha⟩
    by_cases htw : t<w.length
    · left
      have hd : (w++v).drop t=w.drop t++v := by
        rw [List.drop_append,show t-w.length=0 by omega,List.drop_zero]
      rw [hd,mass_append] at hm
      rw [hd,areaW_append] at ha
      have hne : w.drop t≠[] := by
        intro hn
        have hl := List.length_drop (l:=w) (i:=t)
        rw [hn] at hl
        simp only [List.length_nil] at hl
        omega
      have hpositive := (sufPos_block hw (w.take t) (w.drop t) (List.take_append_drop t w) hne).1
      refine ⟨?_,hr,hR⟩
      refine ⟨(mass (w.drop t),areaW (w.drop t)),?_,hm,ha⟩
      exact (mem_spectrum R w _ _).mpr ⟨by omega,by omega,t,htw,rfl,rfl⟩
    · right
      apply (mem_spectrum R v r a).mpr
      have hd : (w++v).drop t=v.drop (t-w.length) := by
        rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append]
      rw [hd] at hm ha
      simp only [List.length_append] at ht
      exact ⟨hr,hR,t-w.length,by omega,hm,ha⟩
  · rintro (⟨⟨⟨u,b⟩,hs,hm,ha⟩,hr,hR⟩|hs)
    · obtain ⟨_,_,t,ht,hmt,hat⟩ := (mem_spectrum R w u b).mp hs
      have hd : (w++v).drop t=w.drop t++v := by
        rw [List.drop_append,show t-w.length=0 by omega,List.drop_zero]
      refine ⟨hr,hR,t,by simp only [List.length_append]; omega,?_,?_⟩
      · rw [hd,mass_append,hmt]
        exact hm
      · rw [hd,areaW_append,hmt,hat]
        exact ha
    · obtain ⟨hr,hR,t,ht,hm,ha⟩ := (mem_spectrum R v r a).mp hs
      have hd : (w++v).drop (w.length+t)=v.drop t := by
        rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,Nat.add_sub_cancel_left]
      refine ⟨hr,hR,w.length+t,by simp only [List.length_append]; omega,?_,?_⟩
      · rw [hd]; exact hm
      · rw [hd]; exact ha

/-- A representation preserving every old pair preserves the exact append
rule, rather than choosing an unrelated representative for each query. -/
theorem advance_membership_congr (R : Nat) (s t : List (Int × Int)) (v : List Bool)
    (h : ∀ p, p∈s ↔ p∈t) (p : Int × Int) :
    p∈advance R s v ↔ p∈advance R t v := by
  simp only [advance,List.mem_append,List.mem_filter,List.mem_map]
  simp only [h]

/-- Both lists describe the same finite set, preserving duplicate-insensitive
membership while letting the certificate choose a canonical ordering. -/
def samePairs (s t : List (Int × Int)) : Bool :=
  s.all (fun p => decide (p∈t)) && t.all (fun p => decide (p∈s))

theorem samePairs_sound (s t : List (Int × Int)) (h : samePairs s t=true) (p : Int × Int) :
    p∈s ↔ p∈t := by
  obtain ⟨hs,ht⟩ := Bool.and_eq_true_iff.mp h
  constructor
  · intro hp
    exact of_decide_eq_true (List.all_eq_true.mp hs p hp)
  · intro hp
    exact of_decide_eq_true (List.all_eq_true.mp ht p hp)

abbrev Row := List (Int × Int) × Nat × Nat × Nat
structure Table where
  size : Nat
  get : Nat → Row

def checkChild (R : Nat) (rs : Table) (s : List (Int × Int)) (v : List Bool) (j : Nat) : Bool :=
  decide (j<rs.size) && samePairs (advance R s v) (rs.get j).1

def checkOne (R : Nat) (rs : Table) (i : Nat) : Bool :=
  checkChild R rs (rs.get i).1 [true] (rs.get i).2.1 &&
  checkChild R rs (rs.get i).1 aasW (rs.get i).2.2.1 &&
  checkChild R rs (rs.get i).1 tripW (rs.get i).2.2.2

def verifiedRange (R : Nat) (rs : Table) (lo count : Nat) : Bool :=
  (List.range count).all (fun i => checkOne R rs (lo+i))

def verified (R : Nat) (rs : Table) : Bool := verifiedRange R rs 0 rs.size

theorem verifiedRange_at (R : Nat) (rs : Table) (lo count : Nat)
    (h : verifiedRange R rs lo count=true) (i : Nat) (hlo : lo≤i) (hi : i<lo+count) :
    checkOne R rs i=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_cancel' hlo] using ha

private theorem checkChild_sound (R : Nat) (rs : Table) (s : List (Int × Int)) (v : List Bool) (j : Nat)
    (h : checkChild R rs s v j=true) :
    j<rs.size ∧ ∀ p, p∈advance R s v ↔ p∈(rs.get j).1 := by
  obtain ⟨hj,hp⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true hj,fun p => samePairs_sound _ _ hp p⟩

private theorem transition (R : Nat) (rs : Table) (w v : List Bool) (hw : BlockWord w)
    (hv : 0≤mass v) (i j : Nat) (hi : i<rs.size)
    (hmatch : ∀ p, p∈spectrum R w ↔ p∈(rs.get i).1)
    (hcheck : checkChild R rs (rs.get i).1 v j=true) :
    j<rs.size ∧ ∀ p, p∈spectrum R (w++v) ↔ p∈(rs.get j).1 := by
  obtain ⟨hj,hstep⟩ := checkChild_sound R rs _ v j hcheck
  refine ⟨hj,?_⟩
  rintro ⟨r,a⟩
  exact (spectrum_append R w v hw hv r a).trans
    ((advance_membership_congr R _ _ v hmatch (r,a)).trans (hstep (r,a)))

/-- A checked finite table yields an actual all-length BlockWord
classification, with the same row matching every suffix query at once. -/
theorem block_spectrum_table (R : Nat) (rs : Table)
    (hverified : verified R rs=true) (h0 : 0<rs.size)
    (hempty : samePairs (spectrum R []) (rs.get 0).1=true)
    {w : List Bool} (hw : BlockWord w) :
    ∃ i, i<rs.size ∧ ∀ (r a : Int),
      ((0<r ∧ r≤(R : Int) ∧ ∃ t, t<w.length ∧ mass (w.drop t)=r ∧ areaW (w.drop t)=a) ↔
        (r,a)∈(rs.get i).1) := by
  have hrows : ∀ i, i<rs.size → checkOne R rs i=true := by
    intro i hi
    exact verifiedRange_at R rs 0 rs.size hverified i (Nat.zero_le _) (by omega)
  have hm : ∃ i, i<rs.size ∧ ∀ p, p∈spectrum R w ↔ p∈(rs.get i).1 := by
    induction hw with
    | nil => exact ⟨0,h0,fun p => samePairs_sound _ _ hempty p⟩
    | free hw ih =>
      obtain ⟨i,hi,hmatch⟩ := ih
      have hc := hrows i hi
      have hchild := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
      exact ⟨(rs.get i).2.1,transition R rs _ [true] hw (by decide) i _ hi hmatch hchild⟩
    | aas hw ih =>
      obtain ⟨i,hi,hmatch⟩ := ih
      have hc := hrows i hi
      have hchild := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
      exact ⟨(rs.get i).2.2.1,transition R rs _ aasW hw (by decide) i _ hi hmatch hchild⟩
    | triple hw ih =>
      obtain ⟨i,hi,hmatch⟩ := ih
      have hc := hrows i hi
      have hchild := (Bool.and_eq_true_iff.mp hc).2
      exact ⟨(rs.get i).2.2.2,transition R rs _ tripW hw (by decide) i _ hi hmatch hchild⟩
  obtain ⟨i,hi,hmatch⟩ := hm
  exact ⟨i,hi,fun r a => (mem_spectrum R w r a).symm.trans (hmatch (r,a))⟩

/-- Pure-word interface of the existing old-window count obstruction.
It retains the actual old suffix, rather than an independent old tag. -/
theorem old_suffix_mass_bound (u v : List Bool) (hu : BlockWord u) (hne : u≠[])
    (hm : mass u+mass v=1) (ha : areaW (u++v)=0) : mass u≤ones v-1 := by
  obtain ⟨hr,harea⟩ := sufPos_block hu [] u rfl hne
  have hlow := block_area_quadratic_lower hu
  have hv := areaW_count_lower v
  have hmV := mass_eq v
  have hA := ones_bounds v
  rw [areaW_append] at ha
  have hineq : 0≤(ones v-1)^2-(mass u)^2 := by
    have harith (r A V U L : Int) (hm : r+(2*A-L)=1)
        (hz : U+L*r+V=0) (hl : r*(r+1)≤2*U+2)
        (hv : A*(A+1)-(L-A)*(L-A+1)-2*A*(L-A)≤2*V) :
        0≤(A-1)^2-r^2 := by
      have hL : L=r+2*A-1 := by omega
      have hid : 2*((A-1)^2-r^2)=
          (2*U+2-r*(r+1))+
          (2*V-(A*(A+1)-(L-A)*(L-A+1)-2*A*(L-A))) := by
        rw [hL] at hz ⊢
        grind
      omega
    exact harith (mass u) (ones v) (areaW v) (areaW u) v.length (by omega) ha hlow hv
  have hposA : 1≤ones v := by
    by_cases h0 : ones v=0
    · have hp := Int.mul_nonneg (show 0≤mass u by omega) (show 0≤mass u-1 by omega)
      have harith (r V U L : Int) (hm : r-L=1) (hz : U+L*r+V=0)
          (hv : -L*(L+1)≤2*V) : 2*U≤-r*(r-1) := by grind
      have hc := harith (mass u) (areaW v) (areaW u) v.length (by omega) ha
        (by rw [h0] at hv; simp only [Int.zero_add,Int.zero_mul,Int.mul_zero,Int.sub_zero,Int.zero_sub] at hv; simpa only [Int.neg_mul] using hv)
      have heq : -mass u*(mass u-1)=-(mass u*(mass u-1)) := by grind
      rw [heq] at hc
      omega
    · omega
  by_cases hbound : mass u≤ones v-1
  · exact hbound
  · have hp := Int.mul_pos (show 0<mass u-(ones v-1) by omega)
        (show 0<mass u+(ones v-1) by omega)
    have hid : (mass u-(ones v-1))*(mass u+(ones v-1))=(mass u)^2-(ones v-1)^2 := by grind
    rw [hid] at hp
    omega

/-- The same bounded old spectrum answers every arbitrary future query.
The budget is explicit; no source or endpoint tag is made independent. -/
theorem localSupply_budget_spectrum_iff (w v : List Bool) (hw : BlockWord w)
    (B : Nat) (hB : 1≤B) (hv : ones v≤(B : Int)) :
    Recaman.ThreeNonsuppliedData.localSupply (w++v)=true ↔
      Recaman.ThreeNonsuppliedData.localSupply v=true ∨
      ∃ (r a : Int), (r,a)∈spectrum (B-1) w ∧ r+mass v=1 ∧
        a+(v.length : Int)*r+areaW v=0 := by
  rw [localSupply_iff]
  constructor
  · rintro ⟨t,ht,hm,ha⟩
    by_cases htw : t<w.length
    · right
      have hd : (w++v).drop t=w.drop t++v := by
        rw [List.drop_append,show t-w.length=0 by omega,List.drop_zero]
      have hne : w.drop t≠[] := by
        intro hn
        have hl := List.length_drop (l:=w) (i:=t)
        rw [hn] at hl
        simp only [List.length_nil] at hl
        omega
      have hu := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
      rw [hd,mass_append] at hm
      rw [hd,checked_wordArea_eq] at ha
      have hb := old_suffix_mass_bound (w.drop t) v hu hne hm ha
      have hp := (sufPos_block hu [] (w.drop t) rfl hne).1
      refine ⟨mass (w.drop t),areaW (w.drop t),?_,hm,?_⟩
      · apply (mem_spectrum (B-1) w _ _).mpr
        exact ⟨by omega,by omega,t,htw,rfl,rfl⟩
      · simpa only [areaW_append] using ha
    · left
      apply (localSupply_iff v).mpr
      have hd : (w++v).drop t=v.drop (t-w.length) := by
        rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append]
      simp only [List.length_append] at ht
      rw [hd] at hm ha
      exact ⟨t-w.length,by omega,hm,ha⟩
  · rintro (hl|⟨r,a,hs,hm,ha⟩)
    · obtain ⟨t,ht,hm,ha⟩ := (localSupply_iff v).mp hl
      have hd : (w++v).drop (w.length+t)=v.drop t := by
        rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,Nat.add_sub_cancel_left]
      exact ⟨w.length+t,by simp only [List.length_append]; omega,by rw [hd]; exact hm,by rw [hd]; exact ha⟩
    · obtain ⟨_,_,t,ht,hmt,hat⟩ := (mem_spectrum (B-1) w r a).mp hs
      have hd : (w++v).drop t=w.drop t++v := by
        rw [List.drop_append,show t-w.length=0 by omega,List.drop_zero]
      refine ⟨t,by simp only [List.length_append]; omega,?_,?_⟩
      · rw [hd,mass_append,hmt]; exact hm
      · rw [hd,checked_wordArea_eq,areaW_append,hmt,hat]; exact ha

/-- Equality of one joint old spectrum suffices for all bounded-A futures;
no finite history length or free-Endable tag is assumed. -/
theorem localSupply_same_spectrum (w z v : List Bool) (hw : BlockWord w) (hz : BlockWord z)
    (B : Nat) (hB : 1≤B) (hv : ones v≤(B : Int))
    (hs : ∀ (r a : Int), (r,a)∈spectrum (B-1) w ↔ (r,a)∈spectrum (B-1) z) :
    Recaman.ThreeNonsuppliedData.localSupply (w++v)=true ↔
      Recaman.ThreeNonsuppliedData.localSupply (z++v)=true := by
  rw [localSupply_budget_spectrum_iff w v hw B hB hv,
    localSupply_budget_spectrum_iff z v hz B hB hv]
  simp only [hs]

/-- Literal actual histories with the same joint spectrum and the same
bounded-A future have the same EndN result, including the endpoint sign. -/
theorem endable_same_spectrum (f g : Nat → Bool) (n N B : Nat) (w z v : List Bool)
    (hw : BlockWord w) (hz : BlockWord z) (hfpre : seg f 0 n=w) (hgpre : seg g 0 N=z)
    (hfv : seg f n v.length=v) (hgv : seg g N v.length=v)
    (hB : 1≤B) (hv : ones v≤(B : Int))
    (hs : ∀ (r a : Int), (r,a)∈spectrum (B-1) w ↔ (r,a)∈spectrum (B-1) z)
    (hA : f (n+v.length)=g (N+v.length)) :
    EndN f 0 (n+v.length) ↔ EndN g 0 (N+v.length) := by
  have hfword : seg f 0 (n+v.length)=w++v := by rw [seg_add,Nat.zero_add,hfpre,hfv]
  have hgword : seg g 0 (N+v.length)=z++v := by rw [seg_add,Nat.zero_add,hgpre,hgv]
  by_cases hp : f (n+v.length)=true
  · have hgp : g (N+v.length)=true := by rw [←hA]; exact hp
    have hf := localSupply_seg_iff f 0 (n+v.length) (Nat.zero_le _) hp
    have hg := localSupply_seg_iff g 0 (N+v.length) (Nat.zero_le _) hgp
    rw [Nat.sub_zero,hfword] at hf
    rw [Nat.sub_zero,hgword] at hg
    exact hf.symm.trans ((localSupply_same_spectrum w z v hw hz B hB hv hs).trans hg)
  · constructor
    · intro he; exact False.elim (hp he.1)
    · intro he; exact False.elim (hp (hA.trans he.1))

private theorem ones_take_bound (x : List Bool) (k : Nat) : ones (x.take k)≤ones x := by
  have h := ones_append (x.take k) (x.drop k)
  rw [List.take_append_drop] at h
  have hd := ones_bounds (x.drop k)
  omega

/-- One fixed pair of prefixes preserves all future supply and free counts.
Every tag is the actual EndN of that prefix, not a freely chosen label. -/
theorem spectrum_future_counts (f g : Nat → Bool) (n N B : Nat) (w z v : List Bool)
    (hw : BlockWord w) (hz : BlockWord z) (hfpre : seg f 0 n=w) (hgpre : seg g 0 N=z)
    (hfv : seg f n v.length=v) (hgv : seg g N v.length=v)
    (hB : 1≤B) (hv : ones v≤(B : Int))
    (hs : ∀ (r a : Int), (r,a)∈spectrum (B-1) w ↔ (r,a)∈spectrum (B-1) z)
    (hA : f (n+v.length)=g (N+v.length)) (k : Nat) (hk : k≤v.length) :
    cN (EndN f 0) n k=cN (EndN g 0) N k ∧
    cN (fun i => f i=true ∧ ¬EndN f 0 i) n k=
      cN (fun i => g i=true ∧ ¬EndN g 0 i) N k := by
  have hsign : ∀ i, i≤v.length → f (n+i)=g (N+i) := by
    intro i hi
    by_cases hil : i<v.length
    · have hf := seg_get f n v.length i hil
      have hg := seg_get g N v.length i hil
      rw [hfv] at hf
      rw [hgv] at hg
      exact Option.some.inj (hf.symm.trans hg)
    · have heq : i=v.length := by omega
      simpa only [heq] using hA
  have heq : ∀ i, i≤v.length → (EndN f 0 (n+i) ↔ EndN g 0 (N+i)) := by
    intro i hi
    have hft := seg_take f n v.length i hi
    have hgt := seg_take g N v.length i hi
    rw [hfv] at hft
    rw [hgv] at hgt
    have hlen : (v.take i).length=i := by simp only [List.length_take,Nat.min_eq_left hi]
    have ho := ones_take_bound v i
    have hh := endable_same_spectrum f g n N B w z (v.take i) hw hz hfpre hgpre
      (by simpa only [hlen] using hft.symm) (by simpa only [hlen] using hgt.symm) hB
      (by omega) hs (by simpa only [hlen] using hsign i hi)
    simpa only [hlen] using hh
  have hshiftf := Recaman.SeparatorTailFreeGap.count_nat_shift (EndN f 0) n 0 k
  have hshiftg := Recaman.SeparatorTailFreeGap.count_nat_shift (EndN g 0) N 0 k
  have hfreef := Recaman.SeparatorTailFreeGap.count_nat_shift (fun i => f i=true ∧ ¬EndN f 0 i) n 0 k
  have hfreeg := Recaman.SeparatorTailFreeGap.count_nat_shift (fun i => g i=true ∧ ¬EndN g 0 i) N 0 k
  simp only [Nat.add_zero] at hshiftf hshiftg hfreef hfreeg
  constructor
  · rw [←hshiftf,←hshiftg]
    apply cN_congr
    intro i _ hik
    exact heq i (by omega)
  · rw [←hfreef,←hfreeg]
    apply cN_congr
    intro i _ hik
    rw [hsign i (by omega)]
    exact and_congr_right (fun _ => not_congr (heq i (by omega)))

end Recaman.BlockSuffixSpectrum
