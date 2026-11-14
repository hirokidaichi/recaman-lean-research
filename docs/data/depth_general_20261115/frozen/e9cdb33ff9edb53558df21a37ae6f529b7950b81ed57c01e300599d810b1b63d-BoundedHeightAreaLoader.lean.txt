import Recaman.SuffixSourceCompletion

namespace Recaman.BoundedHeightAreaLoader

open Recaman.SuffixSourceCompletion Recaman.LeadingRunSupply Recaman.ShortPeriodicSupply
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality

theorem area_loop_length (b : Bool) : ∀ n, (areaLoop b n).length=2*n
  | 0 => rfl
  | n+1 => by simp only [areaLoop,List.length_append,List.length_cons,List.length_nil,
      area_loop_length]; omega

private theorem SA_prefix (n : Nat) : ∀ k, k≤2*n →
    mass ((areaLoop false n).take k)= -((k%2 : Nat) : Int) ∧
    areaW ((areaLoop false n).take k)= -(((k+1)/2 : Nat) : Int) := by
  induction n with
  | zero =>
    intro k hk
    have he : k=0 := by omega
    subst k
    decide
  | succ n ih =>
    intro k hk
    rcases k with _ | k
    · simp [areaW]
    rcases k with _ | k
    · simp [areaLoop,areaW,mass,sign]
    have hi := ih k (by omega)
    have ht : (areaLoop false (n+1)).take (k+1+1)=
        [false,true]++(areaLoop false n).take k := by
      change (false::true::areaLoop false n).take (k+1+1)=_
      rw [show k+1+1=Nat.succ (Nat.succ k) by omega]
      rfl
    rw [ht,mass_append,areaW_append,show mass [false,true]=0 by decide,
      show areaW [false,true]= -1 by decide,hi.1,hi.2]
    constructor <;> omega

def loader (D : Nat) : List Bool :=
  ([false,true,true,true,false]++areaLoop false (D+3))++List.replicate 4 false

theorem loader_data (D : Nat) :
    mass (loader D)= -3 ∧ areaW (loader D)=(D : Int) ∧ (loader D).length=2*D+15 := by
  have h := area_loop_data false (D+3)
  have hl := area_loop_length false (D+3)
  simp only [Bool.false_eq_true,ite_false] at h
  have hm : mass [false,true,true,true,false]=1 := by decide
  have ha : areaW [false,true,true,true,false]=3 := by decide
  have hmt : mass (List.replicate 4 false)= -4 := by decide
  have hat : areaW (List.replicate 4 false)= -10 := by decide
  simp only [loader,mass_append,areaW_append,hm,ha,hmt,hat,h.1,h.2,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil,hl,
    Int.natCast_add,Int.natCast_mul]
  constructor
  · omega
  · constructor <;> omega

/-- Every prefix stays within five levels. A return to height zero with
zero area is possible only at the origin, independently of stored D. -/
theorem loader_prefix_control (D k : Nat) (hk : k≤(loader D).length) :
    (-3≤mass ((loader D).take k) ∧ mass ((loader D).take k)≤2) ∧
    (mass ((loader D).take k)=0 → areaW ((loader D).take k)=0 → k=0) := by
  let H : List Bool := [false,true,true,true,false]
  let L := areaLoop false (D+3)
  have hH : H.length=5 := rfl
  have hL : L.length=2*(D+3) := area_loop_length false (D+3)
  have hMH : mass H=1 := by decide
  have hAH : areaW H=3 := by decide
  have hML : mass L=0 := (area_loop_data false (D+3)).1
  have hAL : areaW L= -((D+3 : Nat) : Int) := (area_loop_data false (D+3)).2
  by_cases hfirst : k≤5
  · have ht : (loader D).take k=H.take k := by
      change ((H++L)++List.replicate 4 false).take k=_
      rw [List.take_append_of_le_length (by simp only [List.length_append,hH]; omega),
        List.take_append_of_le_length (by omega)]
    rw [ht]
    have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · by_cases hmiddle : k≤5+L.length
    · let j := k-5
      have hj : j≤2*(D+3) := by dsimp [j]; omega
      have ht : (loader D).take k=H++L.take j := by
        change ((H++L)++List.replicate 4 false).take k=_
        rw [List.take_append_of_le_length (by simp only [List.length_append,hH]; omega),
          show k=H.length+j by dsimp [j]; omega,List.take_length_add_append]
      have hd := SA_prefix (D+3) j hj
      have htake : (L.take j).length=j := by rw [List.length_take,Nat.min_eq_left (by omega)]
      change mass (L.take j)=_ ∧ areaW (L.take j)=_ at hd
      rw [ht,mass_append,areaW_append,hMH,hAH,hd.1,hd.2,htake]
      have hmod : j%2<2 := Nat.mod_lt _ (by omega)
      constructor
      · constructor <;> omega
      · intro _ hzero; omega
    · let j := k-(5+L.length)
      have hj : j≤4 := by have hh := (loader_data D).2.2; dsimp [j]; omega
      have ht : (loader D).take k=(H++L)++(List.replicate 4 false).take j := by
        change ((H++L)++List.replicate 4 false).take k=_
        rw [show k=(H++L).length+j by simp only [List.length_append,hH]; dsimp [j]; omega,
          List.take_length_add_append]
      rw [ht]
      have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
      rcases hc with hj0|hj0|hj0|hj0|hj0
      all_goals rw [hj0]
      all_goals simp only [mass_append,areaW_append,hMH,hAH,hML,hAL,hL,
        List.take_replicate,List.length_replicate]
      all_goals simp [mass,areaW,sign]
      all_goals omega

/-- Every original realization has the same bounded-height, no-return
property. This is the area-loader support, not the all-N plateau. -/
theorem original_loader_control (f : Nat → Bool) (s D k : Nat)
    (hseg : seg f s (loader D).length=loader D) (hk : k≤(loader D).length) :
    (-3≤Fw f (s+k)-Fw f s ∧ Fw f (s+k)-Fw f s≤2) ∧
    (Fw f (s+k)=Fw f s → Ar f s k=0 → k=0) := by
  have ht := seg_take f s (loader D).length k hk
  rw [hseg] at ht
  have hm := seg_mass f s k
  have ha := Ar_areaW f s k
  rw [←ht] at hm ha
  have hc := loader_prefix_control D k hk
  exact ⟨by omega,fun hF hA => hc.2 (by omega) (by omega)⟩

end Recaman.BoundedHeightAreaLoader
