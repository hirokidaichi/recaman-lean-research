import Recaman.FourRunSupplyBudget

namespace Recaman.FourRunTargetArea

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.ASourceReuse Recaman.RunClockClassifier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

theorem runKey_seven_runs (h M m L s U v : Nat) :
    runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)=
    4*((M : Int)*((m : Int)+(s : Int)+(v : Int))+(L : Int)*((s : Int)+(v : Int))+
      (U : Int)*(v : Int))-2*((h : Int)+(m : Int)+(s : Int)+(v : Int))^2 := by
  rw [runKey_append_S,runKey_append_A,runKey_five_runs]
  simp only [mass_append,mass_rep_false,mass_replicate_A]
  grind

/-- The same old suffix retains its mass and area in the four-run
identity. No mass cap or independent old signatures are used. -/
theorem old_target_area_identity (u : List Bool) (h M m L s U v T j : Nat)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    2*areaW u+mass u*(mass u-1)=
      2*((M : Int)+(L : Int)+(U : Int)+(T : Int))*
        ((M : Int)+(L : Int)+(U : Int)+(T : Int)-2*((j : Int)+1))-
      4*((M : Int)*((m : Int)+(s : Int)+(v : Int))+
        (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)) := by
  let b := List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hk := source_key_before_gap (u++b) T j
    (by simpa only [b,List.append_assoc] using hmass)
    (by simpa only [b,List.append_assoc] using harea)
  have hb := runKey_seven_runs h M m L s U v
  have hc : (cntF b : Int)=(h : Int)+(m : Int)+(s : Int)+(v : Int) := by
    simp only [b,cntF_append,cntF_replicate_S,cntF_A,Nat.add_zero,Int.natCast_add]
  rw [runKey_append,hc] at hk
  change runKey b=_ at hb
  rw [hb] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmass
  unfold runKey at hk
  grind

/-- A short last ray (forced by a final-S local clock in the final band)
requires two more A signs than twice R=j+1. This strengthens the source
A cut but does not itself prove an actual free-count bound. -/
theorem old_target_short_last_A_budget (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s U v T j : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hshort : T≤j+2)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    2*(j+1)+2≤M+L+U+T := by
  let A : Int := (M : Int)+(L : Int)+(U : Int)+(T : Int)
  let H : Int := (M : Int)+(L : Int)+(U : Int)
  let R : Int := (j : Int)+1
  let I : Int := (M : Int)*((m : Int)+(s : Int)+(v : Int))+
    (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)
  have he := old_target_area_identity u h M m L s U v T j hmass harea
  have hl := block_area_quadratic_lower hu
  have hC : 1≤mass u := (sufPos_block hu [] u rfl hne).1
  have hb : (mass u)^2+2*I≤A*(A-2*R)+1 := by dsimp [I,A,R]; grind
  have hmprod := Int.mul_nonneg (show 0≤(M : Int) by omega)
    (show 0≤(m : Int)+(s : Int)+(v : Int)-3 by omega)
  have hlprod := Int.mul_nonneg (show 0≤(L : Int) by omega)
    (show 0≤(s : Int)+(v : Int)-2 by omega)
  have huprod := Int.mul_nonneg (show 0≤(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hI : H+3≤I := by dsimp [H,I]; grind
  have hC2 := Int.mul_nonneg (show 0≤mass u-1 by omega) (show 0≤mass u+1 by omega)
  have hA : 0≤A := by dsimp [A]; omega
  have hlarge : 2*R<A := by
    by_cases hh : 2*R<A
    · exact hh
    · have hp := Int.mul_nonpos_of_nonneg_of_nonpos hA (show A-2*R≤0 by omega)
      grind
  by_cases hh : 2*R+2≤A
  · dsimp [A,R] at hh; omega
  · have hAe : A=2*R+1 := by omega
    have hH : R≤H := by dsimp [A,H,R] at *; omega
    rw [hAe] at hb
    grind

/-- A P2 source lying in the immediately preceding S run is clock2. -/
theorem final_S_source_clock (q i : Nat)
    (hm : mass (List.replicate q false++List.replicate i true)=1)
    (ha : areaW (List.replicate q false++List.replicate i true)=0) : q=1 ∧ i=2 := by
  have hk := source_key_before_gap (List.replicate q false) i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm)
    (by simpa only [List.replicate_zero,List.append_nil] using ha)
  rw [runKey_S] at hk
  have hq : q=1 := by
    by_cases h : q=0
    · rw [h] at hk; simp at hk
    · by_cases h1 : q=1
      · exact h1
      · have hp := Int.mul_nonneg (show 0≤(q : Int)-2 by omega) (show 0≤(q : Int)+2 by omega)
        grind
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  exact ⟨hq,by omega⟩

/-- Sharp raw P2 control for the +2 budget, not a free-gap counterexample. -/
theorem short_last_raw_boundary :
    mass ([true,true]++List.replicate 5 false++[true,false,true,false]++
      List.replicate 3 true++[false]++List.replicate 5 true++List.replicate 3 false)=1 ∧
    areaW ([true,true]++List.replicate 5 false++[true,false,true,false]++
      List.replicate 3 true++[false]++List.replicate 5 true++List.replicate 3 false)=0 ∧
    (1+1+3+5 : Nat)=2*(3+1)+2 := by decide

/-- Raw four-run necessary condition lifted to the SAME actual old
source/window. The whole old prefix is retained. -/
theorem actual_short_last_A_budget (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hshort : T≤j+2)
    (hword : seg f n (h+M+m+L+s+U+v+T)=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (hwin : Win f t (n+h+M+m+L+s+U+v+T+j-t)) :
    2*(j+1)+2≤cN (fun x=>f x=true) n (h+M+m+L+s+U+v+T) := by
  let B:=h+M+m+L+s+U+v+T
  let u:=w.drop t
  have hn : w.length=n := by rw [←hpre,seg_length]
  have hu : BlockWord u := block_suffix hw (w.take t) u (List.take_append_drop t w).symm
  have hne : u≠[] := by
    intro hh
    have hlen := List.length_drop t w
    change (w.drop t)=[] at hh
    rw [hh,hn] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hd := seg_drop f 0 n t (by omega)
  simp only [Nat.zero_add,hpre] at hd
  have hfull : seg f t (n+B+j-t)=u++List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false := by
    rw [show n+B+j-t=(n-t)+(B+j) by omega,seg_add,show t+(n-t)=n by omega,←hd,
      seg_add,show n+B=n+h+M+m+L+s+U+v+T by omega,
      seg_false f (n+h+M+m+L+s+U+v+T) j hgap,hword]
    simp only [u,List.append_assoc]
  have hmwin : mass (u++List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=1 := by
    rw [←hfull,seg_mass]
    have h:=hwin.2.1
    rw [show t+(n+B+j-t)=n+B+j by omega]
    exact h
  have hawin : areaW (u++List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=0 := by
    rw [←hfull,←Ar_areaW]
    exact hwin.2.2
  have hb := old_target_short_last_A_budget u hu hne h M m L s U v T j hM hm hL hs hU hv hshort hmwin hawin
  have ha:=ones_seg_eq_count f n B
  change ones (seg f n (h+M+m+L+s+U+v+T))=_ at ha
  rw [hword] at ha
  simp only [ones_append,ones_replicate_A,ones_replicate_S] at ha
  omega

/-- The local source is in the final separator. Its actual window fixes
q=1/i=2 and hence supplies the short-last-ray premise, rather than taking
that necessary condition or the desired A/free bound as a hypothesis. -/
theorem actual_final_S_source_A_budget (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hword : seg f n (h+M+m+L+s+U+v+T)=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i)) :
    q=1 ∧ i=2 ∧ 2*(j+1)+2≤cN (fun x=>f x=true) n (h+M+m+L+s+U+v+T) := by
  let D:=n+h+M+m+L+s+U+v
  have hseg : seg f (D-q) (q+i)=List.replicate q false++List.replicate i true := by
    rw [seg_add,show D-q+q=D by dsimp [D]; omega]
    have hS : seg f (D-q) q=List.replicate q false := by
      apply seg_false
      intro x hx hxq
      exact hS4 x (by dsimp [D] at *; omega) (by dsimp [D] at *; omega)
    have hA : seg f D i=List.replicate i true := by
      apply seg_A
      intro x hx hxi
      simpa only [Nat.add_sub_cancel' hx] using hA4 (x-D) (by omega)
    rw [hS,hA]
  have hmass : mass (List.replicate q false++List.replicate i true)=1 := by
    rw [←hseg,seg_mass]
    have hm:=hlocal.2.1
    rw [show D-q+(q+i)=D+i by dsimp [D]; omega]
    exact hm
  have harea : areaW (List.replicate q false++List.replicate i true)=0 := by
    rw [←hseg,←Ar_areaW]
    exact hlocal.2.2
  obtain ⟨hq1,hi2⟩:=final_S_source_clock q i hmass harea
  refine ⟨hq1,hi2,?_⟩
  exact actual_short_last_A_budget f n t h M m L s U v T j w hw hpre ht
    hM hm hL hs hU hv (by omega) hword hgap htarget

end Recaman.FourRunTargetArea
