import Recaman.LocalSourcePrefixBudget

namespace Recaman.SourceCrossSurplus

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- The cross term counts A-before-S pairs, with weight4. -/
theorem cross_append (u v : List Bool) :
    runKey (u++v)+2*(cntF (u++v) : Int)^2=
      runKey u+2*(cntF u : Int)^2+runKey v+2*(cntF v : Int)^2+
        4*ones u*(cntF v : Int) := by
  have hm := mass_eq u
  have hc := cntF_int u
  rw [runKey_append,cntF_append]
  simp only [Int.natCast_add]
  grind

/-- An actual AS pair, in arbitrary surrounding signs, supplies positive
cross surplus. It is not a free-count or rank assumption. -/
theorem cross_of_AS (u v : List Bool) :
    4≤runKey (u++[true,false]++v)+2*(cntF (u++[true,false]++v) : Int)^2 := by
  have hu := runKey_count_lower u
  have hv := runKey_count_lower v
  have h1:=cross_append u [true,false]
  have h2:=cross_append (u++[true,false]) v
  have ha:=ones_bounds u
  have hb:=ones_bounds (u++[true,false])
  have hp:=Int.mul_nonneg ha.1 (show 0≤(cntF [true,false] : Int) by omega)
  have hq:=Int.mul_nonneg hb.1 (show 0≤(cntF v : Int) by omega)
  have he : runKey [true,false]+2*(cntF [true,false] : Int)^2=4 := by decide
  grind

/-- Exact relation for the same old and local source windows. Keeping
cross surplus retains the source delay K=i+j-T rather than discarding it. -/
theorem two_source_cross_identity (u b v : List Bool) (i T j : Nat)
    (hm1 : mass (v++List.replicate i true)=1)
    (ha1 : areaW (v++List.replicate i true)=0)
    (hm2 : mass (u++b++v++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++b++v++List.replicate T true++List.replicate j false)=0) :
    2*(ones b-((i : Int)+(j : Int)-(T : Int)))^2=
      2*((j : Int)+1)^2+runKey u+2*(mass u)^2+
      (runKey b+2*(cntF b : Int)^2)+
      4*((i : Int)+(j : Int)-(T : Int))*(cntF v : Int)-2 := by
  have hk1 := source_key_before_gap v i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [List.replicate_zero,List.append_nil] using ha1)
  have hk2 := source_key_before_gap (u++b++v) T j hm2 ha2
  have hmb:=mass_eq b
  have hcb:=cntF_int b
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hm1 hm2
  rw [runKey_append,runKey_append,mass_append,hk1] at hk2
  grind

/-- A positive cross term gives a strict, delay-sensitive source A cut.
The old suffix is nonempty BlockWord; free counts are not substituted. -/
theorem source_prefix_A_strict (u b v : List Bool) (hu : BlockWord u) (hne : u≠[])
    (i T j : Nat) (hj : 2≤j) (hband : T≤i+j)
    (hcross : 4≤runKey b+2*(cntF b : Int)^2)
    (hm1 : mass (v++List.replicate i true)=1)
    (ha1 : areaW (v++List.replicate i true)=0)
    (hm2 : mass (u++b++v++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++b++v++List.replicate T true++List.replicate j false)=0) :
    (j : Int)+1+((i : Int)+(j : Int)-(T : Int))+1≤ones b := by
  let C:=mass u
  let K:=(i : Int)+(j : Int)-(T : Int)
  let X:=ones b-K
  let R:=(j : Int)+1
  have he:=two_source_cross_identity u b v i T j hm1 ha1 hm2 ha2
  have hC : 1≤C := (sufPos_block hu [] u rfl hne).1
  have hku : -2≤runKey u := by have hh:=block_area_quadratic_lower hu; unfold runKey; omega
  have hK : 0≤K := by dsimp [K]; omega
  have hcv : 0≤(cntF v : Int) := by omega
  have hprod:=Int.mul_nonneg hK hcv
  have hm : 0≤C+X := by
    have hcb:=cntF_int b
    have hmb:=mass_eq b
    simp only [mass_append,mass_replicate_A,mass_rep_false] at hm1 hm2
    dsimp [C,X,K]
    omega
  have hineq : C^2+R^2≤X^2 := by dsimp [C,R,X,K]; grind
  have hR : 3≤R := by dsimp [R]; omega
  have hX : 0≤X := by
    by_cases hh : 0≤X
    · exact hh
    · have hp:=Int.mul_nonneg hm (show 0≤C-X by omega)
      have hs : X^2≤C^2 := by grind
      grind
  have hC2 : 1≤C^2 := by have hp:=Int.mul_nonneg (show 0≤C-1 by omega) (show 0≤C+1 by omega); grind
  have hgt : R<X := by
    by_cases hh : R<X
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤R-X by omega) (show 0≤R+X by omega)
      grind
  dsimp [R,X,K] at hgt
  omega

/-- The strict cut in the original actual windows. An AS pair before
source z is supplied by its literal segment, not by the desired cut. -/
theorem actual_source_prefix_A_strict (f : Nat → Bool) (n s z B i T j : Nat)
    (hw : BlockWord (seg f 0 n)) (b0 b1 : List Bool)
    (hAS : seg f n (z-n)=b0++[true,false]++b1) (hs : s<n) (hz : n≤z) (hzB : z≤n+B)
    (hi : i<T) (hj : 2≤j) (hband : T≤i+j)
    (hA : ∀ k, k<T → f (n+B+k)=true)
    (hS : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (hlocal : Win f z (n+B+i-z)) (htarget : Win f s (n+B+T+j-s)) :
    j+1+(i+j-T)+1≤cN (fun x => f x=true) n (z-n) := by
  let u := (seg f 0 n).drop s
  let b := seg f n (z-n)
  let v := seg f z (n+B-z)
  have hu := block_suffix hw ((seg f 0 n).take s) u (List.take_append_drop s (seg f 0 n))
  have hd : u=seg f s (n-s) := by
    simpa only [u,Nat.zero_add] using seg_drop f 0 n s (by omega)
  have hnv : seg f n B=b++v := by
    rw [show B=(z-n)+(n+B-z) by omega,seg_add,show n+(z-n)=z by omega]
  have huv : seg f s (n+B-s)=u++b++v := by
    rw [show n+B-s=(n-s)+B by omega,seg_add,show s+(n-s)=n by omega,←hd,hnv]
    simp only [List.append_assoc]
  have hAword (K : Nat) (hK : K≤T) : seg f (n+B) K=List.replicate K true := by
    apply seg_A
    intro x hx hxK
    simpa only [Nat.add_sub_cancel' hx] using hA (x-(n+B)) (by omega)
  have hlword : seg f z (n+B+i-z)=v++List.replicate i true := by
    rw [show n+B+i-z=(n+B-z)+i by omega,seg_add,show z+(n+B-z)=n+B by omega,hAword i (by omega)]
  have htword : seg f s (n+B+T+j-s)=u++b++v++List.replicate T true++List.replicate j false := by
    rw [show n+B+T+j-s=(n+B+T-s)+j by omega,seg_add,show s+(n+B+T-s)=n+B+T by omega,
      seg_false f (n+B+T) j hS,show n+B+T-s=(n+B-s)+T by omega,seg_add,
      show s+(n+B-s)=n+B by omega,huv,hAword T (Nat.le_refl _)]
  have hlm : mass (v++List.replicate i true)=1 := by
    rw [←hlword,seg_mass]
    have hh := hlocal.2.1
    rw [show z+(n+B+i-z)=n+B+i by omega] at hh ⊢
    omega
  have hla : areaW (v++List.replicate i true)=0 := by rw [←hlword,←Ar_areaW]; exact hlocal.2.2
  have htm : mass (u++b++v++List.replicate T true++List.replicate j false)=1 := by
    rw [←htword,seg_mass]
    have hh := htarget.2.1
    rw [show s+(n+B+T+j-s)=n+B+T+j by omega] at hh ⊢
    omega
  have hta : areaW (u++b++v++List.replicate T true++List.replicate j false)=0 := by
    rw [←htword,←Ar_areaW]
    exact htarget.2.2
  have hne : u≠[] := by
    intro hz
    have hl : (seg f 0 n).length=n := seg_length f 0 n
    have hdlen := List.length_drop (l:=seg f 0 n) (i:=s)
    change u.length=(seg f 0 n).length-s at hdlen
    rw [hz,hl] at hdlen
    simp only [List.length_nil] at hdlen
    omega
  have hcross : 4≤runKey b+2*(cntF b : Int)^2 := by
    change 4≤runKey (seg f n (z-n))+2*(cntF (seg f n (z-n)) : Int)^2
    rw [hAS]
    exact cross_of_AS b0 b1
  have hb := source_prefix_A_strict u b v hu hne i T j hj hband hcross hlm hla htm hta
  have hc := ones_seg_eq_count f n (z-n)
  change ones b=_ at hc
  omega

end Recaman.SourceCrossSurplus
