import Recaman.SourceCrossSurplus

namespace Recaman.DelayedSourcePrefix

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A counted late local source pays its delay in prior A signs.
Mass at least two supplies strictness even if the prefix has no AS pair. -/
theorem delay_source_prefix_A (u b x : List Bool) (hu : BlockWord u) (hC : 2≤mass u)
    (i T j : Nat) (hi : i<T) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (x++List.replicate i true)=1) (ha1 : areaW (x++List.replicate i true)=0)
    (hm2 : mass (u++b++x++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++b++x++List.replicate T true++List.replicate j false)=0) :
    (j : Int)+2+((i : Int)+(j : Int)-(T : Int))≤ones b := by
  let K:=(i : Int)+(j : Int)-(T : Int)
  let R:=(j : Int)+1
  let A:=ones b
  have hid:=Recaman.SourceCrossSurplus.two_source_cross_identity u b x i T j hm1 ha1 hm2 ha2
  change 2*(A-K)^2=2*R^2+runKey u+2*(mass u)^2+
    (runKey b+2*(cntF b : Int)^2)+4*K*(cntF x : Int)-2 at hid
  have hkey : -2≤runKey u := by
    have hh:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hcross:=runKey_count_lower b
  have hC2:=Int.mul_nonneg (show 0≤mass u-2 by omega) (show 0≤mass u+2 by omega)
  have hdelay := Int.mul_nonneg (show 0≤K by dsimp [K]; omega) (show 0≤(cntF x : Int) by omega)
  have hA : 0≤A := (ones_bounds b).1
  have hKR : K≤R-2 := by dsimp [K,R]; omega
  change R+K+1≤A
  by_cases h : R+K+1≤A
  · exact h
  · exfalso
    have hp := Int.mul_nonneg (show 0≤R-(A-K) by omega) (show 0≤R+(A-K) by omega)
    grind only

/-- Original actual windows, including the full history before the target. -/
theorem actual_delay_source_prefix_A (f : Nat → Bool) (n s z B i T j : Nat)
    (hw : BlockWord (seg f 0 n)) (hC : 2≤mass (seg f s (n-s))) (hs : s<n) (hz : n≤z) (hzB : z≤n+B)
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
  have huC : 2≤mass u := by rwa [hd]
  have hb := delay_source_prefix_A u b v hu huC i T j hi hj hband hlm hla htm hta
  have hc := ones_seg_eq_count f n (z-n)
  change ones b=_ at hc
  omega

end Recaman.DelayedSourcePrefix
