import Recaman.LocalSourcePrefixBudget

namespace Recaman.PrefixKeySourceBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- Only the scalar key lower bound on u is needed. Its mass can have
either sign; b and the original history remain arbitrary. -/
theorem continuation_key_lower (u b : List Bool) (hkey : -2≤runKey u)
    (hm : 0≤mass (u++b)) : -2-2*(ones b)^2≤runKey (u++b) := by
  let C := mass u
  let A := ones b
  let S := (cntF b : Int)
  have hA : 0≤A := (ones_bounds b).1
  have hS : 0≤S := by dsimp [S]; omega
  have hmb : mass b=A-S := by
    have hc := cntF_int b
    have he := mass_eq b
    dsimp [A,S]
    omega
  have hSA : S≤C+A := by rw [mass_append,hmb] at hm; dsimp [C]; omega
  have hsq : (S-C)^2≤C^2+A^2 := by
    by_cases hh : S≤C
    · have hp := Int.mul_nonneg hS (show 0≤2*C-S by omega)
      have hAA := Int.mul_nonneg hA hA
      grind
    · have hp := Int.mul_nonneg (show 0≤A-(S-C) by omega) (show 0≤A+(S-C) by omega)
      have hCC := Int.sq_nonneg C
      grind
  have hku : -2≤runKey u := hkey
  have hkb := runKey_count_lower b
  rw [runKey_append]
  change -2-2*A^2≤runKey u+runKey b+4*C*S
  change -2*S^2≤runKey b at hkb
  grind

/-- Source cut from a primitive quantitative key premise, without
BlockWord grammar or nonnegative old-source mass. -/
theorem local_source_prefix_A_of_key (u b v : List Bool) (hkey : -2≤runKey u)
    (i T j : Nat) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (v++List.replicate i true)=1)
    (ha1 : areaW (v++List.replicate i true)=0)
    (hm2 : mass (u++b++v++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++b++v++List.replicate T true++List.replicate j false)=0) :
    (j : Int)+1≤ones b := by
  have hpm : 0≤mass (u++b) := by
    simp only [mass_append,mass_replicate_A,mass_rep_false] at hm1 hm2 ⊢
    omega
  have hlow := continuation_key_lower u b hkey hpm
  have hk1 := source_key_before_gap v i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [List.replicate_zero,List.append_nil] using ha1)
  have hk2 := source_key_before_gap (u++b++v) T j hm2 ha2
  rw [runKey_append] at hk2
  have hcross := Int.mul_nonneg hpm (show 0≤(cntF v : Int) by omega)
  have hquad : ((j : Int)+1)^2≤(ones b)^2+2 := by grind
  have hA : 0≤ones b := (ones_bounds b).1
  by_cases hh : (j : Int)+1≤ones b
  · exact hh
  · have hp := Int.mul_nonneg (show 0≤(j : Int)-ones b by omega)
      (show 0≤(j : Int)+ones b by omega)
    grind

/-- Actual all-length/all-run form. A local source before the last A
ray must have at least j+1 actual A signs before its start. The original
base0 windows, the same old source, and all earlier history are retained. -/
theorem actual_local_source_prefix_A_of_key (f : Nat → Bool) (n s z B i T j : Nat)
    (hkey : -2≤runKey (seg f s (n-s))) (hs : s<n) (hz : n≤z) (hzB : z≤n+B)
    (hi : i<T) (hj : 2≤j) (hband : T≤i+j)
    (hA : ∀ k, k<T → f (n+B+k)=true)
    (hS : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (hlocal : Win f z (n+B+i-z)) (htarget : Win f s (n+B+T+j-s)) :
    j+1≤cN (fun x => f x=true) n (z-n) := by
  let u := (seg f 0 n).drop s
  let b := seg f n (z-n)
  let v := seg f z (n+B-z)
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
  have hku : -2≤runKey u := by rw [hd]; exact hkey
  have hb := local_source_prefix_A_of_key u b v hku i T j hj hband hlm hla htm hta
  have hc := ones_seg_eq_count f n (z-n)
  change ones b=_ at hc
  omega

end Recaman.PrefixKeySourceBudget
