import Recaman.UnitTargetZeroCross

namespace Recaman.UnitTargetActualBoundary

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

theorem actual_unit_zero_cross (f : Nat → Bool) (n s z B i T j : Nat)
    (hw : BlockWord (seg f 0 n)) (hC : mass ((seg f 0 n).drop s)=1) (a q : Nat)
    (hprefix : seg f n (z-n)=List.replicate a false++List.replicate q true) (hq : q≤j+2)
    (hsuf : 1≤cntF (seg f z (n+B-z))) (hs : s<n) (hz : n≤z) (hzB : z≤n+B)
    (hi : i<T) (hj : 2≤j) (hband : T≤i+j)
    (hA : ∀ k, k<T → f (n+B+k)=true)
    (hS : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (hlocal : Win f z (n+B+i-z)) (htarget : Win f s (n+B+T+j-s)) :
    q=j+1 ∧ a=j+2 ∧ i+j=T := by
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
  have hu1 : u=[true] := block_mass_one hu hC
  rw [hu1] at htm hta
  change seg f n (z-n)=_ at hprefix
  have hb : b=List.replicate a false++List.replicate q true := hprefix
  rw [hb] at htm hta
  exact Recaman.UnitTargetZeroCross.source_zero_cross_boundary v a q i T j hsuf hj hband hq hlm hla htm hta

end Recaman.UnitTargetActualBoundary
