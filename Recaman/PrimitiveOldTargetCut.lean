import Recaman.SourceCrossSurplus
import Recaman.OldTargetFreeAccounting

namespace Recaman.PrimitiveOldTargetCut

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse

/-- A primitive old target of mass>=2 forces a sharp A lower bound in
its arbitrary mixed future before the gap. No history-width bound is used. -/
theorem primitive_old_target_A_cut (u z : List Bool) (hu : BlockWord u) (hC : 2≤mass u) (j : Nat)
    (hm : mass (u++z++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate j false)=0) :
    2*(j : Int)+3≤ones z := by
  let R:=(j : Int)+1
  let C:=mass u
  let S:=(cntF z : Int)
  let X:=S-C
  have hk:=source_key_before_gap (u++z) 0 j (by simpa only [List.replicate_zero,List.append_nil] using hm)
    (by simpa only [List.replicate_zero,List.append_nil] using ha)
  rw [runKey_append] at hk
  have huKey : -2≤runKey u := by have hl:=block_area_quadratic_lower hu; unfold runKey; omega
  have hcross:=runKey_count_lower z
  have hmass:=mass_eq z
  have hcnt:=cntF_int z
  have hones:=ones_bounds z
  simp only [mass_append,mass_rep_false] at hm
  have hA : ones z=X+R := by dsimp [X,S,C,R]; omega
  have hXlo : -R≤X := by omega
  have hid : 2*X^2=2*R^2+runKey u+2*C^2+(runKey z+2*S^2) := by
    dsimp [R,C,S,X]
    grind only
  have hC2 : 2≤C := hC
  have hCsq:=Int.mul_nonneg (show 0≤C-2 by omega) (show 0≤C+2 by omega)
  have hbig : R<X := by
    by_cases he : R<X
    · exact he
    · have hp:=Int.mul_nonneg (show 0≤R-X by omega) (show 0≤R+X by omega)
      change -2*(cntF z : Int)^2≤runKey z at hcross
      change -2*S^2≤runKey z at hcross
      grind only
  dsimp [R] at hbig hA
  omega

/-- The full target square retains its old mass; all cross surplus is nonnegative. -/
theorem primitive_old_target_square_budget (u z : List Bool) (hu : BlockWord u) (j : Nat)
    (hm : mass (u++z++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate j false)=0) :
    (mass u)^2+((j : Int)+1)^2≤(ones z-((j : Int)+1))^2+1 := by
  let R:=(j : Int)+1
  let C:=mass u
  let S:=(cntF z : Int)
  let X:=S-C
  have hk:=source_key_before_gap (u++z) 0 j (by simpa only [List.replicate_zero,List.append_nil] using hm)
    (by simpa only [List.replicate_zero,List.append_nil] using ha)
  rw [runKey_append] at hk
  have huKey : -2≤runKey u := by have hl:=block_area_quadratic_lower hu; unfold runKey; omega
  have hcross:=runKey_count_lower z
  have hmass:=mass_eq z
  have hcnt:=cntF_int z
  simp only [mass_append,mass_rep_false] at hm
  have hA : ones z=X+R := by dsimp [X,S,C,R]; omega
  have hid : 2*X^2=2*R^2+runKey u+2*C^2+(runKey z+2*S^2) := by
    dsimp [R,C,S,X]
    grind only
  have hnonneg : 0≤runKey z+2*S^2 := by dsimp [S]; omega
  have hi : C^2+R^2≤X^2+1 := by omega
  have he : ones z-R=X := by omega
  change C^2+R^2≤(ones z-R)^2+1
  rw [he]
  exact hi

/-- The same sharp cut for an actual original-base old target. -/
theorem actual_old_target_A_cut (f : Nat → Bool) (n t B j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hC : 2≤mass (seg f t (n-t)))
    (hgap : ∀ x, n+B≤x → x<n+B+j → f x=false)
    (htarget : Win f t (n+B+j-t)) :
    2*j+3≤cN (fun x=>f x=true) n B := by
  let u:=seg f t (n-t)
  let z:=seg f n B
  have hd:=seg_drop f 0 n t (by omega)
  simp only [Nat.zero_add,hpre] at hd
  have hu : BlockWord u := by rw [show u=w.drop t by dsimp [u]; exact hd.symm]; exact block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hs : seg f t (n+B+j-t)=u++z++List.replicate j false := by
    rw [show n+B+j-t=(n-t+B)+j by omega,seg_add,
      show t+(n-t+B)=n+B by omega,seg_false f (n+B) j hgap,
      seg_add,show t+(n-t)=n by omega]
  have hm : mass (u++z++List.replicate j false)=1 := by
    rw [←hs,seg_mass]
    have he:=htarget.2.1
    rw [show t+(n+B+j-t)=n+B+j by omega] at he ⊢
    omega
  have ha : areaW (u++z++List.replicate j false)=0 := by rw [←hs,←Ar_areaW]; exact htarget.2.2
  have hc:=primitive_old_target_A_cut u z hu hC j hm ha
  have he:=ones_seg_eq_count f n B
  change ones z=_ at he
  omega

theorem actual_old_target_square_budget (f : Nat → Bool) (n t B j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hgap : ∀ x, n+B≤x → x<n+B+j → f x=false)
    (htarget : Win f t (n+B+j-t)) :
    (mass (seg f t (n-t)))^2+((j : Int)+1)^2≤
      ((cN (fun x=>f x=true) n B : Int)-((j : Int)+1))^2+1 := by
  let u:=seg f t (n-t)
  let z:=seg f n B
  have hd:=seg_drop f 0 n t (by omega)
  simp only [Nat.zero_add,hpre] at hd
  have hu : BlockWord u := by rw [show u=w.drop t by dsimp [u]; exact hd.symm]; exact block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hs : seg f t (n+B+j-t)=u++z++List.replicate j false := by
    rw [show n+B+j-t=(n-t+B)+j by omega,seg_add,
      show t+(n-t+B)=n+B by omega,seg_false f (n+B) j hgap,
      seg_add,show t+(n-t)=n by omega]
  have hm : mass (u++z++List.replicate j false)=1 := by
    rw [←hs,seg_mass]
    have he:=htarget.2.1
    rw [show t+(n+B+j-t)=n+B+j by omega] at he ⊢
    omega
  have ha : areaW (u++z++List.replicate j false)=0 := by rw [←hs,←Ar_areaW]; exact htarget.2.2
  have hc:=primitive_old_target_square_budget u z hu j hm ha
  have he:=ones_seg_eq_count f n B
  change ones z=_ at he
  rw [he] at hc
  exact hc

end Recaman.PrimitiveOldTargetCut
