import Recaman.PrimitiveOldTargetCut
import Recaman.SourceFamilyFreeCount
import Recaman.UnitTargetSASProfile
import Recaman.MomentTargetProfile

namespace Recaman.GenuineFourCross

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse Recaman.UnitTargetSASProfile

/-- Six forced A-before-S pairs contribute24 to the full literal cross. -/
theorem four_cross_twenty_four (h M m L s U v T : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) :
    let z:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++List.replicate T true
    24≤runKey z+2*(cntF z : Int)^2 := by
  dsimp only
  rw [runKey_append_A,runKey_append_S,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
  simp only [cntF_append,cntF_replicate_S,cntF_A,mass_append,mass_rep_false,mass_replicate_A,Int.natCast_add]
  have hp:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(m : Int)+(s : Int)+(v : Int) by omega)
  have hq:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int)+(v : Int) by omega)
  have hr:=Int.mul_nonneg (show 0≤(U : Int)-1 by omega) (show 0≤(v : Int) by omega)
  grind only

/-- An explicit cross lower bound is retained in the same-target square. -/
theorem primitive_cross_square (u z : List Bool) (hu : BlockWord u) (j : Nat)
    (hm : mass (u++z++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate j false)=0)
    (hcross : 24≤runKey z+2*(cntF z : Int)^2) :
    (mass u)^2+((j : Int)+1)^2+12≤(ones z-((j : Int)+1))^2+1 := by
  let R:=(j : Int)+1
  let C:=mass u
  let S:=(cntF z : Int)
  let X:=S-C
  have hk:=source_key_before_gap (u++z) 0 j (by simpa only [List.replicate_zero,List.append_nil] using hm)
    (by simpa only [List.replicate_zero,List.append_nil] using ha)
  rw [runKey_append] at hk
  have huKey : -2≤runKey u := by have hl:=block_area_quadratic_lower hu; unfold runKey; omega
  have hmass:=mass_eq z
  have hcnt:=cntF_int z
  simp only [mass_append,mass_rep_false] at hm
  have hA : ones z=X+R := by dsimp [X,S,C,R]; omega
  have hid : 2*X^2=2*R^2+runKey u+2*C^2+(runKey z+2*S^2) := by
    dsimp [R,C,S,X]
    grind only
  change 24≤runKey z+2*S^2 at hcross
  have hi : C^2+R^2+12≤X^2+1 := by omega
  have he : ones z-R=X := by omega
  change C^2+R^2+12≤(ones z-R)^2+1
  rw [he]
  exact hi

theorem actual_cross_square_budget (f : Nat → Bool) (n t B j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hcross : 24≤runKey (seg f n B)+2*(cntF (seg f n B) : Int)^2)
    (hgap : ∀ x, n+B≤x → x<n+B+j → f x=false)
    (htarget : Win f t (n+B+j-t)) :
    (mass (seg f t (n-t)))^2+((j : Int)+1)^2+12≤
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
  have hc:=primitive_cross_square u z hu j hm ha hcross
  have he:=ones_seg_eq_count f n B
  change ones z=_ at he
  rw [he] at hc
  exact hc

theorem head_A_cross_lower (h M m L s U v T : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) :
    let z:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++List.replicate T true
    4*((M : Int)+(L : Int)+(U : Int))+12≤runKey z+2*(cntF z : Int)^2 := by
  dsimp only
  rw [runKey_append_A,runKey_append_S,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
  simp only [cntF_append,cntF_replicate_S,cntF_A,mass_append,mass_rep_false,mass_replicate_A,Int.natCast_add]
  have hp:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(m : Int)+(s : Int) by omega)
  have hq:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
  have hvA:=Int.mul_nonneg (show 0≤(v : Int)-1 by omega) (show 0≤(M : Int)+(L : Int)+(U : Int) by omega)
  grind only

theorem primitive_cross_charge (u z : List Bool) (hu : BlockWord u) (j : Nat) (Q : Int)
    (hm : mass (u++z++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate j false)=0)
    (hcross : 2*Q≤runKey z+2*(cntF z : Int)^2) :
    (mass u)^2+((j : Int)+1)^2+Q≤(ones z-((j : Int)+1))^2+1 := by
  let R:=(j : Int)+1
  let C:=mass u
  let S:=(cntF z : Int)
  let X:=S-C
  have hk:=source_key_before_gap (u++z) 0 j (by simpa only [List.replicate_zero,List.append_nil] using hm)
    (by simpa only [List.replicate_zero,List.append_nil] using ha)
  rw [runKey_append] at hk
  have huKey : -2≤runKey u := by have hl:=block_area_quadratic_lower hu; unfold runKey; omega
  have hmass:=mass_eq z
  have hcnt:=cntF_int z
  simp only [mass_append,mass_rep_false] at hm
  have hA : ones z=X+R := by dsimp [X,S,C,R]; omega
  have hid : 2*X^2=2*R^2+runKey u+2*C^2+(runKey z+2*S^2) := by
    dsimp [R,C,S,X]
    grind only
  change 2*Q≤runKey z+2*S^2 at hcross
  have hi : C^2+R^2+Q≤X^2+1 := by omega
  have he : ones z-R=X := by omega
  change C^2+R^2+Q≤(ones z-R)^2+1
  rw [he]
  exact hi

theorem actual_cross_charge (f : Nat → Bool) (n t B j : Nat) (Q : Int) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hcross : 2*Q≤runKey (seg f n B)+2*(cntF (seg f n B) : Int)^2)
    (hgap : ∀ x, n+B≤x → x<n+B+j → f x=false)
    (htarget : Win f t (n+B+j-t)) :
    (mass (seg f t (n-t)))^2+((j : Int)+1)^2+Q≤
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
  have hc:=primitive_cross_charge u z hu j Q hm ha hcross
  have he:=ones_seg_eq_count f n B
  change ones z=_ at he
  rw [he] at hc
  exact hc

end Recaman.GenuineFourCross
