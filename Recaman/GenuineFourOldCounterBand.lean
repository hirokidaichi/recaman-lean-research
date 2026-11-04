import Recaman.FourRunSupplySeventeen
import Recaman.GenuineFourCross
import Recaman.PrimitiveOldTargetCut

namespace Recaman.GenuineFourOldCounterBand

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem genuine_four_old_counter_band (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hC : mass (seg f t (n-t))=(C : Int))
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U) (hT : 1≤T) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    4≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) ∧
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤14 ∧
    cN (fun x=>f x=true) n (h+M+m+L+s+U+v+T)≤31 ∧ j≤14 ∧ 2≤C ∧ C≤14 ∧
    cN (fun x=>f x=false) n (h+M+m+L+s+U+v+T)≤30 ∧
    h+M+m+L+s+U+v+T≤61 ∧ n-t≤35 ∧ n+h+M+m+L+s+U+v+T+j-t≤110 ∧
    (C : Int)^2+((j : Int)+1)^2+12≤
      ((cN (fun x=>f x=true) n (h+M+m+L+s+U+v+T) : Int)-((j : Int)+1))^2+1 ∧
    cN (fun x=>f x=false) n (h+M+m+L+s+U+v+T)+j+1=
      cN (fun x=>f x=true) n (h+M+m+L+s+U+v+T)+C := by
  let B:=h+M+m+L+s+U+v+T
  let A:=cN (fun x=>f x=true) n B
  let F:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B
  have hposB:=hpos B (by dsimp [B]; omega) (by omega)
  have hC2:=Recaman.OldTargetFreeAccounting.old_target_counter_mass f n t B j C (by omega) hC hposB
    (by simpa only [B,Nat.add_assoc] using hgap)
    (by simpa only [B,Nat.add_assoc] using htarget)
    (by simpa only [B] using hbad)
  have hAlo:=Recaman.PrimitiveOldTargetCut.actual_old_target_A_cut f n t B j w hw hpre ht (by omega)
    (by simpa only [B,Nat.add_assoc] using hgap)
    (by simpa only [B,Nat.add_assoc] using htarget)
  change 2*j+3≤A at hAlo
  have hsup:=Recaman.FourRunSupplySeventeen.four_run_supply_le_seventeen f n h M m L s U v T w hw hpre hM hm hs hv
    hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  change cN (EndN f 0) n B≤17 at hsup
  have hpart:=addition_endable_partition f n B
  change A=cN (EndN f 0) n B+F at hpart
  change F<j+1 at hbad
  have hF4 : 4≤F := by
    by_cases hsml : F≤3
    · have hb:=positive_r3_additions_free_bound f n 0 B hw (by simpa using hpre)
        (by simpa only [B] using hpos) hsml
      change A≤2*F+1 at hb
      omega
    · omega
  have hj14 : j≤14 := by omega
  have hF14 : F≤14 := by omega
  have hA31 : A≤31 := by omega
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hraw : seg f n B=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++List.replicate T true := by
    rw [show B=(h+M+m+L+s+U)+v+T by rfl,seg_add,seg_add,hhead,
      seg_false f (n+(h+M+m+L+s+U)) v (by simpa only [Nat.add_assoc] using hS4)]
    congr 1
    apply seg_A
    intro x hx hxT
    have he:=hA4 (x-(n+h+M+m+L+s+U+v)) (by omega)
    rw [show n+h+M+m+L+s+U+v+(x-(n+h+M+m+L+s+U+v))=x by omega] at he
    exact he
  have hcross : 24≤runKey (seg f n B)+2*(cntF (seg f n B) : Int)^2 := by
    rw [hraw]
    exact Recaman.GenuineFourCross.four_cross_twenty_four h M m L s U v T hM hm hL hs hU hv
  have hsq:=Recaman.GenuineFourCross.actual_cross_square_budget f n t B j w hw hpre ht hcross
    (by simpa only [B,Nat.add_assoc] using hgap)
    (by simpa only [B,Nat.add_assoc] using htarget)
  rw [hC] at hsq
  change (C : Int)^2+((j : Int)+1)^2+12≤((A : Int)-((j : Int)+1))^2+1 at hsq
  have hC14 : C≤14 := by
    by_cases he : C≤14
    · exact he
    · let X:=(A : Int)-((j : Int)+1)
      have hX0 : 0≤X := by dsimp [X]; omega
      have hX16 : X≤16 := by dsimp [X]; omega
      have hpX:=Int.mul_nonneg (show 0≤16-X by omega) (show 0≤16+X by omega)
      have hpC:=Int.mul_nonneg (show 0≤(C : Int)-15 by omega) (show 0≤(C : Int)+15 by omega)
      have hpR:=Int.mul_nonneg (show 0≤(j : Int)+1-5 by omega) (show 0≤(j : Int)+1+5 by omega)
      change (C : Int)^2+((j : Int)+1)^2+12≤X^2+1 at hsq
      grind only
  have hCwalk:=hC
  rw [seg_mass,show t+(n-t)=n by omega] at hCwalk
  have htar:=htarget.2.1
  rw [show t+(n+h+M+m+L+s+U+v+T+j-t)=n+B+j by dsimp [B]; omega] at htar
  have hgm : Fw f (n+B+j)-Fw f (n+B)= -(j : Int) := by
    have hm : mass (seg f (n+B) j)= -(j : Int) := by
      rw [seg_false f (n+B) j (by simpa only [B,Nat.add_assoc] using hgap),mass_rep_false]
    rw [seg_mass] at hm
    exact hm
  have hwalk:=cN_walk f n B
  have hS30 : cN (fun x=>f x=false) n B≤30 := by
    have hA16 : (A : Int)-((j : Int)+1)≤16 := by omega
    change Fw f (n+B)=Fw f n+(A : Int)-(cN (fun x=>f x=false) n B : Int) ∧ _ at hwalk
    omega
  have hB61 : B≤61 := by change _ ∧ A+_=B at hwalk; omega
  have holdlen:=block_prefix_suffix_length_bound f n 0 t hw (by simpa using hpre) (by omega)
  have hold35 : n-t≤35 := by omega
  have hwin110 : n+B+j-t≤110 := by omega
  have hbalance : cN (fun x=>f x=false) n B+j+1=A+C := by
    change Fw f (n+B)=Fw f n+(A : Int)-(cN (fun x=>f x=false) n B : Int) ∧ _ at hwalk
    omega
  refine ⟨hF4,hF14,hA31,hj14,hC2,hC14,hS30,hB61,hold35,?_,hsq,hbalance⟩
  simpa only [B,Nat.add_assoc] using hwin110

end Recaman.GenuineFourOldCounterBand
