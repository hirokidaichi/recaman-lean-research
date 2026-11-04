import Recaman.FourRunSupplyBudget
import Recaman.PrimitiveOldTargetCut

namespace Recaman.FourRunOldCounterBand

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem four_run_old_counter_band (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hC : mass (seg f t (n-t))=(C : Int))
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
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
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤16 ∧
    cN (fun x=>f x=true) n (h+M+m+L+s+U+v+T)≤35 ∧ j≤16 ∧ 2≤C ∧ C≤17 ∧
    cN (fun x=>f x=false) n (h+M+m+L+s+U+v+T)≤35 ∧
    h+M+m+L+s+U+v+T≤70 ∧ n-t≤42 ∧ n+h+M+m+L+s+U+v+T+j-t≤128 := by
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
  have hsup:=Recaman.FourRunSupplyBudget.four_run_supply_budget f n h M m L s U v T w hw hpre hm hs hv
    hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  change cN (EndN f 0) n B≤19 at hsup
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
  have hj16 : j≤16 := by omega
  have hF16 : F≤16 := by omega
  have hA35 : A≤35 := by omega
  have hsq:=Recaman.PrimitiveOldTargetCut.actual_old_target_square_budget f n t B j w hw hpre ht
    (by simpa only [B,Nat.add_assoc] using hgap)
    (by simpa only [B,Nat.add_assoc] using htarget)
  rw [hC] at hsq
  change (C : Int)^2+((j : Int)+1)^2≤((A : Int)-((j : Int)+1))^2+1 at hsq
  have hC17 : C≤17 := by
    by_cases he : C≤17
    · exact he
    · let X:=(A : Int)-((j : Int)+1)
      have hX0 : 0≤X := by dsimp [X]; omega
      have hX18 : X≤18 := by dsimp [X]; omega
      have hpX:=Int.mul_nonneg (show 0≤18-X by omega) (show 0≤18+X by omega)
      have hpC:=Int.mul_nonneg (show 0≤(C : Int)-18 by omega) (show 0≤(C : Int)+18 by omega)
      have hpR:=Int.mul_nonneg (show 0≤(j : Int)+1-5 by omega) (show 0≤(j : Int)+1+5 by omega)
      change (C : Int)^2+((j : Int)+1)^2≤X^2+1 at hsq
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
  have hS35 : cN (fun x=>f x=false) n B≤35 := by
    have hA18 : (A : Int)-((j : Int)+1)≤18 := by omega
    change Fw f (n+B)=Fw f n+(A : Int)-(cN (fun x=>f x=false) n B : Int) ∧ _ at hwalk
    omega
  have hB70 : B≤70 := by change _ ∧ A+_=B at hwalk; omega
  have holdlen:=block_prefix_suffix_length_bound f n 0 t hw (by simpa using hpre) (by omega)
  have hold42 : n-t≤42 := by omega
  have hwin128 : n+B+j-t≤128 := by omega
  exact ⟨hF4,hF16,hA35,hj16,hC2,hC17,hS35,hB70,hold42,hwin128⟩

end Recaman.FourRunOldCounterBand
