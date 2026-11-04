import Recaman.GenuineFourOldCounterBand
import Recaman.FourthActualSeven

namespace Recaman.TopGapCounter

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem top_gap_counter_excluded (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : j=14) : False := by
  have hb:=Recaman.GenuineFourOldCounterBand.genuine_four_old_counter_band f n t h M m L s U v T j C w hw hpre ht hC
    hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad
  let B:=h+M+m+L+s+U+v+T
  let H:=h+M+m+L+s+U
  let A:=cN (fun x=>f x=true) n B
  let F:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B
  have hC2:=hb.2.2.2.2.1
  have hAlo:=Recaman.PrimitiveOldTargetCut.actual_old_target_A_cut f n t B j w hw hpre ht (by omega)
    (by simpa only [B,Nat.add_assoc] using hgap) (by simpa only [B,Nat.add_assoc] using htarget)
  have hA31 : A=31 := by have he:=hb.2.2.1; change 2*j+3≤A at hAlo; change A≤31 at he; omega
  have hF14 : F=14 := by
    have hpart:=addition_endable_partition f n B
    have hsup:=Recaman.FourRunSupplySeventeen.four_run_supply_le_seventeen f n h M m L s U v T w hw hpre hM hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
    have hf:=hb.2.1
    change A=cN (EndN f 0) n B+F at hpart
    change cN (EndN f 0) n B≤17 at hsup
    change F≤14 at hf
    omega
  have hE17 : cN (EndN f 0) n B=17 := by
    have he:=addition_endable_partition f n B
    change A=cN (EndN f 0) n B+F at he
    omega
  have hh : 1≤h := by
    by_cases hz : h=0
    · have ha : f n=true := by simpa only [hz,Nat.add_zero] using hA 0 hM
      have hp:=hpos 1 (by omega) (by omega)
      have hs0 : cN (fun x=>f x=false) n 1=0 := by
        apply cN_zero_of
        intro x hx hx1 he
        have heq : x=n := by omega
        rw [heq,ha] at he
        contradiction
      omega
    · omega
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega))
  have hlast7:=Recaman.FourthActualSeven.fourth_actual_seven f n h M m L s U v T w hw hpre hh hm hs hv
    hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hsep0 : cN (EndN f 0) (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxv he
    have hf:=hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxv; omega)
    rw [hf] at he
    exact Bool.noConfusion he.1
  have hc1:=cN_add (EndN f 0) n H v
  have hc2:=cN_add (EndN f 0) n (H+v) T
  have hEH10 : cN (EndN f 0) n H=10 := by
    change cN (EndN f 0) n H≤10 at hhead10
    change cN (EndN f 0) (n+H+v) T≤7 at hlast7
    change cN (EndN f 0) n (H+v+T)=17 at hE17
    simp only [Nat.add_assoc] at hc1 hc2 hsep0 hlast7
    omega
  have hfree4 : 4≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H := by
    by_cases hsml : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H≤3
    · have hb:=positive_r3_additions_free_bound f n 0 H hw (by simpa using hpre)
        (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega)) hsml
      have he:=addition_endable_partition f n H
      omega
    · omega
  have hHA14 : 14≤cN (fun x=>f x=true) n H := by have he:=addition_endable_partition f n H; omega
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hAhead : (14 : Int)≤(M : Int)+(L : Int)+(U : Int) := by
    have he:=ones_seg_eq_count f n H
    dsimp [H] at he
    rw [hhead] at he
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at he
    omega
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
  have hcross : 68≤runKey (seg f n B)+2*(cntF (seg f n B) : Int)^2 := by
    rw [hraw]
    have he:=Recaman.GenuineFourCross.head_A_cross_lower h M m L s U v T hM hm hL hs hU hv
    omega
  have hsq:=Recaman.GenuineFourCross.actual_cross_charge f n t B j 34 w hw hpre ht hcross
    (by simpa only [B,Nat.add_assoc] using hgap) (by simpa only [B,Nat.add_assoc] using htarget)
  rw [hC] at hsq
  change (C : Int)^2+((j : Int)+1)^2+34≤((A : Int)-((j : Int)+1))^2+1 at hsq
  rw [hj,hA31] at hsq
  have hCsq:=Int.mul_nonneg (show 0≤(C : Int) by omega) (show 0≤(C : Int) by omega)
  grind only

end Recaman.TopGapCounter
