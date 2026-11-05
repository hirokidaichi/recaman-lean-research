import Recaman.HighGapLastSix
import Recaman.FourthEarlyCuts
import Recaman.ThreeHeadFreeCuts
import Recaman.FourthUnitSeparators
import Recaman.HighGapScalarCuts

namespace Recaman.FourHighGapUnitCut

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Every original genuine four-run old-target counter has gap below
nine. The sole unit-separator branch cannot pay its fifth last-ray clock. -/
theorem four_high_gap_excluded (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : 9≤j) : False := by
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let r:=cN P n H
  let F:=cN P n (B+T)
  let E:=cN (EndN f 0) (n+B) T
  let N:=(M : Int)+(L : Int)+(U : Int)
  let Q:=N*(v : Int)+(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  let R:=(j : Int)+1
  let X:=(A : Int)-R
  have hb:=Recaman.HighGapLastSix.high_gap_last_six f n t h M m L s U v T j C w hw hpre ht hC
    hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad hj
  change 2≤C ∧ 2*j+3≤A ∧ A≤j+16 ∧ T≤j+2 ∧
    cN (EndN f 0) n H≤10 ∧ 4≤r ∧ E≤6 ∧
    cN (EndN f 0) n (B+T)=cN (EndN f 0) n H+E ∧ _ at hb
  rcases hb with ⟨hC2,hAlo,hAhi,hT2,hhead,hr4,hE6,hsplit,hword⟩
  have hF : F≤j := by change F<j+1 at hbad; omega
  have hpart:=addition_endable_partition f n (B+T)
  rw [hsplit] at hpart
  change A=cN (EndN f 0) n H+E+F at hpart
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by
    simpa only [B,H,Nat.add_assoc] using hA4
  have hgap' : ∀ a, n+B+T≤a → a<n+B+T+j → f a=false := by
    simpa only [B,H,Nat.add_assoc] using hgap
  have hW : Win f t (n+B+T+j-t) := by
    simpa only [B,H,Nat.add_assoc] using htarget
  have hpT:=addition_endable_partition f (n+B) T
  rw [count_A_run f (n+B) T hA4'] at hpT
  change T=E+cN P (n+B) T at hpT
  have hfa:=cN_add P n B T
  change F=cN P n B+cN P (n+B) T at hfa
  have hfb : cN P n B=r+cN P (n+H) v := cN_add P n H v
  have hfree : T+r≤j+E := by omega
  have hw0 : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have hcuts:=Recaman.FourthEarlyCuts.fourth_early_cuts f n t B h M m L s U v T j
    hw0 ht (by omega) hv hword hA4' hgap' hW
  change E≤T-j+5 ∧ (M≤j → E≤T-j+3) ∧ (M+L≤j → E≤T-j+1) at hcuts
  obtain ⟨hcut0,hcut1,hcut2⟩:=hcuts
  have hraw:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v T
    hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hAeq : (A : Int)=N+(T : Int) := by
    have he:=ones_seg_eq_count f n (B+T)
    change ones (seg f n (B+T))=(A : Int) at he
    rw [hraw] at he
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at he
    dsimp [N]
    omega
  have hcross : runKey (seg f n (B+T))+2*(cntF (seg f n (B+T)) : Int)^2=4*Q := by
    rw [hraw]
    exact Recaman.FourCrossExact.four_cross_exact h M m L s U v T
  have hsq:=Recaman.GenuineFourCross.actual_cross_charge f n t (B+T) j (2*Q) w hw hpre ht
    (by rw [hcross]; omega)
    (by simpa only [Nat.add_assoc] using hgap')
    (by simpa only [Nat.add_assoc] using hW)
  rw [hC] at hsq
  change (C : Int)^2+R^2+2*Q≤X^2+1 at hsq
  have hcutsHead:=Recaman.ThreeHeadFreeCuts.head_free_cuts f n h M m L s U w hw hpre
    hS hA hS2 hA2 (fun k hk hkH=>hpos k hk (by omega))
  have hMcost : M≤r+2 := hcutsHead.1
  have hcut0' (he : (T : Int)≤(j : Int)) : (E : Int)≤5 := by omega
  have hcut1' (he : (M : Int)≤(j : Int)) (ht : (j : Int)≤(T : Int)) :
      (E : Int)≤(T : Int)-(j : Int)+3 := by
    have hh:=hcut1 (by omega)
    omega
  have hcut2' (he : (M : Int)≤(j : Int)) (ht : (T : Int)≤(j : Int)) :
      (E : Int)≤3 := by
    have hh:=hcut1 (by omega)
    omega
  have hcut3' (he : (M : Int)+(L : Int)≤(j : Int)) (ht : (T : Int)≤(j : Int)) :
      (E : Int)≤1 := by
    have hh:=hcut2 (by omega)
    omega
  have hcase:=Recaman.HighGapScalarCuts.high_gap_unit_candidate (j : Int) (M : Int) (m : Int)
    (L : Int) (s : Int) (U : Int) (v : Int) (T : Int) (C : Int) (A : Int) (r : Int)
    (cN (EndN f 0) n H : Int) (E : Int) (F : Int)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by dsimp [N] at hAeq; omega) hcut0' hcut1' hcut2' hcut3' hsq
  rcases hcase with ⟨hj9,_,hT6,hm1,hs1,hv1,hE5⟩
  let z:=List.replicate M true++List.replicate 1 false++List.replicate L true++
    List.replicate 1 false++List.replicate U true++List.replicate 1 false
  have hz : seg f n B=List.replicate h false++z := by
    have hm' : m=1 := by omega
    have hs' : s=1 := by omega
    have hv' : v=1 := by omega
    exact hword.trans (by rw [hm',hs',hv'])
  have hlocal : rayCount z T≤4 := Recaman.FourthUnitSeparators.unit_separators_after_initial_four M L U T hL hU
  have hc:=Recaman.OldTargetEarlyClockBudget.old_target_early_word_budget f n t B T j
    (List.replicate h false) z hw0 ht (by omega) hz (by rw [ones_replicate_S]; omega) hA4' hgap' hW
  change E≤T-j+rayCount z T at hc
  omega

end Recaman.FourHighGapUnitCut
