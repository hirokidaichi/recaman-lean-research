import Recaman.HighGapLastSix
import Recaman.FourthEarlyCuts
import Recaman.ThreeHeadFreeCuts
import Recaman.FourCrossExact
import Recaman.LongFirstMiddleOne

namespace Recaman.FourHighGapExcluded

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem target_square_impossible (R X Q C R0 X0 Q0 : Int)
    (hR0 : 0≤R0) (hR : R0≤R) (hX0 : 0≤X) (hX : X≤X0) (hQ : Q0≤Q)
    (hnum : X0^2+1<R0^2+2*Q0) (h : C^2+R^2+2*Q≤X^2+1) : False := by
  have hr := Recaman.ShortCounterFactorBounds.square_lower R R0 hR0 hR
  have hx := Recaman.ShortCounterFactorBounds.square_lower X0 X hX0 hX
  have hc := Int.sq_nonneg C
  omega

/-- The joint early-band count and the same target square exclude
every genuine four-run counter with gap at least nine. -/
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
  have hXlo : 0≤X := by dsimp [X,R]; omega
  have hcross : runKey (seg f n (B+T))+2*(cntF (seg f n (B+T)) : Int)^2=4*Q := by
    rw [hraw]
    exact Recaman.FourCrossExact.four_cross_exact h M m L s U v T
  have hQlo : N+2*(M : Int)+(L : Int)≤Q := by
    have he:=Recaman.FourCrossExact.four_cross_head_first_lower h M m L s U v T hm hs hv
    change 4*(N+2*(M : Int)+(L : Int))≤_ at he
    rw [hraw] at hcross
    omega
  have hsq:=Recaman.GenuineFourCross.actual_cross_charge f n t (B+T) j (2*Q) w hw hpre ht
    (by rw [hcross]; omega)
    (by simpa only [Nat.add_assoc] using hgap')
    (by simpa only [Nat.add_assoc] using hW)
  rw [hC] at hsq
  change (C : Int)^2+R^2+2*Q≤X^2+1 at hsq
  by_cases hshort : M≤j
  · have he:=hcut1 hshort
    have hTsmall : T<j := by omega
    have hE3 : E≤3 := by omega
    have hML : j<M+L := by
      by_cases hML : M+L≤j
      · have hc:=hcut2 hML
        omega
      · omega
    have hQ24 : 24≤Q := by omega
    have hX12 : X≤12 := by dsimp [X,R]; omega
    exact target_square_impossible R X Q (C : Int) 10 12 24 (by decide)
      (by dsimp [R]; omega) hXlo hX12 hQ24 (by decide) hsq
  · have hcutsHead:=Recaman.ThreeHeadFreeCuts.head_free_cuts f n h M m L s U w hw hpre
      hS hA hS2 hA2 (fun k hk hkH=>hpos k hk (by omega))
    have hMcost : M≤r+2 := hcutsHead.1
    have hT7 : T≤7 := by omega
    have hE5 : E≤5 := by omega
    have hT6 : T≤6 := by omega
    have hX14 : X≤14 := by dsimp [X,R]; omega
    have hj9 : j=9 := by
      by_cases hj10 : 10≤j
      · have hQ40 : 40≤Q := by omega
        exact False.elim (target_square_impossible R X Q (C : Int) 11 14 40 (by decide)
          (by dsimp [R]; omega) hXlo hX14 hQ40 (by decide) hsq)
      · omega
    have hA24 : A=24 := by
      by_cases hA23 : A≤23
      · exact False.elim (target_square_impossible R X Q (C : Int) 10 13 36 (by decide)
          (by dsimp [R]; omega) hXlo (by dsimp [X,R]; omega) (by omega) (by decide) hsq)
      · omega
    have hEhead10 : cN (EndN f 0) n H=10 := by omega
    have hQ46 : Q≤46 := by
      have hR10 : R=10 := by dsimp [R]; omega
      have hXeq : X=14 := by dsimp [X,R]; omega
      rw [hR10,hXeq] at hsq
      have hCsq:=Recaman.ShortCounterFactorBounds.square_lower (C : Int) 2 (by decide) (by omega)
      grind only
    have hm1 : m=1 := by
      by_cases hm2 : 2≤m
      · have ha := Int.mul_nonneg (show 0≤N by dsimp [N]; omega) (show 0≤(v : Int)-1 by omega)
        have hb := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-3 by omega)
        have hc := Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
        have hQstrong : N+3*(M : Int)+(L : Int)≤Q := by dsimp [Q]; grind only
        omega
      · omega
    have hh : 1≤h := by
      by_cases hz : h=0
      · have ha : f n=true := by simpa only [hz,Nat.add_zero] using hA 0 hM
        have hp:=hpos 1 (by omega) (by omega)
        have hs0 : cN (fun x=>f x=false) n 1=0 := by simp [cN,ha]
        omega
      · omega
    have hhead9 : cN (EndN f 0) n H≤9 :=
      Recaman.LongFirstMiddleOne.head_middle_one_long_first_nine f n h M m L s U w hw hpre
        hh (by omega) hL hs hU hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega)) hm1
    omega

end Recaman.FourHighGapExcluded
