import Recaman.TopGapCounter
import Recaman.FourthSaturationSquare

namespace Recaman.HighGapLastSix

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem seven_square_impossible (R X tau C : Int)
    (hR : 10≤R) (hX : 0≤X) (hX16 : X≤16) (ht : tau≤3)
    (h : R^2+C^2+tau^2≤2+2*tau*X) : False := by
  have hR2 : 100≤R^2 := by
    have hp:=Int.mul_nonneg (show 0≤R-10 by omega) (show 0≤R+10 by omega)
    grind only
  have hC2:=Int.sq_nonneg C
  have ht2:=Int.sq_nonneg tau
  have hcross : tau*X≤48 := by
    have hp:=Int.mul_nonneg (show 0≤3-tau by omega) hX
    have he : (3-tau)*X=3*X-tau*X := by grind only
    rw [he] at hp
    omega
  grind only

/-- Original actual counters of gap at least nine cannot saturate
the seven-clock last-ray budget. The lower bound on head free is derived. -/
theorem high_gap_last_six (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) (hj : 9≤j) :
    let H:=h+M+m+L+s+U
    let B:=H+v
    let A:=cN (fun x=>f x=true) n (B+T)
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    2≤C ∧ 2*j+3≤A ∧ A≤j+16 ∧ T≤j+2 ∧
    cN (EndN f 0) n H≤10 ∧ 4≤cN P n H ∧ cN (EndN f 0) (n+B) T≤6 ∧
    cN (EndN f 0) n (B+T)=cN (EndN f 0) n H+cN (EndN f 0) (n+B) T ∧
    seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) := by
  dsimp only
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  have hb:=Recaman.TopGapCounter.top_gap_smaller_band f n t h M m L s U v T j C w hw hpre ht hC
    hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad
  have hC2:=hb.2.2.2.2.1
  have hFlo : F≤j := by change F<j+1 at hbad; omega
  have hAlo : 2*j+3≤A :=
    Recaman.PrimitiveOldTargetCut.actual_old_target_A_cut f n t (B+T) j w hw hpre ht (by omega)
      (by simpa only [B,H,Nat.add_assoc] using hgap)
      (by simpa only [B,H,Nat.add_assoc] using htarget)
  have hpart:=addition_endable_partition f n (B+T)
  change A=cN (EndN f 0) n (B+T)+F at hpart
  have hh : 1≤h := by
    by_cases hz : h=0
    · have ha : f n=true := by simpa only [hz,Nat.add_zero] using hA 0 hM
      have hp:=hpos 1 (by omega) (by omega)
      have hs0 : cN (fun x=>f x=false) n 1=0 := by simp [cN,ha]
      omega
    · omega
  have hhead10 : cN (EndN f 0) n H≤10 :=
    Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
      (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hlast7 : cN (EndN f 0) (n+B) T≤7 := by
    have hl:=Recaman.FourthActualSeven.fourth_actual_seven f n h M m L s U v T w hw hpre hh hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4
    simpa only [B,H,Nat.add_assoc] using hl
  have hsep : cN (EndN f 0) (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxv he
    have ha:=he.1
    rw [hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxv; omega)] at ha
    contradiction
  have hsplit : cN (EndN f 0) n (B+T)=cN (EndN f 0) n H+cN (EndN f 0) (n+B) T := by
    rw [cN_add,cN_add (EndN f 0) n H v,hsep,Nat.add_zero]
  have hEH5 : 5≤cN (EndN f 0) n H := by omega
  have hr4 : 4≤cN P n H := by
    by_cases hr : cN P n H≤3
    · have hBound:=positive_r3_additions_free_bound f n 0 H hw (by simpa using hpre)
        (fun k hk hkH=>hpos k hk (by omega)) hr
      change cN (fun x=>f x=true) n H≤2*cN P n H+1 at hBound
      have he:=addition_endable_partition f n H
      change cN (fun x=>f x=true) n H=cN (EndN f 0) n H+cN P n H at he
      omega
    · omega
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by
    simpa only [B,H,Nat.add_assoc] using hA4
  have hpT:=addition_endable_partition f (n+B) T
  rw [count_A_run f (n+B) T hA4'] at hpT
  change T=cN (EndN f 0) (n+B) T+cN P (n+B) T at hpT
  have hf := cN_add P n B T
  have hfH := cN_add P n H v
  change cN P n B=cN P n H+cN P (n+H) v at hfH
  change F=cN P n B+cN P (n+B) T at hf
  have hTband : T≤j+3 := by omega
  have hAband : A≤j+17 := by omega
  have hword : seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) := by
    have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U
      hS hA hS2 hA2 hS3 hA3
    rw [show B=H+v by rfl,seg_add,seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
    rw [show H=h+M+m+L+s+U by rfl,hhead]
    simp only [List.append_assoc]
  have hlast6 : cN (EndN f 0) (n+B) T≤6 := by
    by_cases hsix : cN (EndN f 0) (n+B) T≤6
    · exact hsix
    · exfalso
      obtain ⟨k,hk,hkey⟩:=Recaman.FourthSaturationSquare.actual_last_seven_square
        f n B t h M m L s U v T j w hw hpre ht hm hs hv hword hA4'
        (by simpa only [B,H,Nat.add_assoc] using hgap)
        (by simpa only [B,H,Nat.add_assoc] using htarget) (by omega)
      rw [hC] at hkey
      exact seven_square_impossible ((j : Int)+1) ((A : Int)-((j : Int)+1))
        ((T : Int)-(j : Int)-(k : Int)) (C : Int) (by omega) (by omega) (by omega) (by omega) hkey
  exact ⟨hC2,hAlo,by omega,by omega,hhead10,hr4,hlast6,hsplit,hword⟩

end Recaman.HighGapLastSix
