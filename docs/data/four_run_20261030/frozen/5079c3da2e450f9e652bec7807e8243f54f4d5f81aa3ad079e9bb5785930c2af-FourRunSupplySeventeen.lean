import Recaman.AdjacentRunSupply

namespace Recaman.FourRunSupplySeventeen

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.ThreeRunSupplyBudget Recaman.SeparatorSupplyReset Recaman.AdjacentRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc:=cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- The genuine first A run and actual relative positivity supply h>=1;
then the first three rays cost10, and fourth local6 plus old1 cost7. -/
theorem four_run_supply_le_seventeen (f : Nat → Bool) (n h M m L s U v T : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+U+v+T)≤17 := by
  let B := h+M+m+L+s+U
  let D := B+v
  let rs : List (Bool × Nat) :=
    [(false,h),(true,M),(false,m),(true,L),(false,s),(true,U),(false,v)]
  have hh : 1≤h := by
    by_cases hh0 : h=0
    · have hAt : f n=true := by simpa only [hh0,Nat.add_zero] using hA 0 hM
      have hSz : cN (fun x=>f x=false) n 1=0 := by simp [cN,hAt]
      have hp:=hpos 1 (by omega) (by omega)
      rw [hSz] at hp
      omega
    · omega
  have h3 := Recaman.InitialSTargetBounds.three_run_count_of_manyS
    f n h M m L s U w hw hpre hs (by omega)
    hS hA hS2 hA2 hS3 hA3 (fun k hk hkB => hpos k hk (by omega))
  have hword : seg f n B=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true :=
    three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hshape : seg f 0 (n+D)=w++runWord rs := by
    rw [show n+D=n+(B+v) by rfl,seg_add,Nat.zero_add,hpre,
      seg_add,show n+B=n+h+M+m+L+s+U by omega,
      seg_false f (n+h+M+m+L+s+U) v hS4]
    change w++(seg f n B++List.replicate v false)=w++runWord rs
    rw [hword]
    simp [rs,runWord,List.append_assoc]
  have hcnt : 3≤cntF (runWord rs) := by
    simp only [rs,runWord,cntF_append,cntF_replicate_S,cntF_A,
      List.append_nil,Nat.add_zero]
    omega
  have hA4' : ∀ i, i<T → f (n+D+i)=true := by
    intro i hi
    simpa only [D,B,Nat.add_assoc] using hA4 i hi
  have he4 := endable_A_run_count f (n+D) T (w++runWord rs) hshape hA4'
  have hb := block_rayCount_append hw (runWord rs) hcnt T
  have hl : rayCount (runWord rs) T≤6 := by
    have hl0:=fourth_ray_local_le_six h M m L s U v T hv
    simpa only [rs,runWord,List.append_nil,List.append_assoc] using hl0
  have h4 : cN (EndN f 0) (n+D) T≤7 := by omega
  have hSzero : cN (EndN f 0) (n+B) v=0 := by
    apply cN_zero_of
    intro x hx hxv he
    have hf := hS4 x (by omega) (by omega)
    have ht := he.1
    rw [hf] at ht
    contradiction
  have hc1 := cN_add (EndN f 0) n B v
  have hc2 := cN_add (EndN f 0) n D T
  change cN (EndN f 0) n (D+T)≤17
  change cN (EndN f 0) n B≤10 at h3
  dsimp only [D] at hc2 h4 ⊢
  omega

end Recaman.FourRunSupplySeventeen
