import Recaman.RunClockClassifier
import Recaman.InitialSTargetBounds

namespace Recaman.HeadUnitPairSupply

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The first-A and middle-S sources cannot meet the third-ray key
when both separators are unit length. The initial S still costs one. -/
theorem third_unit_pair_local (h M L U : Nat) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate 1 false++
      List.replicate L true++List.replicate 1 false) U≤2 := by
  let x:=List.replicate M true++List.replicate 1 false++List.replicate L true++List.replicate 1 false
  have only_two (i : Nat) (hi : Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate i true)=true) :
      i=2 := by
    have hc:=Recaman.RunClockClassifier.thirdClock_sound 0 M 1 L 1 i (by omega)
      (by simpa only [x,List.replicate_zero,List.nil_append,List.append_assoc] using hi)
    simp only [Recaman.RunClockClassifier.thirdClock,decide_eq_true_eq] at hc
    rcases hc with he|⟨hq,hq0,_⟩|⟨_,_,heq⟩|⟨hv,hv1,hkey⟩
    · exact he
    · omega
    · have hf : 2*((1 : Int)+1+1-(L : Int)-(i : Int))*((1 : Int)+1)+2*(L : Int)*1=3 := by
        simpa using heq
      omega
    · have he : (i : Int)+(L : Int)-1-1=1 := by omega
      change ((i : Int)+(L : Int)-1-1+1)^2=2*(L : Int)*1+1 at hkey
      rw [he] at hkey
      have hf : (4 : Int)=2*(L : Int)+1 := by simpa using hkey
      omega
  have hx : rayCount x U≤1 := by
    unfold rayCount
    apply cN_le_one_of_unique
    intro i _ k _ hi hk
    exact (only_two i hi).trans (only_two k hk).symm
  have hb:=rayCount_const_append false h x U
  have he : rayCount (List.replicate h false++x) U≤2 := by omega
  simpa only [x,List.append_assoc] using he

theorem head_unit_pair_eight (f : Nat → Bool) (n h M L U : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hh : 1≤h)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+1 → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+1+i)=true)
    (hS3 : ∀ x, n+h+M+1+L≤x → x<n+h+M+1+L+1 → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+1+L+1+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+1+L+1+U → cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    cN (EndN f 0) n (h+M+1+L+1+U)≤8 := by
  let B:=h+M+1+L
  let y:=List.replicate h false++List.replicate M true++List.replicate 1 false++
    List.replicate L true++List.replicate 1 false
  have hp:=Recaman.ThreeRunSupplyBudget.two_run_supply_of_positive f n h M 1 L w hw hpre
    hS hA hS2 hA2 (fun hb=>hpos _ hb (by omega))
  change cN (EndN f 0) n B≤5 at hp
  have hword : seg f n (B+1)=y := by
    have he:=Recaman.SeparatorSupplyReset.three_run_word f n h M 1 L 1 0
      hS hA hS2 hA2 hS3 (by intro i hi; omega)
    simpa only [B,y,Nat.add_zero,List.replicate_zero,List.append_nil] using he
  have hbase : seg f 0 (n+(B+1))=w++y := by rw [seg_add,Nat.zero_add,hpre,hword]
  have hcnt (k : Nat) : cntF (List.replicate k true)=0 := by
    have he:=mass_cntF (List.replicate k true)
    rw [mass_replicate_A,List.length_replicate] at he
    omega
  have hs : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,hcnt,Nat.add_zero]
    omega
  have hr:=block_rayCount_append hw y hs U
  have hl : rayCount y U≤2 := third_unit_pair_local h M L U
  have he:=endable_A_run_count f (n+(B+1)) U _ hbase
    (by simpa only [B,Nat.add_assoc] using hA3)
  have hzero : cN (EndN f 0) (n+B) 1=0 := by
    apply cN_zero_of
    intro x hx hx1 ex
    have ha:=ex.1
    rw [hS3 x (by dsimp [B] at hx; omega) (by dsimp [B] at hx1; omega)] at ha
    contradiction
  have h1:=cN_add (EndN f 0) n B 1
  have h2:=cN_add (EndN f 0) n (B+1) U
  have h : cN (EndN f 0) n (B+1+U)≤8 := by omega
  exact h

end Recaman.HeadUnitPairSupply
