import Recaman.DoubleDefectCounter
import Recaman.DoubleDefectSupport
import Recaman.UnitDefectCost
import Recaman.OldSourceKeyOrder

namespace Recaman.DoubleDefectActualFive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

private theorem count_shift (P : Nat → Prop) (s : Nat) : ∀ K,
    cN P s K=cN (fun i=>P (s+i)) 0 K
  | 0 => rfl
  | K+1 => by
    classical
    have ih:=count_shift P s K
    by_cases hp : P (s+K) <;> simp [cN,ih,hp]

/-- Old clocks0/1 belong to the same0..2 support as four local families.
They are counted in that union, rather than charged as an extra old clock. -/
theorem double_defect_actual_five (f : Nat → Bool) (n t h M m L s U v T j μ : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hμ : 1≤μ) (hv : v=μ+2)
    (hheadMass : M+L+U=h+m+s+μ)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hC : mass (w.drop t)=1)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤5 ∧ μ≤2 ∧
      cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)≤3 := by
  have hb:=Recaman.DoubleDefectCounter.double_defect_counter f n t h M m L s U v T j μ w hw hpre ht
    hh hM hm hL hs hU hμ hv hheadMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let Q:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  let A:=sourceAt false s (List.replicate U true++List.replicate v false)
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hzeq : z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true := hword
  have hmz : mass z=(μ : Int) := by rw [hzeq]; simp only [mass_append,mass_rep_false,mass_replicate_A]; omega
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hu1 : w.drop t=[true] := block_mass_one hu hC
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hsupport:=Recaman.DoubleDefectSupport.double_defect_local_support h M m L s U v j (by omega)
    (by have he:=hb.2.1; omega) hM hb.2.2
    (by rw [←hzeq,hmz]; omega)
    (by simpa only [hu1,hzeq,hb.1,List.append_assoc] using hp.1)
    (by simpa only [hu1,hzeq,hb.1,List.append_assoc] using hp.2)
  have hlast : cN (EndN f 0) (n+H+v) T≤5 := by
    rw [count_shift]
    have hmono : cN (fun i=>EndN f 0 (n+H+v+i)) 0 T≤cN (fun i=>i≤2 ∨ Q i ∨ A i) 0 T := by
      apply cN_mono
      intro i _ hi he
      obtain ⟨ha,r,l,hr,hel,hwseed⟩:=he
      by_cases hrold : r<n
      · have hord:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t (H+v) i T j
          (by rw [hpre]; exact hw) hrold ht (by omega) (by have he:=hb.2.1; omega)
          (by simpa only [H,Nat.add_assoc] using hA4)
          (by simpa only [H,Nat.add_assoc] using hgap)
          (by rw [show n+(H+v)+i-r=l by omega]; exact hwseed)
          (by simpa only [H,Nat.add_assoc] using htarget)
        exact Or.inl (by have he:=hb.1; omega)
      · have hen : EndN f n (n+H+v+i) := ⟨ha,r,l,by omega,hel,hwseed⟩
        have hlocal:= (localSupply_seg_iff f n (n+H+v+i) (by omega) ha).mpr hen
        have hraw : seg f n (H+v+i)=z++List.replicate v false++List.replicate i true := by
          rw [seg_add,seg_add,show seg f n H=z by rfl,
            seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
          congr 1
          apply seg_A
          intro x hx hxi
          have he:=hA4 (x-(n+H+v)) (by omega)
          rw [show n+h+M+m+L+s+U+v+(x-(n+H+v))=x by dsimp [H]; omega] at he
          exact he
        rw [show n+H+v+i-n=H+v+i by omega,hraw,hzeq] at hlocal
        exact hsupport i (by simpa only [List.append_assoc] using hlocal)
    have h3:=Recaman.DoubleDefectSupport.three_clock_count T
    have hQ:=sourceAt_count_le_one true L _ T
    have hA:=sourceAt_count_le_one false s _ T
    have ho1:=cN_or_le (fun i=>i≤2) (fun i=>Q i ∨ A i) T
    have ho2:=cN_or_le Q A T
    change cN (sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)) 0 T≤1 at hQ
    change cN (sourceAt false s (List.replicate U true++List.replicate v false)) 0 T≤1 at hA
    change cN Q 0 T≤1 at hQ
    change cN A 0 T≤1 at hA
    omega
  have hc1:=cN_add P n H v
  have hc2:=cN_add P n (H+v) T
  have hc3:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hc3
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hc3
  change cN P n (H+v+T)<j+1 at hbad
  simp only [Nat.add_assoc] at hc1 hc2 hc3 hlast hbad
  have hfree3 : cN P n H≤3 := by have he:=hb.1; omega
  have hf:=Recaman.UnitDefectCost.mass_free_charge f n H (hpos H (by dsimp [H]; omega) (by dsimp [H]; omega))
  change mass z+1≤(cN P n H : Int) at hf
  rw [hmz] at hf
  refine ⟨by simpa only [H,Nat.add_assoc] using hlast,by omega,?_⟩
  simpa only [H,P] using hfree3

end Recaman.DoubleDefectActualFive
