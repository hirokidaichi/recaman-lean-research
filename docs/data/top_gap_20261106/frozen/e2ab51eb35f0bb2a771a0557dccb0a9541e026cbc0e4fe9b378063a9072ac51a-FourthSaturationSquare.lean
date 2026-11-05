import Recaman.InitialOldTargetSquare
import Recaman.FourthSaturationSources

namespace Recaman.FourthSaturationSquare

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSaturationSources Recaman.FourthSourceFamilies

private theorem split_initial_S (h q : Nat) (x : List Bool) (hq : q≤h) :
    List.replicate h false++x=List.replicate (h-q) false++(List.replicate q false++x) := by
  have ht : (List.replicate h false).take (h-q)=List.replicate (h-q) false := by
    rw [List.take_replicate,Nat.min_eq_left (by omega)]
  have hd : (List.replicate h false).drop (h-q)=List.replicate q false := by
    rw [List.drop_replicate,show h-(h-q)=q by omega]
  rw [←ht,←hd,←List.append_assoc,List.take_append_drop]

/-- Last-ray saturation forces the initial-S square budget at an actual
counted clock. The A count and selected target refer to the original base. -/
theorem actual_last_seven_square (f : Nat → Bool) (n B t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hword : seg f n B=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false))
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ a, n+B+T≤a → a<n+B+T+j → f a=false)
    (htarget : Win f t (n+B+T+j-t))
    (h7 : 7≤cN (EndN f 0) (n+B) T) :
    ∃ k, k<T ∧
      let R := (j : Int)+1
      let tau := (T : Int)-(j : Int)-(k : Int)
      let A := (cN (fun i=>f i=true) n (B+T) : Int)
      R^2+(mass (seg f t (n-t)))^2+tau^2≤2+2*tau*(A-R) := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true++List.replicate v false
  let y:=List.replicate h false++x
  change seg f n B=y at hword
  have hbase : seg f 0 (n+B)=w++y := by rw [seg_add,Nat.zero_add,hpre,hword]
  rw [endable_A_run_count f (n+B) T _ hbase hA] at h7
  obtain ⟨k,hk,q,hq,hqh,hmb,hkb⟩ := (fourth_seven_sources w hw h M m L s U v T hm hs hv h7).2
  let z:=List.replicate q false++x
  change mass z+(k : Int)=1 at hmb
  change runKey z= -2 at hkb
  have htword := Recaman.MomentTargetProfile.actual_target_word_profile f n t B 0 T j w y
    hpre ht hword (by intro a ha hb; omega)
    (by simpa only [Nat.add_zero] using hA)
    (by simpa only [Nat.add_zero] using hgap)
    (by simpa only [Nat.add_zero] using htarget)
  simp only [List.replicate_zero,List.append_nil] at htword
  have hy : y=List.replicate (h-q) false++z := split_initial_S h q x hqh
  rw [hy] at htword
  have hu := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hd : w.drop t=seg f t (n-t) := by
    simpa only [hpre,Nat.zero_add] using seg_drop f 0 n t (by omega)
  have he := Recaman.InitialOldTargetSquare.initial_old_target_square (w.drop t) z (h-q) k T j hu
    hmb hkb htword.1 htword.2
  dsimp only at he
  have ha := ones_seg_eq_count f n B
  have hc := cN_add (fun i=>f i=true) n B T
  have haT := count_A_run f (n+B) T hA
  rw [haT] at hc
  rw [hword,hy,ones_append,ones_replicate_S,Int.zero_add] at ha
  have hAeq : ones z+(T : Int)=(cN (fun i=>f i=true) n (B+T) : Int) := by omega
  rw [hd,hAeq] at he
  exact ⟨k,hk,he⟩

end Recaman.FourthSaturationSquare
