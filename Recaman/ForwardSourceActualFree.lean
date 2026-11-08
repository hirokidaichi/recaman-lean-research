import Recaman.SevenPrefixSourceShape

namespace Recaman.ForwardSourceActualFree

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- An advance between the two actual primitive source clocks costs
at least two free A in the original positive prefix. The arbitrary
mixed future and old BlockWord are retained. No weighted helper is used. -/
theorem forward_pair_needs_two_actual_free (f : Nat → Bool) (n K B i j : Nat)
    (w p u : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hseg : seg f n K=p)
    (hpos : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hfull : seg f 0 B=w++p++u) (hlast : ∀ r, r≤j → f (B+r)=true)
    (hij : i<j) (hkey : runKey u= -2) (hnewkey : runKey (p++u)= -2)
    (hm : mass u+(i : Int)=1) (hn : mass (p++u)+(j : Int)=1) :
    2≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n K := by
  by_cases hf : 2≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n K
  · exact hf
  · have hr : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n K≤1 := by omega
    have hAb:=positive_r3_additions_free_bound f n 0 K hw
      (by simpa only [List.replicate_zero,List.append_nil] using hpre) hpos (by omega)
    have hones:=ones_seg_eq_count f n K
    rw [hseg] at hones
    obtain ⟨hcost,_⟩:=Recaman.MixedPrefixClockSquare.mixed_prefix_clock_square p u i j hij hkey hnewkey hm hn
    have hA3 : ones p=3 := by omega
    have hji : j=i+1 := by omega
    have hc:=cntF_int p
    have hmp:=mass_eq p
    simp only [mass_append] at hn
    have hmassp : mass p= -1 := by omega
    have hlen : p.length=7 := by omega
    have hFodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hkey
    have hF1 : 1≤cntF u := by omega
    have hkP : runKey p=4*(cntF u : Int) := by
      rw [runKey_append,hkey,hmassp] at hnewkey
      grind only
    have hkpos : 0<runKey p := by omega
    have hKl:=congrArg List.length hseg
    simp only [seg_length] at hKl
    have hK : K=7 := by omega
    have hfalse : f n=false := by
      by_cases ha : f n=true
      · have hp:=hpos 1 (by decide) (by omega)
        have hs0 : cN (fun x=>f x=false) n 1=0 := by simp [cN,ha]
        omega
      · cases he : f n <;> simp_all
    have hfirst : p.head?=some false := by
      have hsplit:=seg_add f n 1 (K-1)
      rw [show 1+(K-1)=K by omega,hseg] at hsplit
      have hone : seg f n 1=[false] := by simp [seg,hfalse]
      rw [hone] at hsplit
      rw [hsplit]
      rfl
    have hshape:=Recaman.SevenPrefixSourceShape.seven_positive_key_shape p hlen hfirst hA3 hkpos
    have hword : seg f n 7=[false,true,true,true,false,false,false] := by
      rw [hK] at hseg
      exact hseg.trans hshape
    have ht3:=seg_take f n 7 3 (by decide)
    have ht4:=seg_take f n 7 4 (by decide)
    rw [hword] at ht3 ht4
    have hseg3 : seg f n 3=[false,true,true] := by simpa using ht3.symm
    have hseg4 : seg f n 4=[false,true,true,true] := by simpa using ht4.symm
    have hg:=seg_get f n 7 3 (by decide)
    rw [hword] at hg
    have hAend : f (n+3)=true := by simpa using hg.symm
    have hlocal : Recaman.ThreeNonsuppliedData.localSupply (seg f n ((n+3)-n))=true := by
      rw [show n+3-n=3 by omega,hseg3]
      decide
    have hnend:= (localSupply_seg_iff f n (n+3) (by omega) hAend).mp hlocal
    have hend : EndN f 0 (n+3) := by
      obtain ⟨ha,t,k,hnt,htk,hW⟩:=hnend
      exact ⟨ha,t,k,by omega,htk,hW⟩
    have hE:=cN_succ_pos (EndN f 0) n 3 hend
    simp only [Nat.reduceAdd] at hE
    have hSf:=cntF_seg f n 4
    rw [hseg4] at hSf
    have hSone : cN (fun x=>f x=false) n 4=1 := by simpa [cntF] using hSf.symm
    have hp4:=hpos 4 (by decide) (by omega)
    omega

end Recaman.ForwardSourceActualFree
