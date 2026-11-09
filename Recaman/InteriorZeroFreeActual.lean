import Recaman.InteriorZeroFreeWords
import Recaman.InitialSPaddingPositive
import Recaman.AdditionRankSlack

namespace Recaman.InteriorZeroFreeActual

open Recaman.InteriorZeroFreeWords Recaman.AdditionRankSlack Recaman.LeadingRunSupply
open Recaman.BlockSuffixPositivity Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem actual_ray_end (f : Nat → Bool) (n i : Nat) (w : List Bool)
    (hpre : seg f 0 n=w) (hA : ∀ k, k≤i → f (n+k)=true)
    (hl : Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true)=true) :
    EndN f 0 (n+i) := by
  have hAseg : seg f n i=List.replicate i true := by
    apply seg_A
    intro t ht hti
    have hs:=hA (t-n) (by omega)
    rwa [Nat.add_sub_cancel' ht] at hs
  have hs:=seg_add f 0 n i
  rw [Nat.zero_add,hpre,hAseg] at hs
  apply (localSupply_seg_iff f 0 (n+i) (by omega) (hA i (by omega))).mp
  simpa only [Nat.sub_zero,hs] using hl

private theorem old_supply (d i : Nat) (hi : i<d+2) (v : List Bool) :
    tailOldRay (v++oldWord (d+1)) [false] i := by
  obtain ⟨u,hu⟩:=old_word_suffix i (d+1) (by omega)
  obtain ⟨hl,hm,hk⟩:=old_word_profile i
  rw [hu,← List.append_assoc]
  refine ⟨(v++u).length,by simp; omega,?_,?_⟩ <;>
    rw [List.drop_left,hm] <;> try rw [hk]
  · rw [show mass [false]= -1 by decide]
    omega
  · rw [show runKey [false]= -2 by decide,show cntF [false]=1 by decide]
    omega

/-- Every addition of the designated interior run is supplied by the
original prefix. Its entire mixed interval has zero actual free additions. -/
theorem interior_free_zero (f : Nat → Bool) (n d : Nat) (v : List Bool)
    (hpre : seg f 0 n=v++oldWord (d+1))
    (hword : seg f n (interiorWord d).length=interiorWord d) :
    free f n (interiorWord d).length=0 := by
  let a:=d+2
  let s:=2*d+1
  let K:=(interiorWord d).length
  have hk : K=1+a+s := by simp [K,a,s,interiorWord] <;> omega
  have hW : seg f n K=([false]++List.replicate a true)++List.replicate s false := hword
  have hhead : seg f n (1+a)=[false]++List.replicate a true := by
    have ht:=seg_take f n K (1+a) (by omega)
    rw [hW,← show ([false]++List.replicate a true).length=1+a by simp [Nat.add_comm],List.take_left] at ht
    simpa only [List.length_append,List.length_singleton,List.length_replicate] using ht.symm
  have hS : seg f n 1=[false] := by
    have ht:=seg_take f n (1+a) 1 (by omega)
    rw [hhead] at ht
    simpa using ht.symm
  have hA (i : Nat) (hi : i<a) : f (n+1+i)=true := by
    have h:=seg_get f n (1+a) (1+i) (by omega)
    rw [hhead,List.getElem?_append_right (by simp),List.length_singleton,
      show 1+i-1=i by omega,List.getElem?_replicate,if_pos hi] at h
    simpa only [Nat.add_assoc] using (Option.some.inj h).symm
  have hpreS : seg f 0 (n+1)=(v++oldWord (d+1))++[false] := by
    have h:=seg_add f 0 n 1
    rwa [Nat.zero_add,hpre,hS] at h
  have hEnd (i : Nat) (hi : i<a) : EndN f 0 (n+1+i) :=
    actual_ray_end f (n+1) i _ hpreS (fun k hk=>hA k (by omega))
      ((ray_supply_append_iff _ _ i).mpr (Or.inl (old_supply d i hi v)))
  have hRun : cN (EndN f 0) (n+1) a=a := by
    rw [cN_congr (P := EndN f 0) (Q := fun t=>f t=true) (s := n+1) a
      (fun t ht hta=>⟨fun h=>h.1,fun _=>by
        have he:=hEnd (t-(n+1)) (by omega)
        rwa [Nat.add_sub_cancel' ht] at he⟩)]
    exact count_A_run f (n+1) a hA
  have hN := cN_add (EndN f 0) n 1 a
  have hTail := cN_add (EndN f 0) n (1+a) s
  rw [← hk] at hTail
  have hones:=ones_seg_eq_count f n K
  rw [hW,ones_append,ones_append,show ones [false]=0 by decide,
    ones_replicate_A,ones_replicate_S] at hones
  change 0+(a : Int)+0=(additions f n K : Int) at hones
  have hSplit:=additions_split f n K
  change free f n K=0
  omega

end Recaman.InteriorZeroFreeActual
