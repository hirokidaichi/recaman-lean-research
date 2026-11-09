import Recaman.ShortSupplyGapBudget
import Recaman.OriginalWinHighSubtraction

namespace Recaman.OtherSupplyHeightBudget

open Recaman.ShortSupplyGapBudget Recaman.ShortSourceTriples Recaman.AdditionRankSlack
open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity Recaman.CapacityEqualityInduction
open Recaman.OriginalWinHighSubtraction

/-- An original supplying window either starts before the charged
interval or contains a subtraction at or above its endpoint height. -/
def oldOrHighSource (f : Nat → Bool) (n t : Nat) : Prop :=
  ∃ s, s≤t ∧ Win f s (t-s) ∧
    (s<n ∨ ∃ c, s≤c ∧ c<t ∧ f c=false ∧ Fw f t≤Fw f c)

theorem local_nonshort_has_high_S (f : Nat → Bool) (n s t : Nat)
    (hs : n≤s) (hst : s≤t) (hA : f t=true)
    (hW : Win f s (t-s)) (hn : ¬shortEndpoint f n t) :
    ∃ c, s≤c ∧ c<t ∧ f c=false ∧ Fw f t≤Fw f c := by
  rcases original_win_short_or_high_S f s t hst hW with hword|hh
  · have hlen:=congrArg List.length hword
    rw [seg_length] at hlen
    have h3 : t-s=3 := by simpa using hlen
    have hseg : seg f s 3=[false,true,true] := by rwa [h3] at hword
    have h0:=seg_get f s 3 0 (by decide)
    have h1:=seg_get f s 3 1 (by decide)
    have h2:=seg_get f s 3 2 (by decide)
    rw [hseg,show s+0=t-3 by omega] at h0
    rw [hseg,show s+1=t-2 by omega] at h1
    rw [hseg,show s+2=t-1 by omega] at h2
    exact (hn ⟨by omega,(Option.some.inj h0).symm,(Option.some.inj h1).symm,
      (Option.some.inj h2).symm,hA⟩).elim
  · exact hh

theorem other_supply_has_old_or_high_source (f : Nat → Bool) (n t : Nat)
    (he : EndN f 0 t) (hn : ¬shortEndpoint f n t) : oldOrHighSource f n t := by
  obtain ⟨hA,s,k,_,hk,hw⟩:=he
  have hst : s≤t := by omega
  have hk' : t-s=k := by omega
  have hW : Win f s (t-s) := by rw [hk']; exact hw
  refine ⟨s,hst,hW,?_⟩
  by_cases hs : s<n
  · exact Or.inl hs
  · exact Or.inr (local_nonshort_has_high_S f n s t (by omega) hst hA hW hn)

/-- Any counter needs enough distinct actual EndN positions with old
or high-S witnesses. Multiple witnesses at one position count once. -/
theorem counter_old_or_high_budget (f : Nat → Bool) (n a b j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hS : ∀ t, b≤t → t<b+j → f t=false) (htarget : EndN f 0 (b+j))
    (hcounter : free f n (b-n)≤j) :
    j+4≤3*cN (fun t=>EndN f 0 t ∧ oldOrHighSource f n t) n (b-n) := by
  have h:=counter_needs_other_supplies f n a b j w hw hpre hnb hS htarget hcounter
  have hc : otherSupplies f n (b-n)≤
      cN (fun t=>EndN f 0 t ∧ oldOrHighSource f n t) n (b-n) := by
    apply cN_mono
    intro t _ _ ht
    exact ⟨ht.1,other_supply_has_old_or_high_source f n t ht.1 ht.2⟩
  omega

end Recaman.OtherSupplyHeightBudget
