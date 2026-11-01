import Recaman.ShortTargetLast4
import Recaman.ShortTargetLast3
import Recaman.ShortBandArithmetic

namespace Recaman.ShortTargetBands

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- All five parameter bands follow from the original actual counter.
No band, count budget or finite-history classification is assumed. -/
theorem short_counter_five_bands (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v<C) (hvpos : 1≤v) (hC4 : 4≤C)
    (hzeroMass : M+L+U=h+m+s)
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
    (hC : mass (w.drop t)=(C : Int))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    ((v=3 ∧ C=4 ∧ j+1≤8) ∨ (v=4 ∧ C=5 ∧ j+1=5) ∨
     (v=1 ∧ C≤8 ∧ j+1≤9) ∨ (v=2 ∧ C≤7 ∧ j+1≤8) ∨ (v=3 ∧ C=5 ∧ j+1≤6)) ∧
    C≤8 ∧ v≤4 ∧ j+1≤9 ∧ h+m+s≤19 ∧ M+L+U+T≤21 := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let S:=h+m+s
  let R:=j+1
  let z:=seg f n H
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=S := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H,S] at hc ⊢
    omega
  have hT : T+C=v+R := hb.1
  have hR : 5≤R := hb.2.1
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hlo : -2≤runKey (w.drop t) := by
    have hh:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hzl:=runKey_count_lower z
  rw [hSz] at hzl
  have hkey : runKey (w.drop t)= -runKey z-4*(C : Int)*((S : Int)+(v : Int))+
      2*(v : Int)^2-2*(R : Int)^2 := by
    have hk:=hb.2.2.2
    simpa only [S,R,Int.natCast_add,Int.natCast_one] using hk
  have hK : (R : Int)^2≤(S : Int)^2-2*(C : Int)*(S : Int)+(v : Int)^2-2*(C : Int)*(v : Int)+1 := by
    grind only
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hsep : cN (EndN f 0) (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxe he
    have hf:=hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxe; omega)
    have ht:=he.1
    rw [hf] at ht
    contradiction
  have he1:=cN_add (EndN f 0) n H v
  have he2:=cN_add (EndN f 0) n (H+v) T
  have hp:=addition_endable_partition f n (H+v+T)
  have hword:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v T hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hc:=ones_seg_eq_count f n (h+M+m+L+s+U+v+T)
  rw [hword] at hc
  simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
  have hAc : cN (fun x=>f x=true) n (H+v+T)=S+T := by dsimp [H,S]; omega
  rw [hAc] at hp
  have hbound (b : Nat) (hlast : cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤b) : S≤C-v+9+b := by
    change cN (EndN f 0) n H≤10 at hhead10
    change cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (H+v+T)<R at hbad
    simp only [H,Nat.add_assoc] at he1 he2 hsep hhead10 hlast hp hbad
    dsimp [S]
    omega
  have hl4:=Recaman.ShortTargetLast4.short_counter_last_4 f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hsmall : C=v+1 → S≤14 := by
    intro heq
    have hh:=hbound 4 hl4
    omega
  have hdeep : v+2≤C → S≤C-v+12 := by
    intro heq
    have hl3:=Recaman.ShortTargetLast3.short_counter_last_3 f n t h M m L s U v T j C w hw hpre ht
      hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad heq
    have hh:=hbound 3 hl3
    omega
  have ha:=Recaman.ShortBandArithmetic.five_bands C v R S T hC4 hvpos hv hR (by dsimp [S]; omega) hT hsmall hdeep hK
  simpa only [R,S,hzeroMass] using ha

end Recaman.ShortTargetBands
