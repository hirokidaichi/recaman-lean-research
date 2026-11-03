import Recaman.MassTwoPrefixKey
import Recaman.MassTwoShortSources

namespace Recaman.MassTwoMiddleSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Same actual windows at clock0 and after equal A/S lengths force a zero-mass square-key bridge. -/
theorem zero_clock_bridge (f : Nat → Bool) (t z b j : Nat) (htz : t≤z) (hzb : z≤b)
    (hA : ∀ k, k<j → f (b+k)=true)
    (hS : ∀ x, b+j≤x → x<b+j+j → f x=false)
    (hlocal : Win f z (b-z)) (htarget : Win f t (b+j+j-t)) :
    mass (seg f t (z-t))=0 ∧ runKey (seg f t (z-t))=2-2*((j : Int)+1)^2 := by
  let P:=seg f t (z-t)
  let V:=seg f z (b-z)
  have hmV : mass V=1 := by
    dsimp [V]
    rw [seg_mass]
    have hx:=hlocal.2.1
    rw [show z+(b-z)=b by omega] at hx ⊢
    omega
  have haV : areaW V=0 := by dsimp [V]; rw [←Ar_areaW]; exact hlocal.2.2
  have hVkey : runKey V= -2 := by unfold runKey; rw [hmV,haV]; decide
  have hword : seg f t (b+j+j-t)=P++V++List.replicate j true++List.replicate j false := by
    have hAj : seg f b j=List.replicate j true := by
      apply seg_A
      intro x hx hxB
      have hh:=hA (x-b) (by omega)
      rw [Nat.add_sub_cancel' hx] at hh
      exact hh
    rw [show b+j+j-t=(b+j-t)+j by omega,seg_add,show t+(b+j-t)=b+j by omega,seg_false f (b+j) j hS,
      show b+j-t=(b-t)+j by omega,seg_add,show t+(b-t)=b by omega,hAj,
      show b-t=(z-t)+(b-z) by omega,seg_add,show t+(z-t)=z by omega]
  have hmfull : mass (P++V++List.replicate j true++List.replicate j false)=1 := by
    rw [←hword,seg_mass]
    have hh:=htarget.2.1
    rw [show t+(b+j+j-t)=b+j+j by omega] at hh ⊢
    omega
  have hafull : areaW (P++V++List.replicate j true++List.replicate j false)=0 := by
    rw [←hword,←Ar_areaW]
    exact htarget.2.2
  have hPmass : mass P=0 := by
    simp only [mass_append,mass_replicate_A,mass_rep_false,hmV] at hmfull
    omega
  have hkey:=Recaman.ASourceReuse.source_key_before_gap (P++V) j j hmfull hafull
  rw [runKey_append,hPmass,hVkey] at hkey
  exact ⟨hPmass,by simpa only [Int.zero_mul,Int.add_zero] using (show runKey P=2-2*((j : Int)+1)^2 by omega)⟩

/-- A middle-S clock0 source is incompatible with the same mass2 old target and M=R+1. -/
theorem middle_actual_excluded (f : Nat → Bool) (n t h M m z b j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n) (hC : mass (w.drop t)=2)
    (hj : 2≤j) (hM : M=j+2) (hz : n+h+M≤z) (hzm : z<n+h+M+m) (hzb : z≤b)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hAend : ∀ k, k<j → f (b+k)=true)
    (hSend : ∀ x, b+j≤x → x<b+j+j → f x=false)
    (htarget : Win f t (b+j+j-t)) : ¬Win f z (b-z) := by
  intro hlocal
  have hb:=zero_clock_bridge f t z b j (by omega) hzb hAend hSend hlocal htarget
  let p:=z-(n+h+M)
  have hword : seg f n (z-n)=List.replicate h false++List.replicate M true++List.replicate p false := by
    have hAword : seg f (n+h) M=List.replicate M true := by
      apply seg_A
      intro x hx hxB
      have hh:=hA (x-(n+h)) (by omega)
      rw [Nat.add_sub_cancel' hx] at hh
      exact hh
    have hPword : seg f (n+h+M) p=List.replicate p false := by
      apply seg_false
      intro x hx hxB
      exact hS2 x hx (by dsimp [p] at hxB; omega)
    rw [show z-n=(h+M)+p by dsimp [p]; omega,seg_add,
      show n+(h+M)=n+h+M by omega,hPword,seg_add,seg_false f n h hS,hAword]
  have hd:=seg_drop f 0 n t (by omega)
  simp only [Nat.zero_add,hpre] at hd
  have hpword : seg f t (z-t)=w.drop t++(List.replicate h false++List.replicate M true++List.replicate p false) := by
    rw [show z-t=(n-t)+(z-n) by omega,seg_add,show t+(n-t)=n by omega,hword,←hd]
  have hu : BlockWord (w.drop t):=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  rw [hpword] at hb
  exact Recaman.MassTwoPrefixKey.middle_prefix_key_excluded (w.drop t) hu h M p hC (by omega) hb.1
    (by simpa only [show (M : Int)-1=(j : Int)+1 by omega] using hb.2)

end Recaman.MassTwoMiddleSource
