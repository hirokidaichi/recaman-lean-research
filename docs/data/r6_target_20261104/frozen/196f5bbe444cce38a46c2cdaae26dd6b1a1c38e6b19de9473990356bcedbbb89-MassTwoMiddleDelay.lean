import Recaman.MassTwoMiddleSource

namespace Recaman.MassTwoMiddleDelay

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Equal source delay i+j-T=0 gives a zero-mass bridge for every i, without changing either actual window. -/
theorem equal_delay_bridge (f : Nat → Bool) (t z b i j : Nat) (htz : t≤z) (hzb : z≤b)
    (hA : ∀ k, k<i+j → f (b+k)=true)
    (hS : ∀ x, b+(i+j)≤x → x<b+(i+j)+j → f x=false)
    (hlocal : Win f z (b+i-z)) (htarget : Win f t (b+(i+j)+j-t)) :
    mass (seg f t (z-t))=0 ∧ runKey (seg f t (z-t))=2-2*((j : Int)+1)^2 := by
  let P:=seg f t (z-t)
  let V:=seg f z (b-z)
  have hAword (K : Nat) (hK : K≤i+j) : seg f b K=List.replicate K true := by
    apply seg_A
    intro x hx hxB
    have ha:=hA (x-b) (by omega)
    rw [Nat.add_sub_cancel' hx] at ha
    exact ha
  have hlword : seg f z (b+i-z)=V++List.replicate i true := by
    rw [show b+i-z=(b-z)+i by omega,seg_add,show z+(b-z)=b by omega,hAword i (by omega)]
  have hlm : mass (V++List.replicate i true)=1 := by
    rw [←hlword,seg_mass]
    have hx:=hlocal.2.1
    rw [show z+(b+i-z)=b+i by omega] at hx ⊢
    omega
  have hla : areaW (V++List.replicate i true)=0 := by rw [←hlword,←Ar_areaW]; exact hlocal.2.2
  have hVkey:=Recaman.ASourceReuse.source_key_before_gap V i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hlm)
    (by simpa only [List.replicate_zero,List.append_nil] using hla)
  have hword : seg f t (b+(i+j)+j-t)=P++V++List.replicate (i+j) true++List.replicate j false := by
    rw [show b+(i+j)+j-t=(b+(i+j)-t)+j by omega,seg_add,
      show t+(b+(i+j)-t)=b+(i+j) by omega,seg_false f (b+(i+j)) j hS,
      show b+(i+j)-t=(b-t)+(i+j) by omega,seg_add,show t+(b-t)=b by omega,hAword (i+j) (by omega),
      show b-t=(z-t)+(b-z) by omega,seg_add,show t+(z-t)=z by omega]
  have hmfull : mass (P++V++List.replicate (i+j) true++List.replicate j false)=1 := by
    rw [←hword,seg_mass]
    have hx:=htarget.2.1
    rw [show t+(b+(i+j)+j-t)=b+(i+j)+j by omega] at hx ⊢
    omega
  have hafull : areaW (P++V++List.replicate (i+j) true++List.replicate j false)=0 := by rw [←hword,←Ar_areaW]; exact htarget.2.2
  have hPmass : mass P=0 := by
    simp only [mass_append,mass_replicate_A,mass_rep_false,Int.natCast_add] at hmfull hlm
    omega
  have hkey:=Recaman.ASourceReuse.source_key_before_gap (P++V) (i+j) j hmfull hafull
  rw [runKey_append,hPmass,hVkey] at hkey
  exact ⟨hPmass,by simpa only [Int.zero_mul,Int.add_zero] using (show runKey P=2-2*((j : Int)+1)^2 by omega)⟩

theorem middle_delay_excluded (f : Nat → Bool) (n t h M m z b i j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n) (hC : mass (w.drop t)=2)
    (hj : 2≤j) (hM : M=j+2) (hz : n+h+M≤z) (hzm : z<n+h+M+m) (hzb : z≤b)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hAend : ∀ k, k<i+j → f (b+k)=true)
    (hSend : ∀ x, b+(i+j)≤x → x<b+(i+j)+j → f x=false)
    (htarget : Win f t (b+(i+j)+j-t)) : ¬Win f z (b+i-z) := by
  intro hlocal
  have hb:=equal_delay_bridge f t z b i j (by omega) hzb hAend hSend hlocal htarget
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

end Recaman.MassTwoMiddleDelay
