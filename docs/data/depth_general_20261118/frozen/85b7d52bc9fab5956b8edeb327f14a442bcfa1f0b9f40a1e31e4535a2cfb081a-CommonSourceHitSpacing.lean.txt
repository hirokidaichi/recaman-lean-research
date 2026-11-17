import Recaman.SameSourceLowCrossings
import Recaman.SFinalWindowLength

namespace Recaman.CommonSourceHitSpacing

open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction Recaman.LeadingRunSupply
open Recaman.SameSourceLowCrossings
open Recaman.ShortPeriodicSupply (sign)

private theorem source_window_phase (f : Nat → Bool) (t k : Nat)
    (h : Win f t k) : k%4=3 := by
  let e : Int → Bool := fun x => f x.toNat
  let v := past e ((t+k : Nat) : Int) k
  have hb := past_bridge e 0 t k
  simp only [Int.zero_add,e,Int.toNat_natCast] at hb
  change mass v=Fw f (t+k)-Fw f t ∧ moment v=Ar f t k at hb
  have hP : P2 v := ⟨by rw [hb.1,h.2.1]; omega,hb.2.trans h.2.2⟩
  have hp := p2_count_identities v hP
  have hl : v.length=k := by simp [v,past]
  rw [hl] at hp
  omega

/-- One unchanged source cannot have two hits less than eight clocks
apart when its first hit is an actual A. Other source alternatives remain. -/
theorem common_source_hit_gap (f : Nat → Bool) (s p q : Nat)
    (hsp : s≤p) (hpq : p<q) (hA : f p=true)
    (hp : Win f s (p-s)) (hq : Win f s (q-s)) : p+8≤q := by
  obtain ⟨r,hsr,hrq,hrH,hrA,hrOrder⟩ :=
    ordered_low_predecessor f s q (Fw f s-1) (by omega) hq (by omega) (by omega)
  have hpr : p<r := hrOrder p hsp hpq hp
  have hHp := hp.2.1
  have hHq := hq.2.1
  rw [Nat.add_sub_cancel' hsp] at hHp
  rw [Nat.add_sub_cancel' (show s≤q by omega)] at hHq
  have hstep : Fw f (p+1)=Fw f p+1 := by
    simpa [hA,sign] using Fw_succ f p
  have hdown := cN_walk f (p+1) (r-(p+1))
  rw [Nat.add_sub_cancel' (show p+1≤r by omega)] at hdown
  have hup := cN_walk f r (q-r)
  rw [Nat.add_sub_cancel' (show r≤q by omega)] at hup
  have hphasep := source_window_phase f s (p-s) hp
  have hphaseq := source_window_phase f s (q-s) hq
  omega

end Recaman.CommonSourceHitSpacing
