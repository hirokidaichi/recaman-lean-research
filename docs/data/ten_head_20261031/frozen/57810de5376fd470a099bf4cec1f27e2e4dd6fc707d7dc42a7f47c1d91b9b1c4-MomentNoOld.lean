import Recaman.MomentActualTarget

namespace Recaman.MomentNoOld

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentBandOldClock Recaman.OldSourceKeyOrder

/-- The entire last ray has no original old supplier for every
zero-mass moment-band head, not just the ten-sign two cases. Only the
proved short-last condition is used; other old masses remain unrestricted. -/
theorem actual_moment_no_old (f : Nat → Bool) (n H t v T j : Nat) (w z : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n) (hz : seg f n H=z)
    (hmz : mass z=0) (B : Int) (haz : areaW z= -B)
    (hlo : 4*(cntF z : Int)+6≤B) (hhi : B≤6*(cntF z : Int)+4)
    (hv : 1≤v) (hshort : T≤j+2) (hj : 2≤j)
    (hS : ∀ x, n+H≤x → x<n+H+v → f x=false)
    (hA : ∀ k, k<T → f (n+H+v+k)=true)
    (hgap : ∀ x, n+H+v+T≤x → x<n+H+v+T+j → f x=false)
    (htarget : Win f t (n+H+v+T+j-t)) :
    ∀ k, k<T → ∀ s, s<n → ¬Win f s (n+H+v+k-s) := by
  intro k hk s hs hwin
  have hclock:=actual_moment_band_old_clock f n (n+H) s v k w z hw hpre
    (by omega) hs (by simpa using hz) B hmz haz hlo hhi hv hS
    (fun l hl=>hA l (by omega)) hwin
  have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have horder:=actual_old_target_prior_clock f n s t (H+v) k T j hw' hs ht
    (by omega) hj (by simpa only [Nat.add_assoc] using hA)
    (by simpa only [Nat.add_assoc] using hgap)
    (by simpa only [Nat.add_assoc] using hwin)
    (by simpa only [Nat.add_assoc] using htarget)
  omega

private theorem count_shift (P : Nat → Prop) (s : Nat) : ∀ K,
    cN P s K=cN (fun i=>P (s+i)) 0 K
  | 0 => rfl
  | K+1 => by
    classical
    have ih:=count_shift P s K
    by_cases hp : P (s+K) <;> simp [cN,ih,hp]

/-- Old windows are removed only after their pointwise impossibility
has been supplied. This equality retains every local window. -/
theorem last_count_eq_local (f : Nat → Bool) (n H v T : Nat) (z : List Bool)
    (hz : seg f n H=z)
    (hS : ∀ x, n+H≤x → x<n+H+v → f x=false)
    (hA : ∀ k, k<T → f (n+H+v+k)=true)
    (hno : ∀ k, k<T → ∀ s, s<n → ¬Win f s (n+H+v+k-s)) :
    cN (EndN f 0) (n+H+v) T=rayCount (z++List.replicate v false) T := by
  rw [count_shift]
  apply cN_congr
  intro i _ hi
  have hei : EndN f 0 (n+H+v+i) ↔ EndN f n (n+H+v+i) := by
    constructor
    · rintro ⟨ha,s,l,h0s,heq,hw⟩
      have hns : n≤s := by
        by_cases hh : n≤s
        · exact hh
        · have heql : l=n+H+v+i-s := by omega
          rw [heql] at hw
          exact False.elim (hno i (by omega) s (by omega) hw)
      exact ⟨ha,s,l,hns,heq,hw⟩
    · exact end_mono f 0 n _ (Nat.zero_le _)
  have hword : seg f n (H+v+i)=z++List.replicate v false++List.replicate i true := by
    rw [seg_add,seg_add,hz,seg_false f (n+H) v hS]
    have hh : seg f (n+(H+v)) i=List.replicate i true := by
      apply seg_A
      intro x hx hxi
      have ha:=hA (x-(n+H+v)) (by omega)
      rw [show n+H+v+(x-(n+H+v))=x by omega] at ha
      exact ha
    rw [hh]
  have he:=localSupply_seg_iff f n (n+H+v+i) (by omega) (hA i (by omega))
  rw [show n+H+v+i-n=H+v+i by omega,hword] at he
  change EndN f 0 (n+H+v+i) ↔ _
  exact hei.trans he.symm


end Recaman.MomentNoOld
