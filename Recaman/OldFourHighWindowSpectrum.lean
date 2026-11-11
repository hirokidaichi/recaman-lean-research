import Recaman.DepthSixOldFour

namespace Recaman.OldFourHighWindowSpectrum

open Recaman.DepthSixOldFour Recaman.SFinalWindowLength
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- Old-source gap-four counters allow only source windows of length
three, or length seven at offset two with no high free addition. Every
witness is extracted from the actual supplier on the original history. -/
theorem old_four_high_source_spectrum (f : Nat → Bool) (n a b t q : Nat) (d : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (htn : t<n) (hwin : Win f t (b+4-t))
    (hnq : n≤q) (hqb : q<b) (hd : 2≤d)
    (hq : Fw f q=Fw f n-2+d+1) (hqe : EndN f 0 q) :
    ∃ u, n≤u ∧ u<q ∧ Fw f u=Fw f n-2+d ∧ Win f u (q-u) ∧
      ((q-u=3 ∧ d≤6 ∧
        2*d+5*(cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n) : Int)≤13) ∨
       (q-u=7 ∧ d=2 ∧ cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n)=0)) := by
  obtain ⟨u,hnu,huq,hu,hWin,hCost⟩ := old_four_actual_high_source f n a b t q d hw hpre
    hnb hfloor hpos hS he hcounter htn hwin hnq hqb hd hq hqe
  have hk := win_ge3 f u (q-u) hWin
  have hmul := Int.mul_nonneg (show 0≤d-2 by omega) (show 0≤((q-u : Nat) : Int)-1 by omega)
  have hpoly : (d-2)*(((q-u : Nat) : Int)-1)=
      d*(((q-u : Nat) : Int)-1)-2*(((q-u : Nat) : Int)-1) := by grind only
  rw [hpoly] at hmul
  refine ⟨u,hnu,huq,hu,hWin,?_⟩
  rcases window_three_or_at_least_seven f u (q-u) hWin with h3 | h7
  · left
    rw [h3] at hCost
    exact ⟨h3,by omega,by omega⟩
  · right
    have hLen : q-u=7 := by omega
    rw [hLen] at hCost
    exact ⟨hLen,by omega,by omega⟩

end Recaman.OldFourHighWindowSpectrum
