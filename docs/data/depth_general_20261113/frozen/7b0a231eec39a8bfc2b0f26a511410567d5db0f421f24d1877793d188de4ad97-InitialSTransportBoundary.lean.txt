import Recaman.InitialSLowTargetTransport
import Recaman.InitialSPaddingPositive

namespace Recaman.InitialSTransportBoundary

open Recaman.InitialSLowTargetTransport Recaman.InitialSPaddingPositive Recaman.AdditionRankSlack
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality

private def sharpF : Nat → Bool := finiteSign [false,true,true,true]
private def marginF : Nat → Bool := finiteSign [false,true]

/-- The height-one source cutoff is sharp: at relative height two the
removed last S may be the original SAA supplier. -/
theorem ceiling_two_changes_original_supply :
    (∀ i, i<1 → sharpF i=false) ∧ Fw sharpF 3=Fw sharpF 1+2 ∧
    EndN sharpF 0 3 ∧ ¬EndN (fun i => sharpF (1+i)) 0 2 := by
  refine ⟨?_,by decide,⟨by decide,0,3,by omega,by omega,?_⟩,?_⟩
  · intro i hi
    have hh : i=0 := by omega
    subst i
    decide
  · unfold Win
    decide
  · intro he
    have hl := (localSupply_seg_iff (fun i => sharpF (1+i)) 0 2 (by omega) (by decide)).mpr he
    have hn : Recaman.ThreeNonsuppliedData.localSupply
        (seg (fun i => sharpF (1+i)) 0 (2-0))=false := by decide
    rw [hn] at hl
    cases hl

private theorem before_three (f : Nat → Bool) (b : Nat) (hb : b<3) : ¬EndN f 0 b := by
  rintro ⟨_,t,k,_,htk,hWin⟩
  have hk := win_ge3 f t k hWin
  omega

/-- Exact free-count transport does not preserve strict positive
actual deficit: deleting S from SA leaves one free A and deficit zero. -/
theorem preserved_free_does_not_preserve_positive_deficit :
    (∀ k, 0<k → k≤2 → cN (EndN marginF 0) 0 k+1≤cN (fun i => marginF i=false) 0 k) ∧
    (∀ i, 1≤i → i<2 → marginF i=true → Fw marginF i≤Fw marginF 1+1) ∧
    free marginF 0 2=free (fun i => marginF (1+i)) 0 1 ∧
    ¬(cN (EndN (fun i => marginF (1+i)) 0) 0 1+1≤
      cN (fun i => marginF (1+i)=false) 0 1) := by
  have hS : ∀ i, i<1 → marginF i=false := by
    intro i hi
    have hh : i=0 := by omega
    subst i
    decide
  have hCeil : ∀ i, 1≤i → i<2 → marginF i=true → Fw marginF i≤Fw marginF 1+1 := by
    intro i hi hj _
    have hh : i=1 := by omega
    subst i
    decide
  have hE : cN (EndN marginF 0) 0 2=0 := by
    apply cN_zero_of
    intro i _ hi
    exact before_three marginF i (by omega)
  have hgE : cN (EndN (fun i => marginF (1+i)) 0) 0 1=0 := by
    apply cN_zero_of
    intro i _ hi
    exact before_three (fun i => marginF (1+i)) i (by omega)
  have hgS : cN (fun i => marginF (1+i)=false) 0 1=0 := by
    simp [cN,marginF,finiteSign]
  have hcounts := initial_S_low_addition_counts marginF 1 1 hS hCeil
  refine ⟨?_,hCeil,hcounts.2.1,by omega⟩
  intro k hk hk2
  have he := count_prefix_le (EndN marginF 0) 0 k 2 hk2
  have hs := count_prefix_le (fun i => marginF i=false) 0 1 k (by omega)
  have hs1 : cN (fun i => marginF i=false) 0 1=1 := by simp [cN,marginF,finiteSign]
  omega

end Recaman.InitialSTransportBoundary
