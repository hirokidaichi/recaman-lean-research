import Recaman.ThirdSResidualSquare

namespace Recaman.ThirdSSmallCircle

/-- A complete small arithmetic certificate for the residual source circle. -/
private theorem circle_certificate :
    ∀ p ∈ ([5,6,7,8,9,10,11] : List Int), ∀ R ∈ ([5,6,7,8,9,10] : List Int),
      ∀ b ∈ ([2,3,4,5,6,7,8,9,10] : List Int),
      R<p → b<p → p^2+1=R^2+b^2 →
      (p=7 ∧ R=5 ∧ b=5) ∨ (p=8 ∧ R=7 ∧ b=4) := by decide

theorem small_source_circle (p R b : Int) (hp : 5≤p) (hp' : p≤11)
    (hR : 5≤R) (hRp : R<p) (hb : 2≤b) (hbp : b<p)
    (he : p^2+1=R^2+b^2) :
    (p=7 ∧ R=5 ∧ b=5) ∨ (p=8 ∧ R=7 ∧ b=4) := by
  have memp : p∈([5,6,7,8,9,10,11] : List Int) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  have memR : R∈([5,6,7,8,9,10] : List Int) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  have memb : b∈([2,3,4,5,6,7,8,9,10] : List Int) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  exact circle_certificate p memp R memR b memb hRp hbp he

end Recaman.ThirdSSmallCircle
