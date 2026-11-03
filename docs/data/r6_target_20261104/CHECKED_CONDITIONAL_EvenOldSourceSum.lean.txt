import Recaman.OldThreeKeyParity
import Recaman.ShortCounterFactorBounds

namespace Recaman.EvenOldSourceSum

theorem even_source_sum (R E ku ks Z : Int) (hR : 5≤R) (hE : E≤18) (heven : R%2=0)
    (hku : ku= -2 ∨ ku=0) (hks : ks= -2 ∨ ks=0 ∨ ks=2)
    (hseed : ks=2*E-2+4*Z) (hdiff : ku-ks=4*E+2-2*R^2) :
    R=6 ∧ ((E=17 ∧ ku= -2 ∧ ks=0) ∨ (E=18 ∧ ku=0 ∧ ks= -2)) := by
  have hR6 : R≤6 := by
    by_cases h6 : R≤6
    · exact h6
    have hs:=Recaman.ShortCounterFactorBounds.square_lower R 7 (by omega) (by omega)
    rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
  have hr6 : R=6 := by omega
  rw [hr6] at hdiff
  have hsum : E=17 ∨ E=18 := by
    rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
  refine ⟨hr6,?_⟩
  rcases hsum with h17|h18
  · have hs0 : ks=0 := by rcases hks with hks|hks|hks <;> omega
    exact Or.inl ⟨h17,by omega,hs0⟩
  · exact Or.inr ⟨h18,by rcases hku with hku|hku <;> omega,by rcases hku with hku|hku <;> omega⟩

/-- The two even-R sum branches lie strictly between explicit consecutive squares. -/
theorem sum_nonsquare (S v K ku : Int) (hv : v=3 ∨ v=4)
    (hsum : (S+v=17 ∧ ku= -2) ∨ (S+v=18 ∧ ku=0))
    (hkey : ku=2*S^2-4*K-8*(S+v)+2*v^2-72) :
    ∃ a : Nat, (a : Int)^2<2*K+1 ∧ 2*K+1<((a : Int)+1)^2 := by
  rcases hv with h3|h4
  · rcases hsum with ⟨h17,hku⟩|⟨h18,hku⟩
    · have hS : S=14 := by omega
      rw [hS,h3,hku] at hkey
      exact ⟨10,by omega,by omega⟩
    · have hS : S=15 := by omega
      rw [hS,h3,hku] at hkey
      exact ⟨11,by omega,by omega⟩
  · rcases hsum with ⟨h17,hku⟩|⟨h18,hku⟩
    · have hS : S=13 := by omega
      rw [hS,h4,hku] at hkey
      exact ⟨9,by omega,by omega⟩
    · have hS : S=14 := by omega
      rw [hS,h4,hku] at hkey
      exact ⟨10,by omega,by omega⟩

end Recaman.EvenOldSourceSum
