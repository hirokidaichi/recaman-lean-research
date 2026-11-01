import Recaman.PhaseSearch

namespace Recaman

/-- The four-component lexicographic order used by phase search is
transitive. -/
theorem natQuadLex_trans
    {x y z : Nat × (Nat × (Nat × Nat))}
    (hxy : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) x y)
    (hyz : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) y z) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) x z := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  rcases z with ⟨za, zb⟩
  cases hxy with
  | left _ _ hleftXY =>
      cases hyz with
      | left _ _ hleftYZ =>
          exact Prod.Lex.left _ _ (Nat.lt_trans hleftXY hleftYZ)
      | right _ _ =>
          exact Prod.Lex.left _ _ hleftXY
  | right _ hrightXY =>
      cases hyz with
      | left _ _ hleftYZ =>
          exact Prod.Lex.left _ _ hleftYZ
      | right _ hrightYZ =>
          exact Prod.Lex.right _
            (natTripleLex_trans hrightXY hrightYZ)

/-- Phase-search progress composes, allowing local mechanisms to expose an
intermediate semantic node without losing the global rank decrease. -/
theorem PhaseSearchProgress.trans {m : Nat}
    {x y z : PhaseSearchNode}
    (hxy : PhaseSearchProgress m x y)
    (hyz : PhaseSearchProgress m y z) :
    PhaseSearchProgress m x z := by
  exact natQuadLex_trans hxy hyz

end Recaman
