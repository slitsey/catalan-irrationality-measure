module

public import CatalanArchive.CatalanLambda.Mirror.Growth
public import CatalanArchive.CatalanLambda.GrowthFinal

@[expose] public section

/-!
# Mirror constant: `log D_h ≤ (313/105 + ε) h²` eventually, via the PNT in progressions mod 4.
-/

open Filter

namespace CatalanLambda.Mirror

/-- The growth bound for the mirror denominator constant. -/
theorem log_Dden_le_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, Real.log (Dden h) ≤ (313 / 105 + ε) * (h : ℝ) ^ 2 :=
  growth_of_theta CatalanLambda.th_upper hε

end CatalanLambda.Mirror
