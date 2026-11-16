module

public import CatalanCore.Zeta5.Data.Design

@[expose] public section
set_option maxRecDepth 100000

/-!
# Z5-DATA, part 4: the constant inequality ZD22 at the design

`zd22Ok 6 (37/40) (3/40) (43/50) E M₀ D₀ = true` with `E = energyAux 1 cs` (`Design.Eq0`, the
energy `Σ c_k²/(2k)` of the design) and `D₀ = 138500086/10⁸`.  The design value is
`D = 1.385000860794…`.
-/

namespace CatalanCore.Zeta5.Data

open CatalanCore.Zeta5.Cells

-- kcost: three logQ (series length 6) + 60-term energy, < 0.5 s estimated (pilot `zd22Ok 6` true)
theorem zd22Ok_design :
    zd22Ok 6 (37 / 40) (3 / 40) (43 / 50) Eq0 desA.M0 (138500086 / 10 ^ 8) = true := by
  decide +kernel

noncomputable section

/-- **ZD22 at the design**, in the form `hconst_of_zd22` consumes. -/
theorem zd22_design :
    ZD22 (37 / 40) (3 / 40) (43 / 50)
      (∑ k ∈ Finset.range 60, cR (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ))) (desA.M0 : ℝ)
      (138500086 / 10 ^ 8) := by
  have h := zd22_sound zd22Ok_design
  rw [E_eq]
  push_cast at h
  exact h

end

end CatalanCore.Zeta5.Data
