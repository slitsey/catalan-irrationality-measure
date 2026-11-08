module

public import CatalanCore.Uniform.Bank.Plane2.Content
public import CatalanCore.Uniform.Bank.Plane2.PiContent

@[expose] public section

/-!
# The plane 2 theorem

For all rationals `a, b`, not both zero, `a ζ(3) + b π²` is irrational and `μ(a ζ(3) + b π²) ≤ 335.20`.
The three contents (generic datum, `ζ(3)`, `π²`) are supplied at the common value `plane2Lam`; the `π²`
content, proved at the smaller `piLam`, is weakened by monotonicity of `HasScaledContent` in `Λ`.
-/

namespace CatalanCore.Uniform.Bank.Plane2

open CatalanCore.Measure
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Shape

theorem piLam_le_plane2Lam : PiContent.piLam ≤ plane2Lam := by
  unfold plane2Lam; decide +kernel

/-- **The plane 2 theorem.** For all rationals `a, b`, not both zero, `a ζ(3) + b π²` is irrational and
`μ(a ζ(3) + b π²) ≤ 335.20`. -/
theorem plane2_measure (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    MeasureLBAt ((a : ℝ) * (riemannZeta 3).re + (b : ℝ) * Real.pi ^ 2) ((33520 / 100 : ℚ) : ℝ) ∧
      Irrational ((a : ℝ) * (riemannZeta 3).re + (b : ℝ) * Real.pi ^ 2) :=
  plane2_point_ab_of_content plane2Lam_le_max (p2_ratio_le plane2Lam_le_max) plane2Content_inst plane2ContentZeta_inst
    (hasScaledContent_mono PiContent.plane2ContentPi (by exact_mod_cast piLam_le_plane2Lam)) a b hab

end CatalanCore.Uniform.Bank.Plane2
