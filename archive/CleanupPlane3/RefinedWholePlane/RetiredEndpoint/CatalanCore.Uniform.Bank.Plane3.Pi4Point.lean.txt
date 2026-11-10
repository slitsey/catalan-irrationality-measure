module

public import CatalanCore.Uniform.Bank.Plane3.Pi4Content

@[expose] public section
set_option Elab.async false

/-! Dedicated one-term ψ″ endpoint, using full content, full jet decay and NV. -/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Measure CatalanCore.Uniform CatalanCore.Uniform.Support

-- kcost: <1s estimated, fixed rational scalar comparison.
theorem pi4_eta : pi4Lambda<Cover.Dchi.Dt := by decide +kernel
-- kcost: <1s estimated, fixed rational difference/division/comparison.
theorem pi4_ratio : Cover.Dchi.ccert/(Cover.Dchi.Dt-pi4Lambda)<75 := by decide +kernel

theorem pi4_dedicated_point :
    MeasureLBAt (Real.pi^4) (p3Cert.cr/(p3Cert.Dr-(pi4Lambda:ℝ))) ∧
      Irrational (Real.pi^4) :=
  pi4_point_of_content pi4Lambda pi4_content (by exact_mod_cast pi4_eta)

theorem pi4_dedicated_final : ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,
    (q:ℝ)^(-(75:ℝ))< |Real.pi^4-(p:ℝ)/q| := by
  exact pi4_final_of_content pi4Lambda 75 pi4_content pi4_eta pi4_ratio

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_dedicated_point
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_dedicated_final
