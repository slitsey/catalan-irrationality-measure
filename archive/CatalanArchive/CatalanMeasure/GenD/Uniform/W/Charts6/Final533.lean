module
public import CatalanMeasure.GenD.Uniform.W.Charts5.Final
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0145.Top
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0135.Top
public import CatalanArchive.CatalanMeasure.GenD.Uniform.W.Charts6.L0179.Top
public import CatalanMeasure.GenD.Uniform.Bank532.Final533
@[expose] public section
set_option Elab.async false

/-!
# `μ(G) ≤ 533`, unconditional

`Hosts533` has the four fields `Pk.L0145_k280_47.Phys`, `Pk.L0146_k152_25.Phys` (G8e), `Pk.L0179_k89_8.Phys`, `Pk.L0135_left.Phys`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.Bank532

theorem hosts533 : Hosts533 :=
  ⟨L0145.physHost_145, CatalanMeasure.GenD.Uniform.W.Charts5.physHost_pilot, L0179.physHost_179,
    L0135.physHost_135⟩

/-- **`μ(G) ≤ 533`.** -/
theorem catalan_irrationalityMeasure_533 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(533 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  catalan_irrationalityMeasure_533_of_hosts hosts533

end CatalanMeasure.GenD.Uniform.W.Charts6

#print axioms CatalanMeasure.GenD.Uniform.W.Charts6.catalan_irrationalityMeasure_533
