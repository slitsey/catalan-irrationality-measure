module

public import CatalanArchive.CatalanMeasure.Parametric.TwentyParameters
public import CatalanMeasure.GenD.OddProfile

@[expose] public section

/-!
# P20 = (20,3,1,2,1) as an instance of the generic layer (numerals only)

`design` is the existing `Parametric.twenty` (kept: the C3 certificate `TwentyBase` is stated for it).
-/

namespace CatalanMeasure.GenD
namespace P20

open CatalanMeasure.Parametric

noncomputable section

abbrev design : Parameters := Parametric.twenty

theorem design_admissible : Admissible design := twenty_admissible

theorem design_H (N : ℕ) : design.H N = 27 * N := twenty_H N

theorem design_L (N : ℕ) : design.L N = 24 * N := by
  simp only [Parameters.L, Parameters.n, Parameters.b, Parameters.q, design, twenty]
  omega

theorem design_A (N : ℕ) : design.A N = 8 * N := twenty_A N

end
end P20
end CatalanMeasure.GenD
