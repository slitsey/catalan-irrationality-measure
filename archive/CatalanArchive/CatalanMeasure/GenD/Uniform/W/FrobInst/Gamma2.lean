module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.Gamma
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Polynomial Polynomial.Chebyshev OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W Matrix
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem gyH_e0 : gyH p 2 0 (Pi.single 0 1) = (X ^ 2 - 1 : (ZMod p)[X]) := by
  rw [gyH_apply]
  simp [Fin.sum_univ_two, Pi.single_apply]
  ring

theorem tyH_e0 : tyH p 2 0 (Pi.single 0 1) = (X - 1 : (ZMod p)[X]) := by
  rw [tyH_apply]
  simp [Fin.sum_univ_two, Pi.single_apply]

theorem gyH_e1 : gyH p 2 0 (Pi.single 1 1) = (X - 1) * (1 + X) * (2 * X - 1 : (ZMod p)[X]) := by
  rw [gyH_apply]
  simp [Fin.sum_univ_two, Pi.single_apply]

theorem tyH_e1 : tyH p 2 0 (Pi.single 1 1) = (X - 1) * (2 * X + 1 : (ZMod p)[X]) := by
  rw [tyH_apply]
  simp [Fin.sum_univ_two, Pi.single_apply]

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
