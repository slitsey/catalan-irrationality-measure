module

public import CatalanMeasure.GenD.TwoAdic

@[expose] public section

/-!
# Parity: the generic 2-adic constant at P20 is `21/200` (instance file)
-/

namespace CatalanMeasure.GenD
namespace Parity

open CatalanMeasure.Parametric

noncomputable section

theorem a2_p20 : TwoAdic.a2 ⟨20, 3, 1, 2, 1⟩ = 21 / 200 := by
  have hH : (⟨20, 3, 1, 2, 1⟩ : Parameters).H 1 = 27 := by
    simp [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
      Parameters.g, Parameters.h]
  unfold TwoAdic.a2 TwoAdic.A2
  rw [hH]
  norm_num

end
end Parity
end CatalanMeasure.GenD
