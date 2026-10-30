module
public import CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZLLB5
@[expose] public section
set_option Elab.async false

/-!
# `zLB`: Theorem Z at `s = 4` (G2h)

`zLB = sup (zHLB, zLLB)`: the Law_H(4) bound (no cap, and cap with `L ≤ 5p`) and the Law_L(4) bound
(cap window, any `L`).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open CatalanMeasure.Parametric
noncomputable section

/-- **Theorem Z at `s = 4`**: Law_H(4) and Law_L(4) as one nullity lower bound. -/
def zLB (P : Parameters) (hP : Admissible P) : CatalanMeasure.GenD.NullityLB P :=
  CatalanMeasure.GenD.NullityLB.sup (zHLB P hP) (zLLB P hP)

theorem zLB_ge_H {P : Parameters} (hP : Admissible P) (N p : ℕ) :
    (zHLB P hP).kap N p ≤ (zLB P hP).kap N p := by
  show _ ≤ max _ _
  exact le_max_left _ _

theorem zLB_ge_L {P : Parameters} (hP : Admissible P) (N p : ℕ) :
    (zLLB P hP).kap N p ≤ (zLB P hP).kap N p := by
  show _ ≤ max _ _
  exact le_max_right _ _

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
