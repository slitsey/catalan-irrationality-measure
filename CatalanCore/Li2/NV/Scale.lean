module

public import CatalanCore.Content.HalfIntDet

@[expose] public section

open scoped BigOperators

namespace CatalanCore.Li2.NV

/-- A nonsingular integral reduction prevents the original scaled determinant
from vanishing. The scale identity is the existing content determinant lemma. -/
theorem det_ne_zero_of_scaled_reduction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (G : Matrix ι ι ℚ)
    (Z : Matrix ι ι (CatalanCore.Basic.LocRing ℓ)) (C : ℕ) (ex ey : ι → ℕ)
    (hscale : ∀ i j, (ℓ : ℚ)^C * G i j =
      (ℓ : ℚ)^(ex i) * (Z i j : ℚ) * (ℓ : ℚ)^(ey j))
    (hred : ((CatalanCore.Arith.Hybrid.redQ ℓ).mapMatrix Z).det ≠ 0) : G.det ≠ 0 := by
  have hdet : CatalanCore.Arith.Hybrid.redQ ℓ Z.det ≠ 0 := by
    simpa only [RingHom.map_det] using hred
  have hZq : (Z.det : ℚ) ≠ 0 := by
    intro h0
    apply hdet
    have hZ : Z.det = 0 := Subtype.ext h0
    rw [hZ, map_zero]
  intro hG
  have hs := CatalanCore.Content.det_scale G Z C ex ey hscale
  rw [hG, mul_zero] at hs
  have hl : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  exact mul_ne_zero (pow_ne_zero _ hl) hZq hs.symm

end CatalanCore.Li2.NV
