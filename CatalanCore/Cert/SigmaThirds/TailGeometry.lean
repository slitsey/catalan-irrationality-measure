module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Elementary geometry for the thirds hybrid certificate

These lemmas depend only on the support rectangle and fixed contour geometry.
They import no numerical certificate or frame instance.
-/

namespace CatalanCore.Cert.SigmaThirds

/-- The support rectangle `[-1,1] × [-3/2,3/2]` lies in the radius-two disk. -/
theorem rectangle_norm_le_two (x y : ℝ)
    (hx0 : -(1 : ℝ) ≤ x) (hx1 : x ≤ 1)
    (hy0 : -(3 / 2 : ℝ) ≤ y) (hy1 : y ≤ 3 / 2) :
    ‖(⟨x, y⟩ : ℂ)‖ ≤ 2 := by
  have hx : x ^ 2 ≤ (1 : ℝ) ^ 2 := sq_le_sq' hx0 hx1
  have hy : y ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := sq_le_sq' hy0 hy1
  have hs : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change x * x + y * y = x ^ 2 + y ^ 2
    ring
  have hn : 0 ≤ ‖(⟨x, y⟩ : ℂ)‖ := norm_nonneg _
  nlinarith

/-- Regularised squared distance from the slope-`5/2` tail to the support rectangle. -/
theorem tail_distance_sq_le (x y u δ : ℝ)
    (hx0 : -(1 : ℝ) ≤ x) (hx1 : x ≤ 1)
    (hy0 : -(3 / 2 : ℝ) ≤ y) (hy1 : y ≤ 3 / 2)
    (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    (-(7 / 50 : ℝ) + δ - u - x) ^ 2 + (5 / 2 * u - y) ^ 2 +
      (1 / 4096 : ℝ) ^ 2 ≤ 25 * u ^ 2 := by
  have hδ0 : |δ| ≤ 1 / 100 := hδ.trans (by norm_num)
  have hδ' := abs_le.mp hδ0
  have ha : (-(7 / 50 : ℝ) + δ - u - x) ^ 2 ≤ (u + 23 / 20) ^ 2 :=
    sq_le_sq' (by linarith [hδ'.1, hδ'.2]) (by linarith [hδ'.1, hδ'.2])
  have hb : (5 / 2 * u - y) ^ 2 ≤ (5 / 2 * u + 3 / 2) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu)]

end CatalanCore.Cert.SigmaThirds

#print axioms CatalanCore.Cert.SigmaThirds.rectangle_norm_le_two
#print axioms CatalanCore.Cert.SigmaThirds.tail_distance_sq_le