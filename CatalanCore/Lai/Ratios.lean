module

public import CatalanCore.Lai.Roots
public import CatalanCore.Measure.Mobius

@[expose] public section

/-!
# `CatalanCore.Lai.Ratios`: every ratio of two points of the plane of `ζ(3)` and `π⁴`

`lai_mobius_of`: for integers `a, b, c, d` with `a d - b c ≠ 0`,
`q ^ (-55.50) < |(a ζ(3) + b π⁴)/(c ζ(3) + d π⁴) - p/q|` for all `p` and all large `q`.
The number is the image of `ζ(3)/ζ(4)` under the integer Möbius map `(a, 90 b; c, 90 d)`, and the
ratio root `lai_ratio_family_of` (`μ' = 55.499`) transfers by `plain_measure_mobius`.

Say μ, never B, for the irrationality measure.
-/

open Filter Topology CatalanCore.Measure

namespace CatalanCore.Lai

/-- **Ratios of points of the plane**, `μ = 55.50`. -/
theorem lai_mobius_of (h : LaiInputs) (a b c d : ℤ) (hdet : a * d - b * c ≠ 0) :
    ∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(55.50 : ℝ)) <
        |((a : ℝ) * zeta3 + (b : ℝ) * Real.pi ^ 4) / ((c : ℝ) * zeta3 + (d : ℝ) * Real.pi ^ 4)
          - (p : ℝ) / q| := by
  have hdet' : a * (90 * d) - 90 * b * c ≠ 0 := by
    intro h0; apply hdet; linarith
  have hm := plain_measure_mobius (x := zeta3 / zeta4) (μ' := 55.499) (μ := 55.50)
    (by norm_num) (by norm_num) a (90 * b) c (90 * d) hdet' (lai_ratio_family_of h)
  have hz : zeta4 ≠ 0 := by rw [zeta4_eq_pi]; positivity
  have hp : Real.pi ^ 4 = 90 * zeta4 := by rw [zeta4_eq_pi]; ring
  have n1 : (a : ℝ) * (zeta3 / zeta4) + ((90 * b : ℤ) : ℝ)
      = ((a : ℝ) * zeta3 + (b : ℝ) * Real.pi ^ 4) / zeta4 := by
    rw [hp]; push_cast; field_simp
  have n2 : (c : ℝ) * (zeta3 / zeta4) + ((90 * d : ℤ) : ℝ)
      = ((c : ℝ) * zeta3 + (d : ℝ) * Real.pi ^ 4) / zeta4 := by
    rw [hp]; push_cast; field_simp
  rw [n1, n2, div_div_div_cancel_right₀ hz] at hm
  exact hm

end CatalanCore.Lai

#print axioms CatalanCore.Lai.lai_mobius_of
