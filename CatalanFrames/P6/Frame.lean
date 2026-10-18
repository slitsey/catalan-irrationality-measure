module

public import CatalanCore.Frame.Spec

/-!
# The P6 frame (WP9)

`P6 = L(2, χ₋₃) / 4` as a Loewner frame: `F(z) = ψ(z+1) + 2ψ(z+1/3) - 3ψ(z+1/2)`, i.e.
`μ = ![1, 1/3, 1/2]`, `w = ![1, 2, -3]`, `norm = 36`.  The constant identity is in
`CatalanFrames.P6.Const`.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.P6

/-- The frame of `L(2,χ₋₃)/4`. -/
def p6Frame : Frame where
  d := 3
  μ := ![1, 1 / 3, 1 / 2]
  w := ![1, 2, -3]
  norm := 36
  xs := 3 / 4
  δ0 := 1 / 4
  n0off := 1
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  hw := by simp [Fin.sum_univ_three]
  hnorm := by norm_num

/-- `Delta k = 1/k + 6/(3k-2) - 6/(2k-1)` for `k ≥ 1`. -/
theorem Delta_eq (k : ℕ) (hk : 1 ≤ k) :
    p6Frame.Delta k = 1 / (k : ℚ) + 6 / (3 * (k : ℚ) - 2) - 6 / (2 * (k : ℚ) - 1) := by
  have : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have e : p6Frame.Delta k = ∑ i : Fin 3, ((![1, 2, -3] i : ℤ) : ℚ) /
      ((k : ℚ) - 1 + ![1, 1 / 3, 1 / 2] i) := rfl
  rw [e, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  have h1 : (k : ℚ) - 1 + 1 = k := by ring
  have h2 : (k : ℚ) - 1 + 1 / 3 = (3 * k - 2) / 3 := by ring
  have h3 : (k : ℚ) - 1 + 1 / 2 = (2 * k - 1) / 2 := by ring
  have n1 : (3 * (k : ℚ) - 2) ≠ 0 := by intro h; linarith
  have n2 : (2 * (k : ℚ) - 1) ≠ 0 := by intro h; linarith
  have n0 : (k : ℚ) ≠ 0 := by intro h; linarith
  rw [h1, h2, h3]
  field_simp
  ring

/-- `Dsq k = 1/k² + 18/(3k-2)² - 12/(2k-1)²` for `k ≥ 1`. -/
theorem Dsq_eq (k : ℕ) (hk : 1 ≤ k) :
    p6Frame.Dsq k = 1 / (k : ℚ) ^ 2 + 18 / (3 * (k : ℚ) - 2) ^ 2 - 12 / (2 * (k : ℚ) - 1) ^ 2 := by
  have : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have e : p6Frame.Dsq k = ∑ i : Fin 3, ((![1, 2, -3] i : ℤ) : ℚ) /
      ((k : ℚ) - 1 + ![1, 1 / 3, 1 / 2] i) ^ 2 := rfl
  rw [e, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  have h1 : (k : ℚ) - 1 + 1 = k := by ring
  have h2 : (k : ℚ) - 1 + 1 / 3 = (3 * k - 2) / 3 := by ring
  have h3 : (k : ℚ) - 1 + 1 / 2 = (2 * k - 1) / 2 := by ring
  have n1 : (3 * (k : ℚ) - 2) ≠ 0 := by intro h; linarith
  have n2 : (2 * (k : ℚ) - 1) ≠ 0 := by intro h; linarith
  have n0 : (k : ℚ) ≠ 0 := by intro h; linarith
  rw [h1, h2, h3]
  field_simp
  ring

end CatalanFrames.P6
