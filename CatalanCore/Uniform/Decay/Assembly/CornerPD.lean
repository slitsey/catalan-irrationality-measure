module

public import CatalanCore.Uniform.Decay.Assembly.CornerFinal

@[expose] public section

/-!
# Positive definiteness constants and the corner identity for `|s u - t v|²`

`PD.of_posdef`: `A > 0`, `C > 0`, `B² < A C` give `PD A B C m K` with `m = (A C - B²)/(A + C)`,
`K = A + C + |B|`.  `boundary_energy_corner_posdef` is `boundary_energy_corner` with those data.
(Applies to the form `|s u - t v|²` of two non-parallel supporting lines: `A = |u|²`,
`B = -Re(u v̄)`, `C = |v|²`, and `B² < A C` iff `u, v` are real-linearly independent.)
-/

namespace CatalanCore.Uniform.Decay.Assembly

open CatalanCore.Uniform.Decay.Tools

theorem PD.of_posdef {A B C : ℝ} (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 < A * C) :
    PD A B C ((A * C - B ^ 2) / (A + C)) (A + C + |B|) where
  m_pos := div_pos (by linarith) (by linarith)
  lower s t := by
    set m : ℝ := (A * C - B ^ 2) / (A + C) with hm
    have hAC : 0 < A + C := by linarith
    have hm0 : 0 < m := div_pos (by linarith) hAC
    have hmeq : m * (A + C) = A * C - B ^ 2 := by rw [hm]; field_simp
    have hAm : 0 < A - m := by nlinarith
    have hprod : (A - m) * (C - m) = B ^ 2 + m ^ 2 := by nlinarith
    have key : 0 ≤ (A - m) * s ^ 2 + 2 * B * s * t + (C - m) * t ^ 2 := by
      have h1 : 0 ≤ (A - m) * ((A - m) * s ^ 2 + 2 * B * s * t + (C - m) * t ^ 2) := by
        have : (A - m) * ((A - m) * s ^ 2 + 2 * B * s * t + (C - m) * t ^ 2)
            = ((A - m) * s + B * t) ^ 2 + m ^ 2 * t ^ 2 := by
          have : (A - m) * (C - m) * t ^ 2 = (B ^ 2 + m ^ 2) * t ^ 2 := by rw [hprod]
          nlinarith [this]
        rw [this]; positivity
      exact nonneg_of_mul_nonneg_right h1 hAm
    unfold qf
    nlinarith [key]
  upper s t := by
    unfold qf
    have h1 : 2 * B * s * t ≤ |B| * (s ^ 2 + t ^ 2) := by
      have : 2 * B * s * t ≤ 2 * |B| * |s| * |t| := by
        calc 2 * B * s * t = 2 * (B * s * t) := by ring
          _ ≤ 2 * |B * s * t| := by linarith [le_abs_self (B * s * t)]
          _ = 2 * |B| * |s| * |t| := by rw [abs_mul, abs_mul]; ring
      nlinarith [sq_abs s, sq_abs t, sq_nonneg (|s| - |t|), abs_nonneg B]
    nlinarith [sq_nonneg s, sq_nonneg t, abs_nonneg B]

/-- Corner identity for a positive definite form given by `A, B, C`. -/
theorem boundary_energy_corner_posdef {A B C : ℝ} (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 < A * C)
    (i j : ℕ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    ((i : ℝ) + j + 2) * ∫ s in (0 : ℝ)..b, ∫ t in (0 : ℝ)..d, s ^ i * t ^ j * Lq A B C s t
      = (∫ t in (0 : ℝ)..d, (b ^ (i + 1) * t ^ j * Lq A B C b t
            - (0 : ℝ) ^ (i + 1) * t ^ j * Lq A B C 0 t))
        + (∫ s in (0 : ℝ)..b, (s ^ i * d ^ (j + 1) * Lq A B C s d
            - s ^ i * (0 : ℝ) ^ (j + 1) * Lq A B C s 0))
        - (b ^ (i + 1) - (0 : ℝ) ^ (i + 1)) * (d ^ (j + 1) - (0 : ℝ) ^ (j + 1))
            / (((i : ℝ) + 1) * ((j : ℝ) + 1)) :=
  boundary_energy_corner (PD.of_posdef hA hC hB) i j hb hd

end CatalanCore.Uniform.Decay.Assembly
