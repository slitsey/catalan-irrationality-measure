module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

/-!
# Lipschitz bound for Chebyshev polynomials on `[-1, 1]` (G32b)

`|T_k x - T_k c| ≤ k² |x - c|` for `|x|, |c| ≤ 1`, and the finite trial sum
`∑ d_k T_{k+1}(x)/(k+1)` is Lipschitz with constant `∑ |d_k| (k+1)`.  Used to pass from the cell
centre to the cell in the `τ = 1` residual check (`F₁ - 2 T(du, ·)`).
-/

namespace CatalanMeasure.GenD.Cert.TrialLip
open Real Polynomial

theorem abs_sin_nat_mul_le (n : ℕ) (a : ℝ) : |Real.sin (n * a)| ≤ n * |Real.sin a| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Real.sin (((n + 1 : ℕ) : ℝ) * a) = Real.sin (n * a) * Real.cos a + Real.cos (n * a) * Real.sin a := by
      rw [← Real.sin_add]; congr 1; push_cast; ring
    rw [h]
    calc |Real.sin (n * a) * Real.cos a + Real.cos (n * a) * Real.sin a|
        ≤ |Real.sin (n * a) * Real.cos a| + |Real.cos (n * a) * Real.sin a| := abs_add_le _ _
      _ ≤ n * |Real.sin a| + |Real.sin a| := by
        rw [abs_mul, abs_mul]
        have h1 : |Real.cos a| ≤ 1 := Real.abs_cos_le_one a
        have h2 : |Real.cos (n * a)| ≤ 1 := Real.abs_cos_le_one _
        have h3 := abs_nonneg (Real.sin a)
        have h4 : |Real.sin (n * a)| * |Real.cos a| ≤ n * |Real.sin a| * 1 := by
          calc |Real.sin (n * a)| * |Real.cos a| ≤ (n * |Real.sin a|) * 1 :=
                mul_le_mul ih h1 (abs_nonneg _) (by positivity)
            _ = _ := by ring
        nlinarith [mul_le_mul_of_nonneg_right h2 h3]
      _ = ((n + 1 : ℕ) : ℝ) * |Real.sin a| := by push_cast; ring

theorem T_lip (k : ℕ) {x c : ℝ} (hx : |x| ≤ 1) (hc : |c| ≤ 1) :
    |(Chebyshev.T ℝ (k : ℤ)).eval x - (Chebyshev.T ℝ (k : ℤ)).eval c| ≤ (k : ℝ) ^ 2 * |x - c| := by
  have hx' := abs_le.mp hx
  have hc' := abs_le.mp hc
  set θ := Real.arccos x
  set φ := Real.arccos c
  have ex : Real.cos θ = x := Real.cos_arccos hx'.1 hx'.2
  have ec : Real.cos φ = c := Real.cos_arccos hc'.1 hc'.2
  rw [← ex, ← ec, Chebyshev.T_real_cos θ, Chebyshev.T_real_cos φ]
  rw [Real.cos_sub_cos, Real.cos_sub_cos]
  have e1 : ((k : ℤ) : ℝ) * θ + ((k : ℤ) : ℝ) * φ = 2 * ((k : ℝ) * ((θ + φ) / 2)) := by push_cast; ring
  have e2 : ((k : ℤ) : ℝ) * θ - ((k : ℤ) : ℝ) * φ = 2 * ((k : ℝ) * ((θ - φ) / 2)) := by push_cast; ring
  rw [e1, e2]
  simp only [mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0), abs_mul, abs_neg]
  have h1 := abs_sin_nat_mul_le k ((θ + φ) / 2)
  have h2 := abs_sin_nat_mul_le k ((θ - φ) / 2)
  have h3 : |Real.sin ((θ + φ) / 2)| ≥ 0 := abs_nonneg _
  have h4 : |Real.sin ((θ - φ) / 2)| ≥ 0 := abs_nonneg _
  have key : |Real.sin (k * ((θ + φ) / 2))| * |Real.sin (k * ((θ - φ) / 2))| ≤
      (k * |Real.sin ((θ + φ) / 2)|) * (k * |Real.sin ((θ - φ) / 2)|) :=
    mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  nlinarith [key]

/-- the finite trial sum `∑_{k<n} d_k T_{k+1}(x)/(k+1)` -/
noncomputable def trialPoly (d : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, d k * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)

/-- **Lipschitz bound of the trial sum**, constant `∑ |d_k| (k+1)`. -/
theorem trialPoly_lip (d : ℕ → ℝ) (n : ℕ) {x c : ℝ} (hx : |x| ≤ 1) (hc : |c| ≤ 1) :
    |trialPoly d n x - trialPoly d n c| ≤ (∑ k ∈ Finset.range n, |d k| * ((k + 1 : ℕ) : ℝ)) * |x - c| := by
  unfold trialPoly
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have h := T_lip (k + 1) hx hc
  have e : d k * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ) -
      d k * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval c / ((k + 1 : ℕ) : ℝ) =
      d k / ((k + 1 : ℕ) : ℝ) * ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x - (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval c) := by
    ring
  rw [e, abs_mul, abs_div, abs_of_pos hk]
  calc |d k| / ((k + 1 : ℕ) : ℝ) * |(Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x - (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval c|
      ≤ |d k| / ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) ^ 2 * |x - c|) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = |d k| * ((k + 1 : ℕ) : ℝ) * |x - c| := by field_simp

end CatalanMeasure.GenD.Cert.TrialLip
#print axioms CatalanMeasure.GenD.Cert.TrialLip.T_lip
#print axioms CatalanMeasure.GenD.Cert.TrialLip.trialPoly_lip
