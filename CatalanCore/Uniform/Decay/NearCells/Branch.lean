module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

/-!
# Splitting the principal logarithm of a product (lane D, package D6b)

`Log (a b) = Log a + Log b` when `Re b > 0` and `Im a`, `Im (a b)` have the same (weak) sign.
This is the branch bookkeeping for expanding `Log (1 - ζ₀ - e s)` about `s = 0`.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Complex

private theorem log_split_aux {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ≠ 0)
    (hbr : 0 < b.re) (hlo : -(3 * Real.pi / 2) < arg a + arg b - arg (a * b))
    (hhi : arg a + arg b - arg (a * b) < 3 * Real.pi / 2) :
    log (a * b) = log a + log b := by
  have h : exp (log a + log b - log (a * b)) = 1 := by
    rw [exp_sub, exp_add, exp_log ha, exp_log hb, exp_log hab, div_self hab]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have him := congrArg Complex.im hn
  simp only [Complex.sub_im, Complex.add_im, Complex.log_im, Complex.mul_im, Complex.natCast_re,
    Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
    Complex.im_ofNat, mul_zero, zero_mul, add_zero, sub_zero, mul_one] at him
  have hpi := Real.pi_pos
  have hre : (2 * (Real.pi : ℂ)).re = 2 * Real.pi := by simp
  rw [hre] at him
  have hn0 : n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
      nlinarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      nlinarith
  subst hn0
  simp only [Int.cast_zero, zero_mul, Complex.zero_im] at him
  have : log a + log b - log (a * b) = 0 := by
    have hn' : log a + log b - log (a * b) = (0 : ℤ) * (2 * Real.pi * I) := by simpa using hn
    simpa using hn'
  exact (sub_eq_zero.1 this).symm

/-- Branch splitting, upper half plane version. -/
theorem log_mul_of_im_nonneg {a b : ℂ} (ha : a ≠ 0) (hb : 0 < b.re) (h1 : 0 ≤ a.im)
    (h2 : 0 ≤ (a * b).im) : log (a * b) = log a + log b := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hab : a * b ≠ 0 := mul_ne_zero ha hb0
  have hpi := Real.pi_pos
  have h1' := Complex.arg_nonneg_iff.2 h1
  have h2' := Complex.arg_nonneg_iff.2 h2
  have hba : |arg b| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hb)
  have hbl := (abs_lt.1 hba)
  have ha' := Complex.arg_le_pi a
  have h2'' := Complex.arg_le_pi (a * b)
  exact log_split_aux ha hb0 hab hb (by linarith) (by linarith)

/-- Branch splitting, lower half plane version (strict). -/
theorem log_mul_of_im_neg {a b : ℂ} (ha : a ≠ 0) (hb : 0 < b.re) (h1 : a.im < 0)
    (h2 : (a * b).im < 0) : log (a * b) = log a + log b := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hab : a * b ≠ 0 := mul_ne_zero ha hb0
  have hpi := Real.pi_pos
  have h1' := Complex.arg_neg_iff.2 h1
  have h2' := Complex.arg_neg_iff.2 h2
  have hba : |arg b| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hb)
  have hbl := (abs_lt.1 hba)
  have hA := Complex.neg_pi_lt_arg a
  have hB := Complex.neg_pi_lt_arg (a * b)
  exact log_split_aux ha hb0 hab hb (by linarith) (by linarith)

end CatalanCore.Uniform.Decay.NearCells
