module

public import CatalanCore.Uniform.Decay.PairEnergy.Atoms
public import CatalanCore.Uniform.Decay.Tools.PotentialReal

@[expose] public section

/-!
# Potential of a polynomial density on a segment, as a linear form (lane D, package D6c)

For a segment `A + t (B - A)` with Gaussian rational `A, B`, a Gaussian rational point `z` and a
rational coefficient list `g`, `potLF A B z g` is a linear form in logarithm and argument atoms
with `(potLF A B z g).val = ∫₀¹ g(t) log ‖z - (A + t (B - A))‖ dt`.  The two cases (`ζ = (z-A)/(B-A)`
non-real: complex antiderivative `Gk`; real: `Hk`) share the same formula.
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset intervalIntegral CatalanCore.Uniform.Decay.Tools

/-- Structural sum in `QC`. -/
def sumQ (f : ℕ → QC) : ℕ → QC
  | 0 => QC.zero
  | n + 1 => QC.add (sumQ f n) (f n)

theorem toC_sumQ (f : ℕ → QC) (n : ℕ) : (sumQ f n).toC = ∑ k ∈ range n, (f k).toC := by
  induction n with
  | zero => simp [sumQ]
  | succ n ih => rw [sumQ, QC.toC_add, ih, Finset.sum_range_succ]

/-- `1/(k+1)` as a rational. -/
def inv1 (k : ℕ) : ℚ := 1 / ((k : ℚ) + 1)

/-- `(1 - ζ^{k+1}) / (k+1)`. -/
def c1Q (ζ : QC) (k : ℕ) : QC := QC.qmul (inv1 k) (QC.sub QC.one (QC.pow ζ (k + 1)))
/-- `(0 - ζ^{k+1}) / (k+1)`. -/
def c0Q (ζ : QC) (k : ℕ) : QC := QC.qmul (inv1 k) (QC.neg (QC.pow ζ (k + 1)))
/-- `(1/(k+1)) Σ_{j≤k} ζ^{k-j}/(j+1)`. -/
def pQ (ζ : QC) (k : ℕ) : QC :=
  QC.qmul (inv1 k) (sumQ (fun j => QC.qmul (inv1 j) (QC.pow ζ (k - j))) (k + 1))

theorem re_Gk_diff (ζ : QC) (k : ℕ) :
    (Gk k ζ.toC 1 - Gk k ζ.toC 0).re =
      (c1Q ζ k).re * Real.log ‖(QC.sub QC.one ζ).toC‖ - (c1Q ζ k).im * Complex.arg (QC.sub QC.one ζ).toC
      - ((c0Q ζ k).re * Real.log ‖(QC.neg ζ).toC‖ - (c0Q ζ k).im * Complex.arg (QC.neg ζ).toC)
      - (pQ ζ k).re := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have e1 : (c1Q ζ k).toC = (1 - ζ.toC ^ (k + 1)) / ((k : ℂ) + 1) := by
    simp only [c1Q, inv1, QC.toC_qmul, QC.toC_sub, QC.toC_one, QC.toC_pow]
    push_cast; field_simp
  have e0 : (c0Q ζ k).toC = (0 ^ (k + 1) - ζ.toC ^ (k + 1)) / ((k : ℂ) + 1) := by
    simp only [c0Q, inv1, QC.toC_qmul, QC.toC_neg, QC.toC_pow]
    push_cast; field_simp; simp
  have eP : (pQ ζ k).toC = (1 / ((k : ℂ) + 1)) *
      ∑ j ∈ range (k + 1), ζ.toC ^ (k - j) * 1 ^ (j + 1) / ((j : ℂ) + 1) := by
    simp only [pQ, QC.toC_qmul, toC_sumQ, inv1]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [div_eq_inv_mul, QC.toC_pow]
  have key : Gk k ζ.toC 1 - Gk k ζ.toC 0 =
      (c1Q ζ k).toC * Complex.log ((QC.sub QC.one ζ).toC) - (c0Q ζ k).toC * Complex.log ((QC.neg ζ).toC)
        - (pQ ζ k).toC := by
    rw [e1, e0, eP]
    simp only [Gk, GkL, QC.toC_sub, QC.toC_one, QC.toC_neg]
    simp
    ring
  rw [key]
  simp only [Complex.sub_re, Complex.mul_re, Complex.log_re, Complex.log_im, QC.toC_re, QC.toC_im]

theorem Hk_eq_re_Gk (k : ℕ) (r t : ℝ) : Hk k r t = (Gk k (r : ℂ) (t : ℂ)).re := by
  have hc : ((t : ℂ) ^ (k + 1) - (r : ℂ) ^ (k + 1)) / ((k : ℂ) + 1)
      = (((t ^ (k + 1) - r ^ (k + 1)) / ((k : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  have hs : (1 / ((k : ℂ) + 1)) * ∑ j ∈ range (k + 1), (r : ℂ) ^ (k - j) * (t : ℂ) ^ (j + 1) / ((j : ℂ) + 1)
      = (((1 / ((k : ℝ) + 1)) * ∑ j ∈ range (k + 1), r ^ (k - j) * t ^ (j + 1) / ((j : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast; rfl
  unfold Hk Gk GkL
  simp only []
  rw [hc, hs, Complex.sub_re, Complex.re_ofReal_mul, Complex.log_re, Complex.ofReal_re,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

/-- Rational coefficient bookkeeping of `potLF`. -/
def potLF (A B z : QC) (g : List ℚ) : LF :=
  let ζ := QC.div (QC.sub z A) (QC.sub B A)
  let w1 := QC.sub QC.one ζ
  let w0 := QC.neg ζ
  let n := g.length + 1
  let gk := fun k => g.getD k 0
  ⟨-(sumR (fun k => gk k * (pQ ζ k).re) n),
    (LF.term (sumR (fun k => gk k * (c1Q ζ k).re) n) (.logC w1)).terms ++
    (LF.term (-(sumR (fun k => gk k * (c1Q ζ k).im) n)) (.argC w1)).terms ++
    (LF.term (-(sumR (fun k => gk k * (c0Q ζ k).re) n)) (.logC w0)).terms ++
    (LF.term (sumR (fun k => gk k * (c0Q ζ k).im) n) (.argC w0)).terms ++
    (LF.term (sumR (fun k => gk k * inv1 k) n) (.logC (QC.sub B A))).terms⟩

theorem comb_sums (n : ℕ) (p a b c d e : ℕ → ℝ) (X1 X2 X3 X4 X5 : ℝ) :
    (∑ k ∈ range n, p k) + ((∑ k ∈ range n, a k) * X1 + (∑ k ∈ range n, b k) * X2
      + (∑ k ∈ range n, c k) * X3 + (∑ k ∈ range n, d k) * X4 + (∑ k ∈ range n, e k) * X5)
    = ∑ k ∈ range n, (p k + a k * X1 + b k * X2 + c k * X3 + d k * X4 + e k * X5) := by
  simp only [Finset.sum_add_distrib, Finset.sum_mul]
  ring

theorem potLF_val_aux (A B z : QC) (g : List ℚ) :
    (potLF A B z g).val =
      ∑ k ∈ range (g.length + 1), ((g.getD k 0 : ℚ) : ℝ) *
        (Real.log ‖(QC.sub B A).toC‖ / ((k : ℝ) + 1) +
          (Gk k (QC.div (QC.sub z A) (QC.sub B A)).toC 1 - Gk k (QC.div (QC.sub z A) (QC.sub B A)).toC 0).re) := by
  set ζ := QC.div (QC.sub z A) (QC.sub B A) with hζ
  unfold potLF LF.val
  simp only [termsVal_append]
  have hT : ∀ q a, termsVal (LF.term q a).terms = q * a.val := by
    intro q a
    have := LF.val_term q a
    simp only [LF.val] at this
    have h0 : ((LF.term q a).c : ℝ) = 0 := by
      unfold LF.term; split_ifs <;> simp
    rw [h0, zero_add] at this
    exact this
  rw [hT, hT, hT, hT, hT]
  simp only [Atom.val, sumR_eq]
  have hre : ∀ k, (Gk k ζ.toC 1 - Gk k ζ.toC 0).re = _ := fun k => re_Gk_diff ζ k
  simp only [hre, inv1]
  push_cast
  simp only [← Finset.sum_neg_distrib]
  refine (comb_sums _ _ _ _ _ _ _ _ _ _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  push_cast
  ring

/-- **Soundness of the potential form.** -/
theorem potLF_val (A B z : QC) (g : List ℚ) (hu : (QC.sub B A).toC ≠ 0) :
    (potLF A B z g).val =
      ∫ t in (0 : ℝ)..1, evalL g t * Real.log ‖z.toC - (A.toC + (t : ℂ) * (B.toC - A.toC))‖ := by
  rw [potLF_val_aux]
  have hu' : B.toC - A.toC ≠ 0 := by simpa [QC.toC_sub] using hu
  have hζ : (QC.div (QC.sub z A) (QC.sub B A)).toC = (z.toC - A.toC) / (B.toC - A.toC) := by
    rw [QC.toC_div, QC.toC_sub, QC.toC_sub]
  have hnu : (QC.sub B A).toC = B.toC - A.toC := QC.toC_sub B A
  simp only [hζ, hnu]
  have hint : ∫ t in (0 : ℝ)..1, evalL g t * Real.log ‖z.toC - (A.toC + (t : ℂ) * (B.toC - A.toC))‖
      = ∫ t in (0 : ℝ)..1, (∑ k ∈ range (g.length + 1), ((g.getD k 0 : ℚ) : ℝ) * t ^ k) *
        Real.log ‖z.toC - (A.toC + (t : ℂ) * (B.toC - A.toC))‖ := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [evalL_eq_sum g t (g.length + 1) (by omega)]
  rw [hint]
  by_cases him : ((z.toC - A.toC) / (B.toC - A.toC)).im = 0
  · set r : ℝ := ((z.toC - A.toC) / (B.toC - A.toC)).re with hr
    have hz : (z.toC - A.toC) / (B.toC - A.toC) = (r : ℂ) := by
      apply Complex.ext <;> simp [hr, him]
    rw [segment_potential_real (fun k => ((g.getD k 0 : ℚ) : ℝ)) g.length A.toC B.toC z.toC r hu' hz]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    rw [hz, Hk_eq_re_Gk, Hk_eq_re_Gk, ← Complex.sub_re]
    simp
  · rw [segment_potential_nonreal (fun k => ((g.getD k 0 : ℚ) : ℝ)) g.length A.toC B.toC z.toC hu' him]

end CatalanCore.Uniform.Decay.PairEnergy
