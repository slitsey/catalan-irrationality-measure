module

public import CatalanMeasure.GenD.Analytic.WeightedAtom
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Set
noncomputable section

/-! Generic soundness of the frozen finite-selector endpoint rule. This keeps
the clipped entropy interface and does not replace it by a supporting line. -/

theorem binomRate_le_log_two (κ : ℝ) : binomRate κ ≤ Real.log 2 := by
  unfold binomRate
  split_ifs
  · exact Real.binEntropy_le_log_two
  · exact le_rfl

theorem binomRate_antitone_on_unit {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    binomRate b ≤ binomRate a := by
  by_cases hhalf : 1 ≤ 2 * a
  · have hhalfb : 1 ≤ 2 * b := by linarith
    simp only [binomRate, if_pos hhalf, if_pos hhalfb]
    exact Real.binEntropy_strictAntiOn.antitoneOn
      (by constructor <;> norm_num <;> linarith)
      (by constructor <;> norm_num <;> linarith) hab
  · simp only [binomRate, if_neg hhalf]
    exact binomRate_le_log_two b

theorem affine_circle_selector_cell {r shift n C lo hi U Ψ : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hn : 0 ≤ n)
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hU : (shift - n * hi) * Real.log r + C ≤ U)
    (hΨ : U + n * binomRate lo ≤ Ψ) :
    ∀ κ ∈ Icc lo hi,
      (shift - n * κ) * Real.log r + C + n * binomRate κ ≤ Ψ := by
  intro κ hκ
  have hlog := Real.log_nonpos hr0.le hr1
  have hcoeff : shift - n * hi ≤ shift - n * κ := by
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hκ.2 hn) shift
  have hcircle := (mul_le_mul_of_nonpos_right hcoeff hlog)
  have hentropy := mul_le_mul_of_nonneg_left
    (binomRate_antitone_on_unit hlo hκ.1 (hκ.2.trans hhi)) hn
  linarith

theorem finite_affine_circle_selector {ι : Type*} (lo hi U : ι → ℝ)
    {r shift n C Ψ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hn : 0 ≤ n)
    (hcover : ∀ κ ∈ Icc (0 : ℝ) 1, ∃ i, κ ∈ Icc (lo i) (hi i))
    (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hU : ∀ i, (shift - n * hi i) * Real.log r + C ≤ U i)
    (hΨ : ∀ i, U i + n * binomRate (lo i) ≤ Ψ) :
    ∀ κ ∈ Icc (0 : ℝ) 1,
      (shift - n * κ) * Real.log r + C + n * binomRate κ ≤ Ψ := by
  intro κ hκ
  obtain ⟨i, hiκ⟩ := hcover κ hκ
  exact affine_circle_selector_cell hr0 hr1 hn (hlo i) (hhi i) (hU i) (hΨ i) κ hiκ

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.binomRate_le_log_two
#print axioms CatalanMeasure.GenD.Analytic.binomRate_antitone_on_unit
#print axioms CatalanMeasure.GenD.Analytic.affine_circle_selector_cell
#print axioms CatalanMeasure.GenD.Analytic.finite_affine_circle_selector
