module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Analytic layer (group 4): interval-cover principle for circle certificates

Generic form of `Parametric.TwentyCircle.twentyCircleCovers_spec`: a finite list of rational
pieces `(lo, hi, rt)` with `sqrt((r+s)^2-1) <= rt` on each piece certifies
`(r+s+sqrt((r+s)^2-1))^m * (2(r^2+1)-s^2)^e * r^f <= K` on `[c, r+1]`.  The radius `r`, the exponents
`m, e, f` (`m = d0`) and the constant `K` are instance data; the endpoint inequality
at `s = r+1` is an explicit hypothesis (it is a `norm_num` at the instance).
-/

namespace CatalanMeasure.GenD
namespace Analytic

noncomputable section

def circlePieceOK (r K : ℚ) (m e f : ℕ) (p : ℚ × ℚ × ℚ) : Bool :=
  decide (0 ≤ p.1) && decide (p.1 ≤ p.2.1) && decide (p.2.1 ≤ r + 1) &&
  decide (0 ≤ p.2.2) && decide ((r + p.2.1) ^ 2 - 1 ≤ p.2.2 ^ 2) &&
  decide ((r + p.2.1 + p.2.2) ^ m * (2 * (r ^ 2 + 1) - p.1 ^ 2) ^ e * r ^ f ≤ K)

def circleCovers (r K : ℚ) (m e f : ℕ) : ℚ → List (ℚ × ℚ × ℚ) → Bool
  | c, [] => decide (c = r + 1)
  | c, p :: l => decide (p.1 = c) && circlePieceOK r K m e f p && circleCovers r K m e f p.2.1 l

theorem circleCovers_spec {r K : ℚ} {m e f : ℕ} (hr0 : 0 ≤ r)
    (hend : ((r : ℝ) + (r + 1) + Real.sqrt (((r : ℝ) + (r + 1)) ^ 2 - 1)) ^ m *
      (2 * ((r : ℝ) ^ 2 + 1) - (r + 1) ^ 2) ^ e * (r : ℝ) ^ f ≤ (K : ℝ))
    {c : ℚ} {l : List (ℚ × ℚ × ℚ)} (h : circleCovers r K m e f c l = true) {s : ℝ}
    (hs : (c : ℝ) ≤ s) (hs2 : s ≤ (r : ℝ) + 1) :
    ((r : ℝ) + s + Real.sqrt (((r : ℝ) + s) ^ 2 - 1)) ^ m *
      (2 * ((r : ℝ) ^ 2 + 1) - s ^ 2) ^ e * (r : ℝ) ^ f ≤ (K : ℝ) := by
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  induction l generalizing c with
  | nil =>
    simp only [circleCovers, decide_eq_true_eq] at h
    subst h
    have he : s = (r : ℝ) + 1 := by
      push_cast at hs
      linarith
    rw [he]
    exact hend
  | cons p l ih =>
    simp only [circleCovers, circlePieceOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, ⟨⟨⟨⟨⟨h0, h01⟩, h12⟩, hu0⟩, hu⟩, hK⟩⟩, hrest⟩ := h
    subst hc
    by_cases hs1 : s ≤ p.2.1
    · have hs0 : 0 ≤ s := le_trans (by exact_mod_cast h0) hs
      have hp0 : (0 : ℝ) ≤ p.1 := by exact_mod_cast h0
      have hsq : Real.sqrt (((r : ℝ) + s) ^ 2 - 1) ≤ p.2.2 := by
        rw [Real.sqrt_le_left (by exact_mod_cast hu0)]
        have hh : ((r : ℝ) + (p.2.1 : ℝ)) ^ 2 - 1 ≤ (p.2.2 : ℝ) ^ 2 := by exact_mod_cast hu
        nlinarith
      have hA : (r : ℝ) + s + Real.sqrt (((r : ℝ) + s) ^ 2 - 1) ≤ (r : ℝ) + p.2.1 + p.2.2 := by
        linarith
      have hss : s ^ 2 ≤ ((r : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hs0 hs2 2
      have hB : (2 * ((r : ℝ) ^ 2 + 1) - s ^ 2) ^ e ≤ (2 * ((r : ℝ) ^ 2 + 1) - (p.1 : ℝ) ^ 2) ^ e := by
        apply pow_le_pow_left₀
        · nlinarith only [hss, sq_nonneg ((r : ℝ) - 1)]
        · nlinarith
      have hK' : ((r : ℝ) + (p.2.1 : ℝ) + p.2.2) ^ m *
          (2 * ((r : ℝ) ^ 2 + 1) - (p.1 : ℝ) ^ 2) ^ e * (r : ℝ) ^ f ≤ (K : ℝ) := by
        exact_mod_cast hK
      calc _ ≤ ((r : ℝ) + (p.2.1 : ℝ) + p.2.2) ^ m *
          (2 * ((r : ℝ) ^ 2 + 1) - (p.1 : ℝ) ^ 2) ^ e * (r : ℝ) ^ f := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul
            · exact pow_le_pow_left₀ (by positivity) hA m
            · exact hB
            · exact pow_nonneg (by nlinarith only [hss, sq_nonneg ((r : ℝ) - 1)]) e
            · have hp1 : (0 : ℝ) ≤ p.2.1 := le_trans hs0 hs1
              have hp2 : (0 : ℝ) ≤ p.2.2 := by exact_mod_cast hu0
              positivity
        _ ≤ (K : ℝ) := hK'
    · exact ih hrest (le_of_lt (not_le.mp hs1))

end

end Analytic
end CatalanMeasure.GenD
