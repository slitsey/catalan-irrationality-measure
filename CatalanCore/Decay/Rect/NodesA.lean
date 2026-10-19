module

public import CatalanCore.Decay.Rect.Nodes

@[expose] public section

/-!
# Rectangular node sums, part 2: the energy of the node configuration [R2] (WP-H2-core)

Row nodes `xnode r b` (`b < r + m`): `b` for `b < r`, `r + 2(b - r)` for `b ≥ r`; column nodes
`ynode r b = xnode r b + [b ≥ r]`.  Scaled positions `nodeC r (·)`.

`AX_ge` : the energy `A = ∑_{a,b} elog(τ_a, τ_b)` of the row configuration is bounded below by
`r² J(m/r) - O(r log r)` where `J(x) = 3/2 + ∫_1^{1+2x} U^τ(u) du + x²(3/2 - log 2x)` (the energy of
`ν = Leb[0,1] + ½ Leb[1,1+2x]`), assembled from the legacy `NN_ge` (blocks `CC`, `XX`) and a
Riemann comparison of the cross block against the monotone function `U^τ` on `[1,∞)`.
`AY_ge` : the same for the column configuration (cost `2 m log (r+2m)`).
No Stirling beyond the legacy `log_factorial_le` is needed.
-/

open Finset MeasureTheory intervalIntegral
open CatalanLambda.Decay

namespace CatalanCore.Decay

/-- Row node numerator: `b` for `b < r`, `r + 2 (b - r)` otherwise. -/
def xnode (r b : ℕ) : ℕ := if b < r then b else r + 2 * (b - r)

/-- Column node numerator: `xnode` plus one on the extra block. -/
def ynode (r b : ℕ) : ℕ := if b < r then b else r + 2 * (b - r) + 1

lemma sum_range_xnode (r m : ℕ) (F : ℕ → ℝ) :
    ∑ b ∈ range (r + m), F (xnode r b) = ∑ b ∈ range r, F b + ∑ i ∈ range m, F (r + 2 * i) := by
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl (fun b hb => ?_)
    simp [xnode, Finset.mem_range.1 hb]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [xnode]

lemma sum_range_ynode (r m : ℕ) (F : ℕ → ℝ) :
    ∑ b ∈ range (r + m), F (ynode r b) = ∑ b ∈ range r, F b + ∑ i ∈ range m, F (r + 2 * i + 1) := by
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl (fun b hb => ?_)
    simp [ynode, Finset.mem_range.1 hb]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [ynode]

lemma sum_range_xnode2 (r m : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ a ∈ range (r + m), ∑ b ∈ range (r + m), G (xnode r a) (xnode r b)
      = (∑ a ∈ range r, ∑ b ∈ range r, G a b) + (∑ a ∈ range r, ∑ j ∈ range m, G a (r + 2 * j))
        + (∑ i ∈ range m, ∑ b ∈ range r, G (r + 2 * i) b)
        + ∑ i ∈ range m, ∑ j ∈ range m, G (r + 2 * i) (r + 2 * j) := by
  have h1 : ∀ p, ∑ b ∈ range (r + m), G p (xnode r b)
      = ∑ b ∈ range r, G p b + ∑ j ∈ range m, G p (r + 2 * j) := fun p => sum_range_xnode r m (G p)
  refine Eq.trans (sum_range_xnode r m (fun p => ∑ b ∈ range (r + m), G p (xnode r b))) ?_
  simp only [h1, Finset.sum_add_distrib]
  ring

lemma sum_range_ynode2 (r m : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ a ∈ range (r + m), ∑ b ∈ range (r + m), G (ynode r a) (ynode r b)
      = (∑ a ∈ range r, ∑ b ∈ range r, G a b) + (∑ a ∈ range r, ∑ j ∈ range m, G a (r + 2 * j + 1))
        + (∑ i ∈ range m, ∑ b ∈ range r, G (r + 2 * i + 1) b)
        + ∑ i ∈ range m, ∑ j ∈ range m, G (r + 2 * i + 1) (r + 2 * j + 1) := by
  have h1 : ∀ p, ∑ b ∈ range (r + m), G p (ynode r b)
      = ∑ b ∈ range r, G p b + ∑ j ∈ range m, G p (r + 2 * j + 1) := fun p => sum_range_ynode r m (G p)
  refine Eq.trans (sum_range_ynode r m (fun p => ∑ b ∈ range (r + m), G p (ynode r b))) ?_
  simp only [h1, Finset.sum_add_distrib]
  ring

lemma elog_real (x y : ℝ) : elog (x : ℂ) (y : ℂ) = -Real.log |x - y| := by
  unfold elog
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma sum_offdiag_range (c : ℝ) (m : ℕ) :
    ∑ i ∈ range m, ∑ j ∈ range m, (if i = j then (0 : ℝ) else c) = m * (m - 1) * c := by
  have h1 : ∀ i ∈ range m, ∑ j ∈ range m, (if i = j then (0 : ℝ) else c) = ((m : ℝ) - 1) * c := by
    intro i hi
    have : ∀ j, (if i = j then (0 : ℝ) else c) = c - (if i = j then c else 0) := by
      intro j; split_ifs <;> simp
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_ite_eq, if_pos hi]
    ring
  rw [Finset.sum_congr rfl h1]
  simp
  ring

lemma elog_XX (r m i j : ℕ) (hr : 0 < r) (hm : 0 < m) :
    elog (nodeC r (r + 2 * i)) (nodeC r (r + 2 * j))
      = elog (nodeC m i) (nodeC m j) - (if i = j then 0 else Real.log (2 * m / r)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hij : i = j
  · subst hij; simp [elog_self]
  · rw [if_neg hij]
    have hne : (i : ℝ) - j ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hij)
    have hpos : 0 < |(i : ℝ) - j| := abs_pos.2 hne
    rw [nodeC_X r i hr, nodeC_X r j hr, elog_real]
    unfold nodeC
    rw [elog_real]
    have e1 : (1 + 2 / (r : ℝ) * i) - (1 + 2 / r * j) = (2 / r) * ((i : ℝ) - j) := by ring
    have e2 : ((i : ℝ) / m) - (j / m) = ((i : ℝ) - j) / m := by ring
    rw [e1, e2, abs_mul, abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hr', abs_of_pos hm']
    have : 2 / (r : ℝ) * |(i : ℝ) - j| = (2 * m / r) * (|(i : ℝ) - j| / m) := by field_simp
    rw [this, Real.log_mul (by positivity) (by positivity)]
    ring

lemma elog_YY (r i j : ℕ) (hr : 0 < r) :
    elog (nodeC r (r + 2 * i + 1)) (nodeC r (r + 2 * j + 1))
      = elog (nodeC r (r + 2 * i)) (nodeC r (r + 2 * j)) := by
  rw [nodeC_X r i hr, nodeC_X r j hr, nodeC_Y r i hr, nodeC_Y r j hr, elog_real, elog_real]
  have : (1 + 2 / (r : ℝ) * i + 1 / r) - (1 + 2 / r * j + 1 / r) = (1 + 2 / (r : ℝ) * i) - (1 + 2 / r * j) := by
    ring
  rw [this]

/-- The `XX` block. -/
theorem XX_ge {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    (3 / 2) * (m : ℝ) ^ 2 - 2 * m * Real.log m - 3 * m - 1 / 2 - m * (m - 1) * Real.log (2 * m / r)
      ≤ ∑ i ∈ range m, ∑ j ∈ range m, elog (nodeC r (r + 2 * i)) (nodeC r (r + 2 * j)) := by
  have h := NN_ge hm
  have e : ∑ i ∈ range m, ∑ j ∈ range m, elog (nodeC r (r + 2 * i)) (nodeC r (r + 2 * j))
      = ∑ a ∈ range m, ∑ b ∈ range m, elog (nodeC m a) (nodeC m b)
        - m * (m - 1) * Real.log (2 * m / r) := by
    rw [← sum_offdiag_range (Real.log (2 * m / r)) m, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => elog_XX r m i j hr hm)
  rw [e]; linarith

/-! ### The cross block -/

lemma norm_ofReal_sub (u t : ℝ) : ‖(u : ℂ) - (t : ℂ)‖ = |u - t| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

