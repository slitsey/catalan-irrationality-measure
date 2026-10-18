import CatalanLambda.Decay.Lowner

/-!
# Atom form of `T = λ I + M0` (3a-ii, first step)

`16 * T_{ab} = - ∑_{j ≥ 0} [ 1/((a+j+3/4)(b+j+3/4)) - 1/((a+j+1)(b+j+1)) ]`,
i.e. `T = -(1/16) ∑_μ c_μ u_μ u_μᵀ` with `u_μ(a) = 1/(a+μ)`, `c_μ = +1` at `μ = j+3/4`, `-1` at `μ = j+1`.
-/

open Finset

namespace CatalanLambda.Decay

/-- Real entries of `T = λ I + M0`. -/
noncomputable def Tent (a b : ℕ) : ℝ := (if a = b then lamS else 0) + (M0n a b : ℝ)

/-- The atom `u_μ(a) = 1/(a + μ)`. -/
noncomputable def atomU (μ : ℝ) (a : ℕ) : ℝ := 1 / ((a : ℝ) + μ)

/-- The `j`-th pair of atoms, `+1` at `j + 3/4`, `-1` at `j + 1`. -/
noncomputable def atomTerm (a b j : ℕ) : ℝ :=
  atomU (j + 3 / 4) a * atomU (j + 3 / 4) b - atomU (j + 1) a * atomU (j + 1) b

theorem atomTerm_eq (a b j : ℕ) : atomTerm a b j
    = 1 / (((a : ℝ) + j + 3 / 4) * ((b : ℝ) + j + 3 / 4))
      - 1 / (((a : ℝ) + j + 1) * ((b : ℝ) + j + 1)) := by
  unfold atomTerm atomU
  rw [one_div_mul_one_div, one_div_mul_one_div]
  congr 2 <;> ring

theorem summable_atomTerm (a b : ℕ) : Summable (atomTerm a b) := by
  by_cases hab : a = b
  · subst hab
    have h1 := summable_inv_sq_add ((a : ℝ) + 3 / 4) (by positivity)
    have h2 := summable_inv_sq_add ((a : ℝ) + 1) (by positivity)
    refine (h1.sub h2).congr (fun j => ?_)
    rw [atomTerm_eq]
    have : ((j : ℝ) + ((a : ℝ) + 3 / 4)) = (a : ℝ) + j + 3 / 4 := by ring
    have h' : ((j : ℝ) + ((a : ℝ) + 1)) = (a : ℝ) + j + 1 := by ring
    rw [this, h', sq, sq]
  · have hne : ((b : ℝ) - a) ≠ 0 := by
      intro h
      apply hab
      have : (a : ℝ) = b := by linarith
      exact_mod_cast this
    have hd := ((summable_lowTerm a).sub (summable_lowTerm b)).mul_left (1 / ((b : ℝ) - a))
    refine hd.congr (fun j => ?_)
    rw [atomTerm_eq]
    have : (a : ℝ) + j + 3 / 4 ≠ 0 := by positivity
    have : (a : ℝ) + j + 1 ≠ 0 := by positivity
    have : (b : ℝ) + j + 3 / 4 ≠ 0 := by positivity
    have : (b : ℝ) + j + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem T_eq_atoms (a b : ℕ) : 16 * Tent a b = -∑' j : ℕ, atomTerm a b j := by
  by_cases hab : a = b
  · subst hab
    unfold Tent
    rw [if_pos rfl, ← lowner_diag, (hasDerivAt_lowF a).deriv]
    have : ∀ j : ℕ, (-1 / ((a : ℝ) + j + 3 / 4) ^ 2 - -1 / ((a : ℝ) + j + 1) ^ 2)
        = -atomTerm a a j := by
      intro j
      rw [atomTerm_eq]
      have : (a : ℝ) + j + 3 / 4 ≠ 0 := by positivity
      have : (a : ℝ) + j + 1 ≠ 0 := by positivity
      field_simp
      ring
    simp only [this, tsum_neg]
    ring
  · have hne : ((a : ℝ) - b) ≠ 0 := by
      intro h
      apply hab
      have : (a : ℝ) = b := by linarith
      exact_mod_cast this
    unfold Tent
    rw [if_neg hab, zero_add, ← lowner_offdiag a b hab]
    have hdiff : lowF a - lowF b = -((a : ℝ) - b) * ∑' j : ℕ, atomTerm a b j := by
      unfold lowF
      rw [← Summable.tsum_sub (summable_lowTerm a) (summable_lowTerm b), ← tsum_mul_left]
      congr 1; ext j
      rw [atomTerm_eq]
      have : (a : ℝ) + j + 3 / 4 ≠ 0 := by positivity
      have : (a : ℝ) + j + 1 ≠ 0 := by positivity
      have : (b : ℝ) + j + 3 / 4 ≠ 0 := by positivity
      have : (b : ℝ) + j + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hdiff]
    field_simp

end CatalanLambda.Decay
