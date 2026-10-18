module

public import CatalanLambda.Mirror.Lowner
public import CatalanLambda.Decay.Atoms

@[expose] public section

/-!
# Atom form of `T̄ = -(λ' I + N₀) = L_F̄ / 16`

`16 * T̄_{ab} = - ∑_{j ≥ 0} [ 1/((a+j+1/4)(b+j+1/4)) - 1/((a+j+1)(b+j+1)) ]`.
-/

open Finset

namespace CatalanLambda.Mirror

open CatalanLambda.Decay (atomU summable_inv_sq_add)

/-- Real entries of `T̄ = -(λ' I + N₀)`. -/
noncomputable def TbarEnt (a b : ℕ) : ℝ := -((if a = b then lamB else 0) + (N0n a b : ℝ))

/-- The `j`-th pair of atoms, `+1` at `j + 1/4`, `-1` at `j + 1`. -/
noncomputable def atomTermB (a b j : ℕ) : ℝ :=
  atomU (j + 1 / 4) a * atomU (j + 1 / 4) b - atomU (j + 1) a * atomU (j + 1) b

theorem atomTermB_eq (a b j : ℕ) : atomTermB a b j
    = 1 / (((a : ℝ) + j + 1 / 4) * ((b : ℝ) + j + 1 / 4))
      - 1 / (((a : ℝ) + j + 1) * ((b : ℝ) + j + 1)) := by
  unfold atomTermB atomU
  rw [one_div_mul_one_div, one_div_mul_one_div]
  congr 2 <;> ring

theorem summable_atomTermB (a b : ℕ) : Summable (atomTermB a b) := by
  by_cases hab : a = b
  · subst hab
    have h1 := summable_inv_sq_add ((a : ℝ) + 1 / 4) (by positivity)
    have h2 := summable_inv_sq_add ((a : ℝ) + 1) (by positivity)
    refine (h1.sub h2).congr (fun j => ?_)
    rw [atomTermB_eq]
    have : ((j : ℝ) + ((a : ℝ) + 1 / 4)) = (a : ℝ) + j + 1 / 4 := by ring
    have h' : ((j : ℝ) + ((a : ℝ) + 1)) = (a : ℝ) + j + 1 := by ring
    rw [this, h', sq, sq]
  · have hne : ((b : ℝ) - a) ≠ 0 := by
      intro h
      apply hab
      have : (a : ℝ) = b := by linarith
      exact_mod_cast this
    have hd := ((summable_lowTermB a).sub (summable_lowTermB b)).mul_left (1 / ((b : ℝ) - a))
    refine hd.congr (fun j => ?_)
    rw [atomTermB_eq]
    have : (a : ℝ) + j + 1 / 4 ≠ 0 := by positivity
    have : (a : ℝ) + j + 1 ≠ 0 := by positivity
    have : (b : ℝ) + j + 1 / 4 ≠ 0 := by positivity
    have : (b : ℝ) + j + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem T_eq_atomsB (a b : ℕ) : 16 * TbarEnt a b = -∑' j : ℕ, atomTermB a b j := by
  by_cases hab : a = b
  · subst hab
    unfold TbarEnt
    rw [if_pos rfl]
    have hd := lowner_diagB a
    rw [(hasDerivAt_lowFB a).deriv] at hd
    have : ∀ j : ℕ, (-1 / ((a : ℝ) + j + 1 / 4) ^ 2 - -1 / ((a : ℝ) + j + 1) ^ 2)
        = -atomTermB a a j := by
      intro j
      rw [atomTermB_eq]
      have : (a : ℝ) + j + 1 / 4 ≠ 0 := by positivity
      have : (a : ℝ) + j + 1 ≠ 0 := by positivity
      field_simp
      ring
    simp only [this, tsum_neg] at hd
    linarith
  · have hne : ((a : ℝ) - b) ≠ 0 := by
      intro h
      apply hab
      have : (a : ℝ) = b := by linarith
      exact_mod_cast this
    unfold TbarEnt
    rw [if_neg hab, zero_add]
    have hl := lowner_offdiagB a b hab
    have hdiff : lowFB a - lowFB b = -((a : ℝ) - b) * ∑' j : ℕ, atomTermB a b j := by
      unfold lowFB
      rw [← Summable.tsum_sub (summable_lowTermB a) (summable_lowTermB b), ← tsum_mul_left]
      congr 1; ext j
      rw [atomTermB_eq]
      have : (a : ℝ) + j + 1 / 4 ≠ 0 := by positivity
      have : (a : ℝ) + j + 1 ≠ 0 := by positivity
      have : (b : ℝ) + j + 1 / 4 ≠ 0 := by positivity
      have : (b : ℝ) + j + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hdiff] at hl
    field_simp at hl
    linarith

end CatalanLambda.Mirror
