module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# UF moments, step (a'): the cross-fiber bracket modulo `p` is a Cauchy sum

Reduce the bracket `s'·ζ - g·(E ζ)` of `moment_second_order` modulo `p` (`ζ = D⁻¹ Y`,
`g = D⁻¹ s`).  Modulo `p` the colouring `col` (residues) satisfies: `g` lives on the own colour
`τ`, the cross entries are Loewner, `Ē_{ja} = (ȳ_a - ȳ_j)/(col a - col j)`, the own-colour block of
`Ē` vanishes, and `s̄'_a = (ȳ_a - ȳ_t)/(col a - τ)` off the own colour.  Then (`cross_eval`)

  `s̄'·ζ - g·(Ē ζ) = Σ_{col a ≠ τ} ζ_a (B ȳ_a - G₀)/(col a - τ)`,
  `B = 1 - Σ g`, `G₀ = ȳ_t - g·ȳ` (the reduced own-fiber moment, `0` on the direction class).

Grouped by colours (`sum_by_colour`) the weight of a residue `c` is `B Σ_{col a = c} ζ_a ȳ_a`,
i.e. `γ(c)/B` with `γ(c) = u_cᵀ Q̄_c⁻¹ u_c`, `u_c = -B ȳ_c`: no double poles occur.
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFMoments

variable {k : Type*} [Field k] [DecidableEq k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The reduced cross-fiber bracket.** -/
theorem cross_eval (col : ι → k) (τ : k) (yb : ι → k) (yt : k) (g ζ sb : ι → k)
    (Eb : Matrix ι ι k)
    (hg : ∀ a, col a ≠ τ → g a = 0)
    (hE : ∀ j a, col j = τ → col a ≠ τ → Eb j a = (yb a - yb j) / (col a - τ))
    (hE0 : ∀ j a, col j = τ → col a = τ → Eb j a = 0)
    (hs : ∀ a, col a ≠ τ → sb a = (yb a - yt) / (col a - τ))
    (hs0 : ∀ a, col a = τ → sb a = 0) :
    sb ⬝ᵥ ζ - g ⬝ᵥ (Eb *ᵥ ζ) =
      ∑ a, if col a = τ then 0 else
        ζ a * ((1 - ∑ j, g j) * yb a - (yt - g ⬝ᵥ yb)) / (col a - τ) := by
  -- each `g_j (Ē ζ)_j` as a sum over the outside colours
  have hrow : ∀ j, g j * (Eb *ᵥ ζ) j =
      ∑ a, if col a = τ then 0 else g j * (yb a - yb j) / (col a - τ) * ζ a := by
    intro j
    by_cases hj : col j = τ
    · rw [mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : col a = τ
      · simp only [ha, ↓reduceIte]; rw [hE0 j a hj ha]; ring
      · simp only [ha, ↓reduceIte]; rw [hE j a hj ha]; ring
    · rw [hg j hj, zero_mul]
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      split_ifs <;> ring
  have hsb : sb ⬝ᵥ ζ = ∑ a, if col a = τ then 0 else (yb a - yt) / (col a - τ) * ζ a := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : col a = τ
    · simp only [ha, ↓reduceIte]; rw [hs0 a ha, zero_mul]
    · simp only [ha, ↓reduceIte]; rw [hs a ha]
  have hg2 : g ⬝ᵥ (Eb *ᵥ ζ) =
      ∑ a, if col a = τ then 0 else (∑ j, g j * (yb a - yb j)) / (col a - τ) * ζ a := by
    rw [dotProduct]
    simp_rw [hrow]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : col a = τ
    · simp [ha]
    · simp only [ha, ↓reduceIte]
      rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
  rw [hsb, hg2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : col a = τ
  · simp [ha]
  · simp only [ha, ↓reduceIte]
    have e : ∑ j, g j * (yb a - yb j) = (∑ j, g j) * yb a - g ⬝ᵥ yb := by
      rw [dotProduct, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    ring

omit [DecidableEq k] [DecidableEq ι] in
/-- **Grouping a Cauchy sum by colours.** -/
theorem sum_by_colour {α : Type*} [Fintype α] [DecidableEq α] (col : ι → α) (f : α → k)
    (x : ι → k) :
    ∑ a, f (col a) * x a = ∑ c, f c * ∑ a ∈ univ.filter (fun a => col a = c), x a := by
  rw [← Finset.sum_fiberwise univ col (fun a => f (col a) * x a)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

end CatalanCore.Uniform.Content.UFMoments
