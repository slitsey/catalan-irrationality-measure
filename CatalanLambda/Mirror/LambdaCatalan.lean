module

public import CatalanLambda.Mirror.Lowner
public import CatalanLambda.Decay.LambdaCatalan

@[expose] public section

/-!
# `λ' = G/2 + 5π²/96`
-/

open Finset Real

namespace CatalanLambda.Mirror

open CatalanLambda.Decay (catalanG inj2 inj2s summable_sqInv tsum_sqInv tsum_sqInv_succ
  summable_odd tsum_odd)

theorem lamB_eq : lamB = catalanG / 2 + 5 * π ^ 2 / 96 := by
  have hh := summable_odd
  have e1 : ∀ k : ℕ, (1 : ℝ) / ((2 * (2 * k) + 1 : ℕ) : ℝ) ^ 2 = 1 / (4 * (k : ℝ) + 1) ^ 2 := by
    intro k; push_cast; ring_nf
  have e2 : ∀ k : ℕ, (1 : ℝ) / ((2 * (2 * k + 1) + 1 : ℕ) : ℝ) ^ 2 = 1 / (4 * (k : ℝ) + 3) ^ 2 := by
    intro k; push_cast; ring_nf
  have hhe : Summable fun k : ℕ => (1 : ℝ) / ((2 * (2 * k) + 1 : ℕ) : ℝ) ^ 2 :=
    hh.comp_injective inj2
  have hho : Summable fun k : ℕ => (1 : ℝ) / ((2 * (2 * k + 1) + 1 : ℕ) : ℝ) ^ 2 :=
    hh.comp_injective inj2s
  have hodd := tsum_even_add_odd (f := fun j : ℕ => (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ 2) hhe hho
  rw [tsum_odd] at hodd
  simp only [e1, e2] at hodd
  have hs1 : Summable fun k : ℕ => (1 : ℝ) / (4 * (k : ℝ) + 1) ^ 2 := by simpa only [e1] using hhe
  have hs3 : Summable fun k : ℕ => (1 : ℝ) / (4 * (k : ℝ) + 3) ^ 2 := by simpa only [e2] using hho
  have hg : Summable fun j : ℕ => (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
    refine Summable.of_norm_bounded hh (fun j => ?_)
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg (by positivity)]
  have hgE : Summable fun k : ℕ => (-1 : ℝ) ^ (2 * k) / ((2 * (2 * k) + 1 : ℕ) : ℝ) ^ 2 :=
    hg.comp_injective inj2
  have hgO : Summable fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * (2 * k + 1) + 1 : ℕ) : ℝ) ^ 2 :=
    hg.comp_injective inj2s
  have hG := tsum_even_add_odd (f := fun j : ℕ => (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) hgE hgO
  have ge : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k) / ((2 * (2 * k) + 1 : ℕ) : ℝ) ^ 2
      = 1 / (4 * (k : ℝ) + 1) ^ 2 := by
    intro k; rw [pow_mul]; simp only [neg_one_sq, one_pow, e1]
  have go : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k + 1) / ((2 * (2 * k + 1) + 1 : ℕ) : ℝ) ^ 2
      = -(1 / (4 * (k : ℝ) + 3) ^ 2) := by
    intro k; rw [pow_succ, pow_mul]; simp only [neg_one_sq, one_pow, one_mul]
    rw [neg_div, ← e2 k]
  simp only [ge, go, tsum_neg] at hG
  have hCat : catalanG = (∑' k : ℕ, (1 : ℝ) / (4 * (k : ℝ) + 1) ^ 2)
      - ∑' k : ℕ, (1 : ℝ) / (4 * (k : ℝ) + 3) ^ 2 := by
    unfold catalanG; rw [← hG]; ring
  have hsecond : ∑' k : ℕ, (1 : ℝ) / (16 * ((k : ℝ) + 1) ^ 2) = π ^ 2 / 96 := by
    have : ∀ k : ℕ, (1 : ℝ) / (16 * ((k : ℝ) + 1) ^ 2) = (1 / 16) * (1 / ((k : ℝ) + 1) ^ 2) := by
      intro k; field_simp
    simp only [this]
    rw [tsum_mul_left, tsum_sqInv_succ]; ring
  have hs2' : Summable fun k : ℕ => (1 : ℝ) / (16 * ((k : ℝ) + 1) ^ 2) := by
    have := (CatalanLambda.Decay.summable_inv_sq_add 1 one_pos).mul_left (1 / 16)
    refine this.congr (fun k => ?_)
    field_simp
  unfold lamB
  rw [Summable.tsum_sub hs1 hs2', hsecond]
  linarith

end CatalanLambda.Mirror
