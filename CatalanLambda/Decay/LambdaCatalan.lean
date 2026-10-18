import CatalanLambda.Decay.Lowner
import Mathlib.NumberTheory.ZetaValues

/-!
# `λ = G/2 - 5π²/96`

where `G = ∑_j (-1)^j/(2j+1)²` (the same expression as `OAI.InternalCatalan.catalan`).
-/

open Finset Real

namespace CatalanLambda.Decay

/-- Catalan's constant as a series (identical to the expression in `OAI.InternalCatalan.catalan`). -/
noncomputable def catalanG : ℝ := ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2

theorem inj2 : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simp only at h; omega

theorem inj2s : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by simp only at h; omega

theorem summable_sqInv : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
  Real.summable_one_div_nat_pow.2 (by norm_num)

theorem tsum_sqInv : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = π ^ 2 / 6 := hasSum_zeta_two.tsum_eq

theorem tsum_sqInv_succ : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 = π ^ 2 / 6 := by
  have h := summable_sqInv.sum_add_tsum_nat_add 1
  rw [tsum_sqInv] at h
  simpa using h

theorem summable_odd : Summable fun j : ℕ => (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  have := (summable_inv_sq_add (1 / 2) (by norm_num)).mul_left (1 / 4)
  convert this using 2 with j
  push_cast
  field_simp
  ring

theorem tsum_odd : ∑' j : ℕ, (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 = π ^ 2 / 8 := by
  have hf := summable_sqInv
  have he : Summable fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2 :=
    hf.comp_injective inj2
  have ho : Summable fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 :=
    hf.comp_injective inj2s
  have h := tsum_even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) he ho
  rw [tsum_sqInv] at h
  have h2 : ∑' k : ℕ, (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2 = π ^ 2 / 24 := by
    have : ∀ k : ℕ, (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2 = (1 / 4) * (1 / (k : ℝ) ^ 2) := by
      intro k
      push_cast
      by_cases hk : (k : ℝ) = 0
      · simp [hk]
      · field_simp; norm_num
    simp only [this]
    rw [tsum_mul_left, tsum_sqInv]
    ring
  linarith

theorem lamS_eq : lamS = catalanG / 2 - 5 * π ^ 2 / 96 := by
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
  -- Catalan
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
  -- lambda
  have hfirst : ∑' k : ℕ, (1 : ℝ) / (16 * ((k : ℝ) + 1) ^ 2) = π ^ 2 / 96 := by
    have : ∀ k : ℕ, (1 : ℝ) / (16 * ((k : ℝ) + 1) ^ 2) = (1 / 16) * (1 / ((k : ℝ) + 1) ^ 2) := by
      intro k; field_simp
    simp only [this]
    rw [tsum_mul_left, tsum_sqInv_succ]; ring
  have hsecond : ∑' k : ℕ, (1 : ℝ) / (4 * ((k : ℝ) + 1) - 1) ^ 2
      = ∑' k : ℕ, (1 : ℝ) / (4 * (k : ℝ) + 3) ^ 2 := by
    congr 1; ext k; ring_nf
  have hs1' : Summable fun k : ℕ => (1 : ℝ) / (16 * ((k : ℝ) + 1) ^ 2) := by
    have := (summable_inv_sq_add 1 one_pos).mul_left (1 / 16)
    refine this.congr (fun k => ?_)
    field_simp
  have hs2' : Summable fun k : ℕ => (1 : ℝ) / (4 * ((k : ℝ) + 1) - 1) ^ 2 := by
    refine hs3.congr (fun k => ?_)
    ring_nf
  unfold lamS
  rw [Summable.tsum_sub hs1' hs2', hfirst, hsecond]
  linarith

end CatalanLambda.Decay
