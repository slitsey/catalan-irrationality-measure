import CatalanLambda.Decay.KrhoPD
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Theorem N_ρ, stage 1: logarithmic energies and the Cauchy determinant

`elog x y = -log ‖x - y‖` (so `elog x x = 0` by Lean's convention `log 0 = 0`; this makes all
double sums below full sums over `Fin k × Fin k`).
-/

open Finset

namespace CatalanLambda.Decay

/-- The logarithmic interaction `-log ‖x - y‖`. -/
noncomputable def elog (x y : ℂ) : ℝ := -Real.log ‖x - y‖

lemma elog_comm (x y : ℂ) : elog x y = elog y x := by unfold elog; rw [norm_sub_rev]

lemma elog_self (x : ℂ) : elog x x = 0 := by simp [elog]

/-- The Cauchy-determinant expression used in `tent_andreief_bound`. -/
noncomputable def cexpr {k : ℕ} (x y : Fin k → ℂ) : ℂ :=
  (∏ l, ∏ l' ∈ Ioi l, ((x l' - x l) * (y l - y l'))) / ∏ l, ∏ i, (x l - y i)

lemma sum_split_Ioi {k : ℕ} (f : Fin k → ℝ) (a : Fin k) (hd : f a = 0) :
    ∑ b, f b = ∑ b ∈ Iio a, f b + ∑ b ∈ Ioi a, f b := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun b => b < a)]
  congr 1
  · congr 1; ext b; simp
  · have : (univ.filter fun b => ¬ b < a) = insert a (Ioi a) := by
      ext b; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_Ioi, not_lt]
      constructor
      · intro h; rcases h.eq_or_lt with h | h
        · left; exact h.symm
        · right; exact h
      · rintro (h | h)
        · exact h.symm.le
        · exact h.le
    rw [this, Finset.sum_insert (by simp), hd, zero_add]

lemma sum_double_Ioi {k : ℕ} (f : Fin k → Fin k → ℝ) (hs : ∀ a b, f a b = f b a)
    (hd : ∀ a, f a a = 0) :
    ∑ a, ∑ b, f a b = 2 * ∑ a, ∑ b ∈ Ioi a, f a b := by
  have h1 : ∀ a, ∑ b, f a b = ∑ b ∈ Iio a, f a b + ∑ b ∈ Ioi a, f a b :=
    fun a => sum_split_Ioi (f a) a (hd a)
  simp_rw [h1, Finset.sum_add_distrib]
  have h2 : ∑ a, ∑ b ∈ Iio a, f a b = ∑ a, ∑ b ∈ Ioi a, f a b := by
    have := Finset.sum_comm' (s := (univ : Finset (Fin k))) (t := fun a => Iio a)
      (t' := (univ : Finset (Fin k))) (s' := fun b => Ioi b) (f := fun a b => f a b)
      (by intro a b; simp)
    rw [this]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => hs _ _))
  rw [h2]; ring

/-- Logarithm of the norm of the Cauchy expression. -/
lemma log_prod_prod {ι κ : Type*} (s : Finset ι) (t : ι → Finset κ) (f : ι → κ → ℝ)
    (h : ∀ l ∈ s, ∀ l' ∈ t l, f l l' ≠ 0) :
    Real.log (∏ l ∈ s, ∏ l' ∈ t l, f l l') = ∑ l ∈ s, ∑ l' ∈ t l, Real.log (f l l') := by
  rw [Real.log_prod (fun l hl => Finset.prod_ne_zero_iff.2 (h l hl))]
  exact Finset.sum_congr rfl (fun l hl => Real.log_prod (h l hl))

lemma log_norm_cexpr {k : ℕ} (x y : Fin k → ℂ) (hx : ∀ l l', l < l' → x l' - x l ≠ 0)
    (hy : ∀ l l', l < l' → y l - y l' ≠ 0) (hxy : ∀ l i, x l - y i ≠ 0) :
    Real.log ‖cexpr x y‖
      = ∑ l, ∑ l' ∈ Ioi l, (Real.log ‖x l' - x l‖ + Real.log ‖y l - y l'‖)
        - ∑ l, ∑ i, Real.log ‖x l - y i‖ := by
  unfold cexpr
  have hA : ∀ l ∈ (univ : Finset (Fin k)), ∀ l' ∈ Ioi l,
      ‖(x l' - x l) * (y l - y l')‖ ≠ 0 := fun l _ l' hl' =>
    norm_ne_zero_iff.2 (mul_ne_zero (hx l l' (mem_Ioi.1 hl')) (hy l l' (mem_Ioi.1 hl')))
  have hB : ∀ l ∈ (univ : Finset (Fin k)), ∀ i ∈ (univ : Finset (Fin k)),
      ‖x l - y i‖ ≠ 0 := fun l _ i _ => norm_ne_zero_iff.2 (hxy l i)
  have nA : ‖∏ l, ∏ l' ∈ Ioi l, ((x l' - x l) * (y l - y l'))‖
      = ∏ l, ∏ l' ∈ Ioi l, ‖(x l' - x l) * (y l - y l')‖ := by
    rw [norm_prod]; exact Finset.prod_congr rfl (fun l _ => norm_prod _ _)
  have nB : ‖∏ l, ∏ i, (x l - y i)‖ = ∏ l : Fin k, ∏ i ∈ (univ : Finset (Fin k)), ‖x l - y i‖ := by
    rw [norm_prod]; exact Finset.prod_congr rfl (fun l _ => norm_prod _ _)
  rw [norm_div, Real.log_div, nA, nB, log_prod_prod _ _ _ hA, log_prod_prod _ _ _ hB]
  · congr 1
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' hl' => ?_))
    rw [norm_mul, Real.log_mul]
    · exact norm_ne_zero_iff.2 (hx l l' (mem_Ioi.1 hl'))
    · exact norm_ne_zero_iff.2 (hy l l' (mem_Ioi.1 hl'))
  · rw [nA]; exact Finset.prod_ne_zero_iff.2 (fun l hl => Finset.prod_ne_zero_iff.2 (hA l hl))
  · rw [nB]; exact Finset.prod_ne_zero_iff.2 (fun l hl => Finset.prod_ne_zero_iff.2 (hB l hl))

/-- **Energy form of the Cauchy determinant.**
`-log ‖C‖² = ∑_{l,l'} e(x_l,x_l') + ∑_{i,i'} e(y_i,y_i') - 2 ∑_{l,i} e(x_l,y_i)`. -/
theorem neg_log_cexpr_sq {k : ℕ} (x y : Fin k → ℂ) (hxi : Function.Injective x)
    (hyi : Function.Injective y) (hxy : ∀ l i, x l ≠ y i) :
    -Real.log (‖cexpr x y‖ ^ 2)
      = ∑ l, ∑ l', elog (x l) (x l') + ∑ i, ∑ i', elog (y i) (y i')
        - 2 * ∑ l, ∑ i, elog (x l) (y i) := by
  have hx : ∀ l l', l < l' → x l' - x l ≠ 0 := fun l l' h =>
    sub_ne_zero.2 (fun e => (ne_of_lt h) (hxi e.symm))
  have hy : ∀ l l', l < l' → y l - y l' ≠ 0 := fun l l' h =>
    sub_ne_zero.2 (fun e => (ne_of_lt h) (hyi e))
  have hxy' : ∀ l i, x l - y i ≠ 0 := fun l i => sub_ne_zero.2 (hxy l i)
  have hL := log_norm_cexpr x y hx hy hxy'
  have hpos : ‖cexpr x y‖ ≠ 0 ∨ True := Or.inr trivial
  have e1 : Real.log (‖cexpr x y‖ ^ 2) = 2 * Real.log ‖cexpr x y‖ := by
    rw [Real.log_pow]; norm_num
  have s1 : ∑ l, ∑ l', elog (x l) (x l') = 2 * ∑ l, ∑ l' ∈ Ioi l, (-Real.log ‖x l' - x l‖) := by
    rw [sum_double_Ioi (fun a b => elog (x a) (x b)) (fun a b => elog_comm _ _) (fun a => elog_self _)]
    congr 1
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => ?_))
    unfold elog; rw [norm_sub_rev]
  have s2 : ∑ i, ∑ i', elog (y i) (y i') = 2 * ∑ l, ∑ l' ∈ Ioi l, (-Real.log ‖y l - y l'‖) := by
    rw [sum_double_Ioi (fun a b => elog (y a) (y b)) (fun a b => elog_comm _ _) (fun a => elog_self _)]
    rfl
  have s3 : ∑ l, ∑ i, elog (x l) (y i) = -∑ l, ∑ i, Real.log ‖x l - y i‖ := by
    simp only [elog, Finset.sum_neg_distrib]
  rw [e1, hL, s1, s2, s3]
  simp only [Finset.sum_add_distrib, neg_add, Finset.sum_neg_distrib]
  ring

end CatalanLambda.Decay
