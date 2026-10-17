module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.Polynomial.Div
public import CatalanArchive.CatalanMeasure.Parametric.CartierTranslation

/-!
# Polynomial value sequences become high-order roots at one

For a polynomial F of degree below q over F_p, the generating polynomial of
the sequence F(0),...,F(p-1), after translation by one, is divisible by
X^(p-q). This connects the column difference filter with the root at one
observed in the leading-residue relations.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

set_option autoImplicit false

open Polynomial
open scoped BigOperators Nat

theorem sum_eval_lowDegree (p : ℕ) [Fact p.Prime] (F : (ZMod p)[X])
    (hF : F.natDegree < p - 1) : (∑ x : ZMod p, F.eval x) = 0 := by
  classical
  simp only [eval_eq_sum, Polynomial.sum_def]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum]
  have hdegree : i < Fintype.card (ZMod p) - 1 := by
    simp only [ZMod.card]
    exact lt_of_le_of_lt (le_natDegree_of_ne_zero (mem_support_iff.mp hi)) hF
  rw [FiniteField.sum_pow_lt_card_sub_one (ZMod p) i hdegree, mul_zero]

noncomputable def evaluationGeneratingPoly (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[X]) : (ZMod p)[X] :=
  ∑ x : ZMod p, monomial x.val (F.eval x)

theorem coeff_evaluationGeneratingPoly_translate (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[X]) (k : ℕ) :
    ((evaluationGeneratingPoly p F).comp (X + 1)).coeff k =
      ∑ x : ZMod p, F.eval x * (x.val.choose k : ZMod p) := by
  classical
  simp only [evaluationGeneratingPoly, sum_comp, finsetSum_coeff, monomial_comp,
    coeff_C_mul, coeff_X_add_one_pow]

theorem coeff_evaluationGeneratingPoly_translate_zero (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[X]) (k : ℕ) (hdegree : F.natDegree + k < p - 1) :
    ((evaluationGeneratingPoly p F).comp (X + 1)).coeff k = 0 := by
  classical
  have hk : k < p := by omega
  have hfac : (k.factorial : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff k.factorial p).mp hzero
    exact (not_le.mpr hk) ((Fact.out : p.Prime).dvd_factorial.mp hdiv)
  have hprod : (F * descPochhammer (ZMod p) k).natDegree < p - 1 := by
    have h : (F * descPochhammer (ZMod p) k).natDegree ≤
        F.natDegree + (descPochhammer (ZMod p) k).natDegree := natDegree_mul_le
    rw [descPochhammer_natDegree] at h
    exact lt_of_le_of_lt h hdegree
  have hchoose (x : ZMod p) :
      (x.val.choose k : ZMod p) * (k.factorial : ZMod p) =
        (descPochhammer (ZMod p) k).eval x := by
    have h := descPochhammer_eval_eq_descFactorial (ZMod p) x.val k
    rw [ZMod.natCast_zmod_val] at h
    rw [h, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_comm]
  have hmul : ((evaluationGeneratingPoly p F).comp (X + 1)).coeff k *
      (k.factorial : ZMod p) = 0 := by
    rw [coeff_evaluationGeneratingPoly_translate, Finset.sum_mul]
    calc
      _ = ∑ x : ZMod p, (F * descPochhammer (ZMod p) k).eval x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [mul_assoc, hchoose, eval_mul]
      _ = 0 := sum_eval_lowDegree p _ hprod
  exact (mul_eq_zero.mp hmul).resolve_right hfac

theorem evaluationGeneratingPoly_root_order (p q : ℕ) [Fact p.Prime]
    (F : (ZMod p)[X]) (hF : F.natDegree < q) :
    X ^ (p - q) ∣ (evaluationGeneratingPoly p F).comp (X + 1) := by
  rw [X_pow_dvd_iff]
  intro k hk
  exact coeff_evaluationGeneratingPoly_translate_zero p F k (by omega)

theorem evaluationGeneratingPoly_root_one (p q : ℕ) [Fact p.Prime]
    (F : (ZMod p)[X]) (hF : F.natDegree < q) :
    (X - 1) ^ (p - q) ∣ evaluationGeneratingPoly p F := by
  obtain ⟨A, hA⟩ := evaluationGeneratingPoly_root_order p q F hF
  refine ⟨A.comp (X - 1), ?_⟩
  have h := congrArg (fun B : (ZMod p)[X] => B.comp (X - 1)) hA
  simpa only [comp_assoc, add_comp, X_comp, one_comp, sub_add_cancel,
    comp_X, mul_comp, pow_comp] using h

end CatalanMeasure.Parametric
