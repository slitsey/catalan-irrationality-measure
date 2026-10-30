module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.LinearCombination

/-!
# Homogenised polynomials and top-coefficient jets (tool for package H2)

`RF N f g` : `f` has degree `≤ N` and its reflection `reflect N f` (coefficients reversed) is `g`.
The calculus `RF_lin`, `RF_mul`, `RF_add`, ... computes reflections of products of linear forms.
`natDegree_le_of_RF`: if `X^k ∣ g` then `f` has degree `≤ N - k`, so a degree bound for a
polynomial built from symbolic products reduces to a congruence modulo `X^k` for the reflected
(products of `1 + c X`) polynomials, whose low coefficients are the elementary symmetric functions.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- The linear form `a z + b`. -/
noncomputable def lin (a b : F) : F[X] := C a * X + C b

lemma natDegree_lin_le (a b : F) : (lin a b).natDegree ≤ 1 := by
  unfold lin; compute_degree

/-- `f` has degree `≤ N` and `reflect N f = g`. -/
def RF (N : ℕ) (f g : F[X]) : Prop := f.natDegree ≤ N ∧ reflect N f = g

lemma RF_lin (a b : F) : RF 1 (lin a b) (lin b a) := by
  refine ⟨natDegree_lin_le a b, ?_⟩
  unfold lin
  rw [reflect_add, reflect_C_mul, reflect_one_X, reflect_C]
  simp [add_comm]

lemma RF_mul {N M : ℕ} {f g f' g' : F[X]} (hf : RF N f f') (hg : RF M g g') :
    RF (N + M) (f * g) (f' * g') := by
  refine ⟨(natDegree_mul_le).trans (add_le_add hf.1 hg.1), ?_⟩
  rw [reflect_mul f g hf.1 hg.1, hf.2, hg.2]

lemma RF_add {N : ℕ} {f g f' g' : F[X]} (hf : RF N f f') (hg : RF N g g') :
    RF N (f + g) (f' + g') := by
  refine ⟨(natDegree_add_le _ _).trans (max_le hf.1 hg.1), ?_⟩
  rw [reflect_add, hf.2, hg.2]

lemma RF_neg {N : ℕ} {f f' : F[X]} (hf : RF N f f') : RF N (-f) (-f') := by
  refine ⟨by simpa using hf.1, ?_⟩
  rw [reflect_neg, hf.2]

lemma RF_sub {N : ℕ} {f g f' g' : F[X]} (hf : RF N f f') (hg : RF N g g') :
    RF N (f - g) (f' - g') := by
  simpa [sub_eq_add_neg] using RF_add hf (RF_neg hg)

lemma RF_C_mul {N : ℕ} {f f' : F[X]} (c : F) (hf : RF N f f') : RF N (C c * f) (C c * f') := by
  refine ⟨(natDegree_C_mul_le c f).trans hf.1, ?_⟩
  rw [reflect_C_mul, hf.2]

lemma RF_one : RF 0 (1 : F[X]) 1 := ⟨by simp, by simp [reflect_one]⟩

lemma RF_prod_range (m : ℕ) (a b : ℕ → F) :
    RF m (∏ i ∈ Finset.range m, lin (a i) (b i)) (∏ i ∈ Finset.range m, lin (b i) (a i)) := by
  induction m with
  | zero => simpa using RF_one
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    exact RF_mul ih (RF_lin _ _)

/-- Degree bound from divisibility of the reflection by `X^k`. -/
lemma natDegree_le_of_RF {N k : ℕ} {f g : F[X]} (hk : k ≤ N) (h : RF N f g)
    (hd : (X : F[X]) ^ k ∣ g) : f.natDegree ≤ N - k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hfn : N < n ∨ n ≤ N := by omega
  rcases hfn with hfn | hfn
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h.1 hfn)
  · have := (X_pow_dvd_iff.1 hd) (N - n) (by omega)
    rw [← h.2, coeff_reflect, revAt_le (by omega)] at this
    have e : N - (N - n) = n := by omega
    rwa [e] at this

end CatalanCore.Star.Leonard
