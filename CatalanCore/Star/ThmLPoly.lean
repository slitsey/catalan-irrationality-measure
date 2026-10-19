module

public import CatalanCore.Star.ThmLLead
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Star.ThmLPoly: θ-degree of the coefficients of `∏ (X - p_q)`

`p_q` has order `≥ -d_q` (`d_q ∈ {0,1}`, i.e. θ-degree `≤ d_q`).  Then
`[X^i] ∏_{q∈s}(X - p_q)` has θ-degree `≤ min(D, |s| - i)` with `D = ∑ d_q`, and the coefficient
at `i = |s| - D` has θ-degree exactly `D` with leading coefficient `1` provided every `p_q`
with `d_q = 1` has lead `-θ`.
-/

@[expose] public section

open Finset Polynomial

namespace CatalanCore.Star.ThmL

lemma coeff_lin_mul (p : LS) (P : LS[X]) (i : ℕ) :
    ((X - C p) * P).coeff i = (if i = 0 then 0 else P.coeff (i - 1)) - p * P.coeff i := by
  rw [sub_mul, coeff_sub, coeff_C_mul]
  rcases i with _ | j
  · simp
  · simp [coeff_X_mul]

variable {ι : Type*} [DecidableEq ι]

lemma coeff_prod_zero (s : Finset ι) (p : ι → LS) (i : ℕ) (hi : s.card < i) :
    (∏ q ∈ s, (X - C (p q))).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt ((natDegree_prod_le _ _).trans ?_) hi
  simp [natDegree_X_sub_C]

/-- Bound. -/
lemma coeff_prod_bound (p : ι → LS) (d : ι → ℕ) (s : Finset ι)
    (hd : ∀ q ∈ s, d q ≤ 1) (hp : ∀ q ∈ s, OrdGe (-(d q : ℤ)) (p q)) :
    ∀ i : ℕ, i ≤ s.card →
      OrdGe (-(min ((∑ q ∈ s, d q : ℕ) : ℤ) ((s.card : ℤ) - i)))
        ((∏ q ∈ s, (X - C (p q))).coeff i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro i hi
    have : i = 0 := by simpa using hi
    subst this
    simp only [prod_empty, coeff_one, if_true, Finset.sum_empty, Finset.card_empty]
    intro e he
    have : e ≠ 0 := by omega
    simp [HahnSeries.coeff_one, this]
  | insert q s hq ih =>
    intro i hi
    have hdq := hd q (mem_insert_self _ _)
    have hi' : i ≤ s.card + 1 := by rwa [card_insert_of_notMem hq] at hi
    have hpq := hp q (mem_insert_self _ _)
    have ih' := ih (fun r hr => hd r (mem_insert_of_mem hr)) (fun r hr => hp r (mem_insert_of_mem hr))
    rw [prod_insert hq, coeff_lin_mul, sum_insert hq, card_insert_of_notMem hq]
    simp only [Nat.cast_add, Nat.cast_one]
    set P := ∏ r ∈ s, (X - C (p r))
    set D : ℕ := ∑ r ∈ s, d r
    have hDs : D ≤ s.card := by
      calc D ≤ ∑ _r ∈ s, 1 := sum_le_sum (fun r hr => hd r (mem_insert_of_mem hr))
        _ = s.card := by simp
    -- second term
    have h2 : OrdGe (-(min ((d q : ℤ) + D) ((s.card : ℤ) + 1 - i))) (p q * P.coeff i) := by
      by_cases his : i ≤ s.card
      · have := (OrdGe.mul hpq (ih' i his))
        refine this.mono ?_
        omega
      · have : P.coeff i = 0 := coeff_prod_zero s p i (by omega)
        rw [this, mul_zero]; exact OrdGe.zero _
    have h1 : OrdGe (-(min ((d q : ℤ) + D) ((s.card : ℤ) + 1 - i)))
        (if i = 0 then 0 else P.coeff (i - 1)) := by
      by_cases h0 : i = 0
      · simp [h0]; exact OrdGe.zero _
      · simp only [h0, if_false]
        have := ih' (i - 1) (by omega)
        refine this.mono ?_
        omega
    exact OrdGe.sub h1 h2

/-- Exact lead on the diagonal `i = |s| - D`. -/
lemma coeff_prod_lead (p : ι → LS) (d : ι → ℕ) (s : Finset ι)
    (hd : ∀ q ∈ s, d q ≤ 1) (hp : ∀ q ∈ s, OrdGe (-(d q : ℤ)) (p q))
    (hl : ∀ q ∈ s, d q = 1 → HasLead (-1) (-1) (p q)) (i : ℕ)
    (hi : i + ∑ q ∈ s, d q = s.card) :
    HasLead (-((∑ q ∈ s, d q : ℕ) : ℤ)) 1 ((∏ q ∈ s, (X - C (p q))).coeff i) := by
  induction s using Finset.induction_on generalizing i with
  | empty =>
    have : i = 0 := by simpa using hi
    subst this
    simp only [prod_empty, coeff_one, if_true, Finset.sum_empty]
    simpa using HasLead.one
  | insert q s hq ih =>
    have hdq := hd q (mem_insert_self _ _)
    have hpq := hp q (mem_insert_self _ _)
    have hd' : ∀ r ∈ s, d r ≤ 1 := fun r hr => hd r (mem_insert_of_mem hr)
    have hp' : ∀ r ∈ s, OrdGe (-(d r : ℤ)) (p r) := fun r hr => hp r (mem_insert_of_mem hr)
    have hl' : ∀ r ∈ s, d r = 1 → HasLead (-1) (-1) (p r) := fun r hr => hl r (mem_insert_of_mem hr)
    have ih' := ih hd' hp' hl'
    have hbd := coeff_prod_bound p d s hd' hp'
    rw [sum_insert hq, card_insert_of_notMem hq] at hi
    rw [prod_insert hq, coeff_lin_mul, sum_insert hq]
    set P := ∏ r ∈ s, (X - C (p r))
    set D : ℕ := ∑ r ∈ s, d r
    have hDs : D ≤ s.card := by
      calc D ≤ ∑ _r ∈ s, 1 := sum_le_sum (fun r hr => hd' r hr)
        _ = s.card := by simp
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdq with h0 | h1
    · -- d q = 0
      rw [h0] at hi ⊢
      have hi1 : i ≠ 0 := by omega
      simp only [hi1, if_false]
      have A1 : HasLead (-(D : ℤ)) 1 (P.coeff (i - 1)) := ih' (i - 1) (by omega)
      have A2 : OrdGe (-(D : ℤ) + 1) (p q * P.coeff i) := by
        by_cases his : i ≤ s.card
        · have := OrdGe.mul hpq (hbd i his)
          refine this.mono ?_
          have : (0 : ℤ) = -((0 : ℕ) : ℤ) := by simp
          push_cast; omega
        · have : P.coeff i = 0 := coeff_prod_zero s p i (by omega)
          rw [this, mul_zero]; exact OrdGe.zero _
      have := HasLead.sub A1 (HasLead.zero_of_ordGe A2)
      simpa using this
    · -- d q = 1
      rw [h1] at hi ⊢
      have hqq := hl q (mem_insert_self _ _) h1
      have hiD : i + D = s.card := by omega
      have A2 : HasLead (-(D : ℤ) + -1) (-1 * 1) (p q * P.coeff i) :=
        (HasLead.mul hqq (ih' i hiD)).cast_eq (add_comm _ _) rfl rfl
      have A1 : OrdGe (-(D : ℤ) + -1 + 1) (if i = 0 then 0 else P.coeff (i - 1)) := by
        by_cases h0 : i = 0
        · simp [h0]; exact OrdGe.zero _
        · simp only [h0, if_false]
          have := hbd (i - 1) (by omega)
          refine this.mono ?_
          omega
      have := HasLead.sub (HasLead.zero_of_ordGe A1) A2
      refine this.cast_eq ?_ ?_ rfl
      · push_cast; ring
      · norm_num

end CatalanCore.Star.ThmL
