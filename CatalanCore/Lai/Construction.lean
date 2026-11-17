module

public import CatalanCore.Lai.DoublePole
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

/-!
# Lai's construction (ledger LA01-LA05): the rational function `R_n`, the operator `L_n`, the Hankel
# determinant `J_n(a, b, X)`

Paper: Lai, arXiv 2610.06838, §2 (Definition 2.1, Lemma 2.2, (2.5)).  Everything generic (partial
fractions with double poles, the moment functional) is in `CatalanCore.Lai.DoublePole`; this file holds
the Lai numbers `(6n, 2n)`.

* `laiNum n`, `laiDen n`, `laiR n`: `R_n(t) = (6n)!²/(2n)!³ · (t-2n)³_{2n} / (t)²_{6n+1}`.
* `laiR_partial_fractions`: the principal parts of `R_n P` (Lemma 2.2, equations (2.9)-(2.11)).
* `laiL n P`: the finite form (2.6)-(2.8), a polynomial in the three variables `a, b, X` over `ℚ`.
* `laiL_eval_moment`: the series form (2.3) at `(a, b, aζ(3) + bζ(4))`.
* `laiJ n`: the Hankel determinant (2.5), homogeneous of degree `3n`.
-/

open Polynomial Finset
open scoped Nat

namespace CatalanCore.Lai

section Arith

namespace Arith

/-- Reflection of a product over `range M`. -/
theorem prod_reflect_eq {R : Type*} [CommMonoid R] (M : ℕ) (g f : ℕ → R)
    (h : ∀ i < M, g i = f (M - 1 - i)) : ∏ i ∈ range M, g i = ∏ i ∈ range M, f i := by
  rw [← Finset.prod_range_reflect f M]
  exact Finset.prod_congr rfl fun i hi => h i (Finset.mem_range.1 hi)

/-- Reflection of a sum over `range M`. -/
theorem sum_reflect_eq {R : Type*} [AddCommMonoid R] (M : ℕ) (g f : ℕ → R)
    (h : ∀ i < M, g i = f (M - 1 - i)) : ∑ i ∈ range M, g i = ∑ i ∈ range M, f i := by
  rw [← Finset.sum_range_reflect f M]
  exact Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.1 hi)

theorem cast_reflect (M i : ℕ) (hi : i < M) : ((M - 1 - i : ℕ) : ℚ) = (M : ℚ) - 1 - i := by
  have : (M - 1 - i) + i + 1 = M := by omega
  have h2 : ((M - 1 - i : ℕ) : ℚ) + i + 1 = M := by exact_mod_cast this
  linarith

theorem prod_succ_mul_factorial (k M : ℕ) :
    (∏ i ∈ range M, ((k : ℚ) + i + 1)) * (k ! : ℚ) = ((k + M)! : ℚ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.prod_range_succ, mul_right_comm, ih, show k + (M + 1) = (k + M) + 1 by ring,
      Nat.factorial_succ]
    push_cast
    ring

/-- `∏_{i<M} (-k - (M - i)) = (-1)^M ∏_{i<M} (k + i + 1)`. -/
theorem prod_neg_shift (M k : ℕ) :
    ∏ i ∈ range M, (-(k : ℚ) - ((M : ℚ) - i)) = (-1) ^ M * ∏ i ∈ range M, ((k : ℚ) + i + 1) := by
  rw [prod_reflect_eq M _ (fun j : ℕ => (-1 : ℚ) * ((k : ℚ) + j + 1))]
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  · intro i hi
    rw [cast_reflect M i hi]
    ring

theorem sum_neg_shift (M k : ℕ) :
    ∑ i ∈ range M, 1 / (-(k : ℚ) - ((M : ℚ) - i)) = -∑ i ∈ range M, 1 / ((k : ℚ) + i + 1) := by
  rw [← Finset.sum_neg_distrib]
  refine sum_reflect_eq M _ (fun j : ℕ => -(1 / ((k : ℚ) + j + 1))) ?_
  intro i hi
  show 1 / (-(k : ℚ) - ((M : ℚ) - i)) = -(1 / ((k : ℚ) + ((M - 1 - i : ℕ) : ℚ) + 1))
  rw [cast_reflect M i hi]
  have h : (-(k : ℚ) - ((M : ℚ) - i)) = -((k : ℚ) + ((M : ℚ) - 1 - i) + 1) := by ring
  rw [h, one_div, one_div, inv_neg]

/-- `∏_{j<k} (j - k) = (-1)^k k!`. -/
theorem prod_below (k : ℕ) : ∏ j ∈ range k, ((j : ℚ) - k) = (-1) ^ k * (k ! : ℚ) := by
  rw [prod_reflect_eq k _ (fun j : ℕ => (-1 : ℚ) * ((j : ℚ) + 1))]
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    exact_mod_cast Finset.prod_range_add_one_eq_factorial k
  · intro i hi
    rw [cast_reflect k i hi]
    ring

theorem sum_below (k : ℕ) : ∑ j ∈ range k, 1 / ((j : ℚ) - k) = -∑ j ∈ range k, 1 / ((j : ℚ) + 1) := by
  rw [← Finset.sum_neg_distrib]
  refine sum_reflect_eq k _ (fun j : ℕ => -(1 / ((j : ℚ) + 1))) ?_
  intro i hi
  show 1 / ((i : ℚ) - k) = -(1 / (((k - 1 - i : ℕ) : ℚ) + 1))
  rw [cast_reflect k i hi]
  have h : ((i : ℚ) - k) = -((k : ℚ) - 1 - i + 1) := by ring
  rw [h, one_div, one_div, inv_neg]

/-- `range (N+1) \ {k} = range k ∪ {k+1, ..., N}`. -/
theorem erase_eq {N k : ℕ} (hk : k ≤ N) :
    (range (N + 1)).erase k = range k ∪ (range (N - k)).image (fun i => k + 1 + i) := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hne, hj⟩
    by_cases h : j < k
    · exact Or.inl h
    · exact Or.inr ⟨j - (k + 1), by omega, by omega⟩
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩

theorem erase_disjoint (N k : ℕ) :
    Disjoint (range k) ((range (N - k)).image (fun i => k + 1 + i)) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hj'
  have := Finset.mem_range.1 hj
  omega

theorem prod_erase_split {M : Type*} [CommMonoid M] (f : ℕ → M) {N k : ℕ} (hk : k ≤ N) :
    ∏ j ∈ (range (N + 1)).erase k, f j = (∏ j ∈ range k, f j) * ∏ i ∈ range (N - k), f (k + 1 + i) := by
  rw [erase_eq hk, Finset.prod_union (erase_disjoint N k),
    Finset.prod_image (fun a _ b _ h => by simpa using h)]

theorem sum_erase_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) {N k : ℕ} (hk : k ≤ N) :
    ∑ j ∈ (range (N + 1)).erase k, f j = (∑ j ∈ range k, f j) + ∑ i ∈ range (N - k), f (k + 1 + i) := by
  rw [erase_eq hk, Finset.sum_union (erase_disjoint N k),
    Finset.sum_image (fun a _ b _ h => by simpa using h)]

end Arith

end Arith

open Arith

section Numbers

/-- Rational harmonic numbers `H_k(s) = ∑_{i<k} 1/(i+1)^s`. -/
noncomputable def Hq (s k : ℕ) : ℚ := ∑ i ∈ range k, 1 / ((i : ℚ) + 1) ^ s

theorem harm_eq_Hq (s k : ℕ) : DoublePole.harm s k = ((Hq s k : ℚ) : ℝ) := by
  simp [DoublePole.harm, Hq]

/-- The poles `z_k = -k`. -/
noncomputable def laiNode (j : ℕ) : ℚ := -(j : ℚ)

theorem laiNode_injective : Function.Injective laiNode := fun a b h => by
  simpa [laiNode] using h

/-- `c_k = C(6n, k)² C(2n+k, k)³`. -/
noncomputable def laiCoef (n k : ℕ) : ℕ := (6 * n).choose k ^ 2 * (2 * n + k).choose k ^ 3

/-- `(6n)!² / (2n)!³`. -/
noncomputable def laiC (n : ℕ) : ℚ := ((6 * n)! : ℚ) ^ 2 / ((2 * n)! : ℚ) ^ 3

/-- The Pochhammer product `(t - 2n)_{2n} = ∏_{i<2n} (t - 2n + i)`. -/
noncomputable def laiPoch (n : ℕ) : ℚ[X] := ∏ i ∈ range (2 * n), (X - C ((2 * n : ℚ) - i))

/-- The numerator of `R_n`. -/
noncomputable def laiNum (n : ℕ) : ℚ[X] := C (laiC n) * laiPoch n ^ 3

/-- `(t)_{6n+1} = ∏_{j ≤ 6n} (t + j)`, the square root of the denominator of `R_n`. -/
noncomputable def laiDen (n : ℕ) : ℚ[X] := DoublePole.nodeProd (range (6 * n + 1)) laiNode

/-- Lai's rational function `R_n(t) = (6n)!²/(2n)!³ · (t-2n)³_{2n} / (t)²_{6n+1}` (Definition 2.1). -/
noncomputable def laiR (n : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (laiNum n) / (algebraMap ℚ[X] (RatFunc ℚ) (laiDen n)) ^ 2

theorem laiDen_eq (n : ℕ) : laiDen n = ∏ j ∈ range (6 * n + 1), (X + C (j : ℚ)) := by
  unfold laiDen DoublePole.nodeProd laiNode
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [sub_eq_add_neg]

/-- The numerator polynomial of `R_n` has degree `≤ 6n`. -/
theorem natDegree_laiNum_le (n : ℕ) : (laiNum n).natDegree ≤ 6 * n := by
  unfold laiNum laiPoch
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_pow_le).trans ?_
  have : (∏ i ∈ range (2 * n), (X - C ((2 * n : ℚ) - i))).natDegree = 2 * n := by
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [this]; omega

theorem laiPoch_eval (n k : ℕ) :
    (laiPoch n).eval (-(k : ℚ)) = ∏ i ∈ range (2 * n), ((k : ℚ) + i + 1) := by
  have h := prod_neg_shift (2 * n) k
  push_cast at h
  unfold laiPoch
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [h, Even.neg_one_pow ⟨n, by ring⟩, one_mul]

theorem laiPoch_eval_mul (n k : ℕ) :
    (laiPoch n).eval (-(k : ℚ)) * (k ! : ℚ) = ((k + 2 * n)! : ℚ) := by
  rw [laiPoch_eval, prod_succ_mul_factorial]

theorem laiPoch_ne (n k : ℕ) (i : ℕ) (hi : i ∈ range (2 * n)) :
    -(k : ℚ) ≠ (2 * n : ℚ) - i := by
  have := Finset.mem_range.1 hi
  have h2 : (i : ℚ) < 2 * n := by exact_mod_cast (by omega : i < 2 * n)
  intro h
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The cofactor `u_k` at the node `z_k`. -/
theorem cofac_eval (n k : ℕ) (hk : k ≤ 6 * n) :
    (DoublePole.cofac (range (6 * n + 1)) laiNode k).eval (laiNode k) =
      (-1) ^ k * (k ! : ℚ) * ((6 * n - k)! : ℚ) := by
  unfold DoublePole.cofac
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C, laiNode]
  have h1 : ∀ j : ℕ, (-(k : ℚ) - -(j : ℚ)) = (j : ℚ) - k := fun j => by ring
  simp_rw [h1]
  rw [prod_erase_split (fun j : ℕ => (j : ℚ) - k) hk, prod_below]
  congr 1
  have : ∀ i ∈ range (6 * n - k), (((k + 1 + i : ℕ) : ℚ) - k) = (i : ℚ) + 1 := fun i _ => by
    push_cast; ring
  rw [Finset.prod_congr rfl this]
  exact_mod_cast Finset.prod_range_add_one_eq_factorial (6 * n - k)

/-- The double-pole coefficient of `R_n` at `-k` is `c_k = C(6n, k)² C(2n+k, k)³`. -/
theorem laiCoef_eq (n k : ℕ) (hk : k ≤ 6 * n) :
    laiC n * ((laiPoch n).eval (-(k : ℚ))) ^ 3 /
        ((DoublePole.cofac (range (6 * n + 1)) laiNode k).eval (laiNode k)) ^ 2 = (laiCoef n k : ℚ) := by
  rw [cofac_eval n k hk]
  have hP : (laiPoch n).eval (-(k : ℚ)) = ((k + 2 * n)! : ℚ) / (k ! : ℚ) := by
    rw [eq_div_iff (by positivity), laiPoch_eval_mul]
  rw [hP]
  unfold laiC laiCoef
  have c1 : (((6 * n).choose k : ℕ) : ℚ) = ((6 * n)! : ℚ) / ((k ! : ℚ) * ((6 * n - k)! : ℚ)) :=
    Nat.cast_choose ℚ hk
  have c2 : (((2 * n + k).choose k : ℕ) : ℚ) = ((2 * n + k)! : ℚ) / ((k ! : ℚ) * ((2 * n)! : ℚ)) := by
    have := Nat.cast_choose ℚ (show k ≤ 2 * n + k by omega)
    simpa using this
  push_cast
  rw [c1, c2, add_comm k (2 * n)]
  have : ((-1 : ℚ) ^ k * (k ! : ℚ) * ((6 * n - k)! : ℚ)) ^ 2 = ((k ! : ℚ) * ((6 * n - k)! : ℚ)) ^ 2 := by
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; simp; ring
  rw [this]
  have h1 : (k ! : ℚ) ≠ 0 := by positivity
  have h2 : ((6 * n - k)! : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * n)! : ℚ) ≠ 0 := by positivity
  field_simp

end Numbers

section PrincipalParts

/-- `H_{2n+k} · 3 + H_{6n-k} · 2 - H_k · 5`, the harmonic combination of (2.4)/(2.8). -/
noncomputable def laiH (n k : ℕ) : ℚ := 3 * Hq 1 (2 * n + k) + 2 * Hq 1 (6 * n - k) - 5 * Hq 1 k

theorem Hq_add (k M : ℕ) : Hq 1 (k + M) = Hq 1 k + ∑ i ∈ range M, 1 / ((k : ℚ) + i + 1) := by
  unfold Hq
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  simp [add_assoc]

theorem laiPoch_deriv_eval (n k : ℕ) :
    (derivative (laiPoch n)).eval (-(k : ℚ)) =
      (laiPoch n).eval (-(k : ℚ)) * (-(Hq 1 (k + 2 * n) - Hq 1 k)) := by
  have h := DoublePole.eval_derivative_prod_X_sub (range (2 * n)) (fun i : ℕ => (2 * n : ℚ) - i)
    (x := -(k : ℚ)) (fun i hi => laiPoch_ne n k i hi)
  unfold laiPoch
  rw [h, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  congr 1
  have h2 := sum_neg_shift (2 * n) k
  push_cast at h2
  rw [h2, Hq_add]
  ring

theorem cofac_deriv_eval (n k : ℕ) (hk : k ≤ 6 * n) :
    (derivative (DoublePole.cofac (range (6 * n + 1)) laiNode k)).eval (laiNode k) =
      (DoublePole.cofac (range (6 * n + 1)) laiNode k).eval (laiNode k) *
        (Hq 1 (6 * n - k) - Hq 1 k) := by
  have h := DoublePole.eval_derivative_prod_X_sub ((range (6 * n + 1)).erase k) laiNode
    (x := laiNode k) (fun j hj => fun h => (Finset.mem_erase.1 hj).1 (laiNode_injective h).symm)
  unfold DoublePole.cofac
  rw [h, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  congr 1
  have h1 : ∀ j : ℕ, 1 / (laiNode k - laiNode j) = 1 / ((j : ℚ) - k) := fun j => by
    simp only [laiNode]; congr 1; ring
  simp_rw [h1]
  rw [sum_erase_split (fun j : ℕ => 1 / ((j : ℚ) - k)) hk, sum_below]
  have : ∀ i ∈ range (6 * n - k), 1 / (((k + 1 + i : ℕ) : ℚ) - k) = 1 / ((i : ℚ) + 1) := fun i _ => by
    push_cast; congr 1; ring
  rw [Finset.sum_congr rfl this]
  unfold Hq
  simp only [pow_one]
  ring

theorem laiA2 (n : ℕ) (P : ℚ[X]) {k : ℕ} (hk : k ≤ 6 * n) :
    DoublePole.A2 (range (6 * n + 1)) laiNode (laiNum n * P) k =
      (laiCoef n k : ℚ) * P.eval (-(k : ℚ)) := by
  unfold DoublePole.A2 laiNum
  rw [eval_mul, eval_mul, eval_C, eval_pow]
  have h := laiCoef_eq n k hk
  have : laiNode k = -(k : ℚ) := rfl
  rw [this] at h ⊢
  rw [← h]
  ring

theorem laiA1 (n : ℕ) (P : ℚ[X]) {k : ℕ} (hk : k ≤ 6 * n) :
    DoublePole.A1 (range (6 * n + 1)) laiNode (laiNum n * P) k =
      (laiCoef n k : ℚ) * (P.derivative.eval (-(k : ℚ)) - laiH n k * P.eval (-(k : ℚ))) := by
  have hne := DoublePole.cofac_eval_ne (s := range (6 * n + 1)) laiNode_injective
    (Finset.mem_range.2 (by omega : k < 6 * n + 1))
  have hA2 := laiA2 n P hk
  have hc := laiCoef_eq n k hk
  have hr : laiNode k = -(k : ℚ) := rfl
  set u := (DoublePole.cofac (range (6 * n + 1)) laiNode k).eval (laiNode k) with hu
  set B := (laiPoch n).eval (-(k : ℚ)) with hB
  unfold DoublePole.A1
  rw [hA2]
  have hd : (derivative (laiNum n * P)).eval (laiNode k) =
      laiC n * (3 * B ^ 2 * ((derivative (laiPoch n)).eval (-(k : ℚ)))) * P.eval (-(k : ℚ)) +
        laiC n * B ^ 3 * (derivative P).eval (-(k : ℚ)) := by
    unfold laiNum
    rw [hr, derivative_mul, derivative_mul, derivative_C, derivative_pow]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_zero, zero_mul, zero_add, eval_natCast]
    norm_num
    ring
  rw [hd, laiPoch_deriv_eval, cofac_deriv_eval n k hk, ← hu]
  unfold laiH
  rw [add_comm (2 * n) k, ← hc]
  field_simp
  ring

end PrincipalParts

section LemmaTwoPointTwo

/-- The double-pole coefficients of `R_n P` at `-k` (2.10). -/
noncomputable def laiA2q (n : ℕ) (P : ℚ[X]) (k : ℕ) : ℚ := (laiCoef n k : ℚ) * P.eval (-(k : ℚ))

/-- The simple-pole coefficients of `R_n P` at `-k` (2.11). -/
noncomputable def laiA1q (n : ℕ) (P : ℚ[X]) (k : ℕ) : ℚ :=
  (laiCoef n k : ℚ) * (P.derivative.eval (-(k : ℚ)) - laiH n k * P.eval (-(k : ℚ)))

theorem degree_laiNum_mul_lt (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) :
    (laiNum n * P).degree < ((12 * n + 1 : ℕ) : WithBot ℕ) := by
  by_cases hz : laiNum n * P = 0
  · rw [hz, degree_zero]; exact WithBot.bot_lt_coe _
  have hP0 : P ≠ 0 := fun h => hz (by rw [h, mul_zero])
  have h1 : P.natDegree < 6 * n := (natDegree_lt_iff_degree_lt hP0).2 hP
  have h2 := natDegree_laiNum_le n
  have h3 : (laiNum n * P).natDegree ≤ (laiNum n).natDegree + P.natDegree := natDegree_mul_le
  exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast (by omega : (laiNum n * P).natDegree < 12 * n + 1))

/-- **Lemma 2.2, partial fractions as a polynomial identity** (equations (2.9)-(2.11)). -/
theorem laiNum_mul_eq (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) :
    laiNum n * P = ∑ k ∈ range (6 * n + 1),
      (C (laiA2q n P k) * DoublePole.cofac (range (6 * n + 1)) laiNode k ^ 2 +
        C (laiA1q n P k) * ((X - C (laiNode k)) * DoublePole.cofac (range (6 * n + 1)) laiNode k ^ 2)) := by
  have hdeg : (laiNum n * P).degree < (((2 * (range (6 * n + 1)).card : ℕ) : WithBot ℕ)) := by
    refine lt_of_lt_of_le (degree_laiNum_mul_lt n P hP) ?_
    simp only [Finset.card_range]
    exact_mod_cast (by omega : 12 * n + 1 ≤ 2 * (6 * n + 1))
  have h := DoublePole.eq_sum_term (s := range (6 * n + 1)) laiNode_injective hdeg
  refine h.trans (Finset.sum_congr rfl fun k hk => ?_)
  have hk' : k ≤ 6 * n := by have := Finset.mem_range.1 hk; omega
  unfold DoublePole.term laiA2q laiA1q
  rw [laiA2 n P hk', laiA1 n P hk']

theorem sum_laiA1q (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) :
    ∑ k ∈ range (6 * n + 1), laiA1q n P k = 0 := by
  have hdeg : (laiNum n * P).degree < ((2 * (range (6 * n + 1)).card - 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_lt_of_le (degree_laiNum_mul_lt n P hP) ?_
    simp only [Finset.card_range]
    exact_mod_cast (by omega : 12 * n + 1 ≤ 2 * (6 * n + 1) - 1)
  have h := DoublePole.sum_A1_eq_zero (s := range (6 * n + 1)) laiNode_injective hdeg
  rw [← h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ 6 * n := by have := Finset.mem_range.1 hk; omega
  rw [laiA1 n P hk']
  rfl

/-- **Lemma 2.2, principal parts of `R_n P` at every point of a `ℚ`-algebra field** where it is defined. -/
theorem laiR_partial_fractions {𝕂 : Type*} [Field 𝕂] [Algebra ℚ 𝕂] (n : ℕ) (P : ℚ[X])
    (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) {t : 𝕂} (ht : ∀ k ∈ range (6 * n + 1), t + (k : 𝕂) ≠ 0) :
    aeval t (laiNum n) / (aeval t (laiDen n)) ^ 2 * aeval t P =
      ∑ k ∈ range (6 * n + 1), (algebraMap ℚ 𝕂 (laiA1q n P k) / (t + k) +
        algebraMap ℚ 𝕂 (laiA2q n P k) / (t + k) ^ 2) := by
  have h := congrArg (aeval t) (laiNum_mul_eq n P hP)
  rw [map_mul, map_sum] at h
  have hz : ∀ k : ℕ, algebraMap ℚ 𝕂 (laiNode k) = -(k : 𝕂) := fun k => by simp [laiNode]
  have hW : aeval t (laiDen n) ≠ 0 := by
    unfold laiDen DoublePole.nodeProd
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro j hj
    simpa [hz, sub_eq_add_neg] using ht j hj
  rw [div_mul_eq_mul_div, h, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hW2 : aeval t (laiDen n) = (t + k) * aeval t (DoublePole.cofac (range (6 * n + 1)) laiNode k) := by
    unfold laiDen
    rw [DoublePole.nodeProd_eq k hk]
    simp [hz, sub_eq_add_neg]
  have htk : t + (k : 𝕂) ≠ 0 := ht k hk
  have hu : aeval t (DoublePole.cofac (range (6 * n + 1)) laiNode k) ≠ 0 := by
    intro h0; apply hW; rw [hW2, h0, mul_zero]
  rw [hW2]
  simp only [map_add, map_mul, aeval_C, map_pow, map_sub, aeval_X, hz, sub_neg_eq_add]
  field_simp
  ring

end LemmaTwoPointTwo

section LA01

theorem laiA2q_one (n k : ℕ) : laiA2q n 1 k = (laiCoef n k : ℚ) := by
  simp [laiA2q]

theorem laiA1q_one (n k : ℕ) : laiA1q n 1 k = -(laiCoef n k : ℚ) * laiH n k := by
  simp [laiA1q]

/-- The indeterminate `t` of `ℚ(t)`. -/
noncomputable def laiT : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) X

/-- **LA01 (Lai Lemma 2.2, the case `P = 1`).**  In `ℚ(t)`, for `n ≥ 1`,
`R_n(t) = ∑_{k ≤ 6n} (r_{k,1} / (t + k) + r_{k,2} / (t + k)²)` with `r_{k,2} = c_k` and
`r_{k,1} = c_k (5H_k - 3H_{2n+k} - 2H_{6n-k})`. -/
theorem laiR_eq_partialFractions (n : ℕ) (hn : 1 ≤ n) :
    laiR n = ∑ k ∈ range (6 * n + 1),
      (algebraMap ℚ (RatFunc ℚ) (-(laiCoef n k : ℚ) * laiH n k) / (laiT + k) +
        algebraMap ℚ (RatFunc ℚ) (laiCoef n k : ℚ) / (laiT + k) ^ 2) := by
  have hP : (1 : ℚ[X]).degree < ((6 * n : ℕ) : WithBot ℕ) := by
    rw [degree_one]; exact_mod_cast (by omega : 0 < 6 * n)
  have h := laiR_partial_fractions (𝕂 := RatFunc ℚ) n 1 hP (t := laiT) (fun k _ => by
    have : laiT + (k : RatFunc ℚ) = algebraMap ℚ[X] (RatFunc ℚ) (X + C (k : ℚ)) := by
      simp [laiT]
    rw [this]
    exact (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).2 (X_add_C_ne_zero _))
  have e1 : ∀ p : ℚ[X], aeval laiT p = algebraMap ℚ[X] (RatFunc ℚ) p := fun p => by
    rw [laiT, aeval_algebraMap_apply, aeval_X_left_apply]
  simp only [e1, map_one, mul_one, laiA2q_one, laiA1q_one] at h
  unfold laiR
  exact h

end LA01

section Operator

/-- Polynomials in the three variables `a = X 0`, `b = X 1`, `X = X 2` over `ℚ`. -/
abbrev MP : Type := MvPolynomial (Fin 3) ℚ

/-- `ζ(3) = ∑_{k ≥ 0} 1/(k+1)³`. -/
noncomputable def zeta3 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3

/-- `ζ(4) = ∑_{k ≥ 0} 1/(k+1)⁴`. -/
noncomputable def zeta4 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 4

theorem zeta3_eq : zeta3 = DoublePole.zetaSum 3 := rfl
theorem zeta4_eq : zeta4 = DoublePole.zetaSum 4 := rfl

/-- `U_k = -3a H_k(2) - 2b H_k(3)` (2.7). -/
noncomputable def laiU (k : ℕ) : MP :=
  MvPolynomial.C (-3 * Hq 2 k) * MvPolynomial.X 0 + MvPolynomial.C (-2 * Hq 3 k) * MvPolynomial.X 1

/-- `V_k = (3H_{2n+k} + 2H_{6n-k} - 5H_k)(3aH_k(2) + 2bH_k(3)) + 6(X - aH_k(3) - bH_k(4))` (2.8). -/
noncomputable def laiV (n k : ℕ) : MP :=
  MvPolynomial.C (laiH n k) *
      (MvPolynomial.C (3 * Hq 2 k) * MvPolynomial.X 0 + MvPolynomial.C (2 * Hq 3 k) * MvPolynomial.X 1) +
    MvPolynomial.C 6 * (MvPolynomial.X 2 - MvPolynomial.C (Hq 3 k) * MvPolynomial.X 0 -
      MvPolynomial.C (Hq 4 k) * MvPolynomial.X 1)

/-- The operator `L_n` of (2.3), in the finite form (2.6): `∑_k c_k (U_k P'(-k) + V_k P(-k))`, a
polynomial in `a, b, X` over `ℚ`. -/
noncomputable def laiL (n : ℕ) (P : ℚ[X]) : MP :=
  ∑ k ∈ range (6 * n + 1), MvPolynomial.C (laiCoef n k : ℚ) *
    (laiU k * MvPolynomial.C (P.derivative.eval (-(k : ℚ))) +
      laiV n k * MvPolynomial.C (P.eval (-(k : ℚ))))

/-- The Hankel matrix `(L_n(t^{i+j}))_{0 ≤ i,j < 3n}`. -/
noncomputable def laiMat (n : ℕ) : Matrix (Fin (3 * n)) (Fin (3 * n)) MP :=
  Matrix.of fun i j => laiL n (X ^ ((i : ℕ) + j))

/-- Lai's Hankel determinant `J_n(a, b, X) = (∏_{i<3n} i!²)⁻¹ det (L_n(t^{i+j}))` (2.5). -/
noncomputable def laiJ (n : ℕ) : MP :=
  MvPolynomial.C ((∏ i ∈ range (3 * n), ((i ! : ℚ)) ^ 2)⁻¹) * (laiMat n).det

/-- The real function `R_n(t)`. -/
noncomputable def laiRfun (n : ℕ) (t : ℝ) : ℝ := aeval t (laiNum n) / (aeval t (laiDen n)) ^ 2

/-- The real function `t ↦ R_n(t) P(t)`. -/
noncomputable def laiFun (n : ℕ) (P : ℚ[X]) (t : ℝ) : ℝ := laiRfun n t * aeval t P

theorem laiL_eval (n : ℕ) (P : ℚ[X]) (a b x : ℝ) :
    MvPolynomial.aeval ![a, b, x] (laiL n P) = ∑ k ∈ range (6 * n + 1), (laiCoef n k : ℝ) *
      ((-3 * a * (Hq 2 k : ℝ) - 2 * b * (Hq 3 k : ℝ)) * ((P.derivative.eval (-(k : ℚ)) : ℚ) : ℝ) +
        ((laiH n k : ℝ) * (3 * a * (Hq 2 k : ℝ) + 2 * b * (Hq 3 k : ℝ)) +
          6 * (x - a * (Hq 3 k : ℝ) - b * (Hq 4 k : ℝ))) * ((P.eval (-(k : ℚ)) : ℚ) : ℝ)) := by
  unfold laiL laiU laiV
  have h0 : (![a, b, x] : Fin 3 → ℝ) 0 = a := rfl
  have h1 : (![a, b, x] : Fin 3 → ℝ) 1 = b := rfl
  have h2 : (![a, b, x] : Fin 3 → ℝ) 2 = x := rfl
  simp only [map_sum, map_mul, map_add, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    h0, h1, h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [eq_ratCast]
  push_cast
  ring

end Operator

section Moment

theorem laiFun_eq_pfFun (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) :
    ∀ t > (0 : ℝ), laiFun n P t = DoublePole.pfFun (6 * n) (fun k => (laiA1q n P k : ℝ))
      (fun k => (laiA2q n P k : ℝ)) t := by
  intro t ht
  unfold laiFun laiRfun DoublePole.pfFun
  rw [laiR_partial_fractions n P hP (fun k _ => by positivity)]
  simp only [eq_ratCast]

/-- **Lai (2.3) ⇔ Lemma 2.2 (ledger LA03).**  For real `a, b` and every `P ∈ ℚ[t]` of degree `< 6n`:
`L_n(P)(a, b, aζ(3) + bζ(4)) = -3a ∑_{m≥1} (R_n P)'(m) + b ∑_{m≥1} (R_n P)''(m)`. -/
theorem laiL_eval_moment (n : ℕ) (P : ℚ[X]) (hP : P.degree < ((6 * n : ℕ) : WithBot ℕ)) (a b : ℝ) :
    MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4] (laiL n P) =
      -3 * a * ∑' m : ℕ, deriv (laiFun n P) ((m : ℝ) + 1) +
        b * ∑' m : ℕ, deriv (deriv (laiFun n P)) ((m : ℝ) + 1) := by
  have h1 : ∑ k ∈ range (6 * n + 1), (laiA1q n P k : ℝ) = 0 := by
    have := sum_laiA1q n P hP
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) this
  have hm := DoublePole.moment (6 * n) (fun k => (laiA1q n P k : ℝ)) (fun k => (laiA2q n P k : ℝ))
    (laiFun n P) (laiFun_eq_pfFun n P hP) h1 (-3 * a) b
  rw [← mul_assoc] at hm
  rw [show (-3 * a) * (∑' m : ℕ, deriv (laiFun n P) ((m : ℝ) + 1)) =
      -3 * a * ∑' m : ℕ, deriv (laiFun n P) ((m : ℝ) + 1) from rfl]
  rw [hm, laiL_eval, Finset.sum_mul, zeta3_eq, zeta4_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [laiA1q, laiA2q, harm_eq_Hq]
  push_cast
  ring

end Moment

section Homogeneity

theorem isHomogeneous_laiU (k : ℕ) : (laiU k).IsHomogeneous 1 := by
  unfold laiU
  exact (MvPolynomial.isHomogeneous_C_mul_X _ _).add (MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem isHomogeneous_laiV (n k : ℕ) : (laiV n k).IsHomogeneous 1 := by
  unfold laiV
  refine MvPolynomial.IsHomogeneous.add ?_ ?_
  · exact MvPolynomial.IsHomogeneous.C_mul
      ((MvPolynomial.isHomogeneous_C_mul_X _ _).add (MvPolynomial.isHomogeneous_C_mul_X _ _)) _
  · exact MvPolynomial.IsHomogeneous.C_mul
      (((MvPolynomial.isHomogeneous_X _ _).sub (MvPolynomial.isHomogeneous_C_mul_X _ _)).sub
        (MvPolynomial.isHomogeneous_C_mul_X _ _)) _

theorem isHomogeneous_laiL (n : ℕ) (P : ℚ[X]) : (laiL n P).IsHomogeneous 1 := by
  unfold laiL
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => MvPolynomial.IsHomogeneous.C_mul ?_ _
  refine MvPolynomial.IsHomogeneous.add ?_ ?_
  · simpa using (isHomogeneous_laiU k).mul (MvPolynomial.isHomogeneous_C _ _)
  · simpa using (isHomogeneous_laiV n k).mul (MvPolynomial.isHomogeneous_C _ _)

theorem isHomogeneous_det {m : ℕ} (M : Matrix (Fin m) (Fin m) MP) (h : ∀ i j, (M i j).IsHomogeneous 1) :
    M.det.IsHomogeneous m := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp : (∏ i, M (σ i) i).IsHomogeneous (∑ _i : Fin m, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => h _ _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hp
  rw [Units.smul_def]
  have hz : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (∏ i, M (σ i) i) : MP) =
      MvPolynomial.C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) * ∏ i, M (σ i) i := by
    rw [zsmul_eq_mul]
    simp
  rw [hz]
  exact MvPolynomial.IsHomogeneous.C_mul hp _

/-- **LA05.**  `J_n(a, b, X)` is homogeneous of degree `3n`. -/
theorem isHomogeneous_laiJ (n : ℕ) : (laiJ n).IsHomogeneous (3 * n) := by
  unfold laiJ
  refine MvPolynomial.IsHomogeneous.C_mul (isHomogeneous_det _ fun i j => ?_) _
  exact isHomogeneous_laiL n _

/-- A homogeneous polynomial of degree `d` scales by `r^d`. -/
theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    {F : MvPolynomial σ R} {d : ℕ} (h : F.IsHomogeneous d) (r : R) (v : σ → R) :
    MvPolynomial.eval (fun i => r * v i) F = r ^ d * MvPolynomial.eval v F := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw := h (MvPolynomial.mem_support_iff.1 hm)
  have hd : ∑ i, m i = d := by
    rw [← hw]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

end Homogeneity

section Hankel

theorem degree_X_pow_lt (n : ℕ) (i j : Fin (3 * n)) :
    (X ^ ((i : ℕ) + j) : ℚ[X]).degree < ((6 * n : ℕ) : WithBot ℕ) := by
  rw [degree_X_pow]
  have := i.2
  have := j.2
  exact_mod_cast (by omega : (i : ℕ) + j < 6 * n)

/-- The determinant (2.5) evaluated at a real point, with the series form (2.3) in each entry. -/
theorem laiJ_eval_det (n : ℕ) (a b : ℝ) :
    MvPolynomial.aeval ![a, b, a * zeta3 + b * zeta4] (laiJ n) =
      ((∏ i ∈ range (3 * n), ((i ! : ℝ)) ^ 2)⁻¹) *
        (Matrix.of fun i j : Fin (3 * n) =>
          -3 * a * ∑' m : ℕ, deriv (laiFun n (X ^ ((i : ℕ) + j))) ((m : ℝ) + 1) +
            b * ∑' m : ℕ, deriv (deriv (laiFun n (X ^ ((i : ℕ) + j)))) ((m : ℝ) + 1)).det := by
  unfold laiJ laiMat
  rw [map_mul, MvPolynomial.aeval_C, AlgHom.map_det]
  congr 1
  · simp only [eq_ratCast]; push_cast; rfl
  · congr 1
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact laiL_eval_moment n _ (degree_X_pow_lt n i j) a b

theorem natDegree_aeval_le {F : MP} {d : ℕ} (h : F.IsHomogeneous d) (g : Fin 3 → ℚ[X])
    (hg : ∀ i, (g i).natDegree ≤ 1) : (MvPolynomial.aeval g F).natDegree ≤ d := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  have hw := h (MvPolynomial.mem_support_iff.1 hm)
  have hd : ∑ i, m i = d := by
    rw [← hw]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  rw [← hd]
  refine Finset.sum_le_sum fun i _ => ?_
  refine natDegree_pow_le.trans ?_
  nlinarith [hg i]

theorem eval_aeval (g : Fin 3 → ℚ[X]) (F : MP) (x : ℚ) :
    (MvPolynomial.aeval g F).eval x = MvPolynomial.eval (fun i => (g i).eval x) F := by
  have h := congrArg (fun T => T F)
    (MvPolynomial.comp_aeval (R := ℚ) (σ := Fin 3) (B := ℚ) (S₁ := ℚ[X]) (f := g)
      (Polynomial.aeval x))
  simp only [AlgHom.comp_apply, MvPolynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval] at h
  exact h

end Hankel

end CatalanCore.Lai
