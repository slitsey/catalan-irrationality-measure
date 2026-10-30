module

public import CatalanCore.Star.Leonard.DeltaNewton
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Prop hDelta, step (4): the matrix `[f[u_p, v_q]]` is `A · D · Bᵀ`

`A`, `B` lower triangular with diagonals `(-1)^p p!`, `q!` and `D_{ij} = C(K,i+j+1) (x+j+1)_{K-i-j-1}`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

lemma dd_pair (f : F → F) (a b : F) (hab : a ≠ b) :
    dd f (insert a {b}) = (f b - f a) / (b - a) := by
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hab0 : a - b ≠ 0 := sub_ne_zero.2 hab
  rw [dd_insert f a {b} (by simpa using hab)]
  simp only [Finset.prod_singleton, Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty,
    div_one]
  field_simp
  ring

lemma Nn_zero_of_lt (u : ℕ → F) {p i : ℕ} (h : p < i) : Nn u (u p) i = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.2 h) (sub_self _)

lemma prod_k_sub (p : ℕ) : ∏ k ∈ range p, ((k : F) - (p : F)) = (-1) ^ p * (p.factorial : F) := by
  rw [← Finset.prod_range_reflect]
  have : ∀ j ∈ range p, (((p - 1 - j : ℕ) : F) - (p : F)) = -(((j : F)) + 1) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [Finset.prod_congr rfl this, Finset.prod_neg, Finset.card_range]
  congr 1
  exact_mod_cast Finset.prod_range_add_one_eq_factorial p

lemma prod_q_sub (q : ℕ) : ∏ k ∈ range q, ((q : F) - (k : F)) = (q.factorial : F) := by
  rw [← Finset.prod_range_reflect]
  have : ∀ j ∈ range q, ((q : F) - ((q - 1 - j : ℕ) : F)) = (j : F) + 1 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [Finset.prod_congr rfl this]
  exact_mod_cast Finset.prod_range_add_one_eq_factorial q

lemma Nn_uN_diag (x : F) (p : ℕ) : Nn (uN x) (uN x p) p = (-1) ^ p * (p.factorial : F) := by
  rw [← prod_k_sub]
  unfold Nn uN
  exact Finset.prod_congr rfl fun k _ => by ring

lemma Nn_vN_diag (x : F) (q : ℕ) : Nn (vN x) (vN x q) q = (q.factorial : F) := by
  rw [← prod_q_sub]
  unfold Nn vN
  exact Finset.prod_congr rfl fun k _ => by ring

/-- lower-triangular Newton matrices -/
noncomputable def NA (x : F) (m : ℕ) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun p i => Nn (uN x) (uN x p) i

noncomputable def NB (x : F) (m : ℕ) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun q j => Nn (vN x) (vN x q) j

/-- the binomial-Pochhammer core `D_{ij}` -/
noncomputable def DM (x : F) (K m : ℕ) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun i j => (K.choose ((i : ℕ) + j + 1) : F) *
    pochr (x + ((j : ℕ) : F) + 1) (K - ((i : ℕ) + j + 1))

/-- the divided-difference matrix -/
noncomputable def MD (x : F) (K m : ℕ) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun p q => dd (fun z => pochr z K) (insert (uN x p) {vN x q})

lemma MD_eq (x : F) (K m : ℕ) : MD x K m = NA x m * DM x K m * (NB x m)ᵀ := by
  ext p q
  simp only [MD, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, NA, NB, DM]
  rw [dd_pair_expand]
  set g : ℕ → ℕ → F := fun i j => Nn (uN x) (uN x p) i * Nn (vN x) (vN x q) j *
    ((K.choose (i + j + 1) : F) * pochr (x + (j : F) + 1) (K - (i + j + 1))) with hg
  have hR : ∑ j : Fin m, (∑ i : Fin m, Nn (uN x) (uN x p) i *
      ((K.choose ((i : ℕ) + j + 1) : F) * pochr (x + ((j : ℕ) : F) + 1) (K - ((i : ℕ) + j + 1)))) *
        Nn (vN x) (vN x q) j = ∑ i : Fin m, ∑ j : Fin m, g i j := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by simp only [hg]; ring
  rw [hR]
  have hF : ∑ i : Fin m, ∑ j : Fin m, g i j = ∑ i ∈ range m, ∑ j ∈ range m, g i j := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range m, g i j) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Fin.sum_univ_eq_sum_range (g i) m
  rw [hF]
  have hp := p.2
  have hq := q.2
  symm
  rw [← Finset.sum_subset (s₁ := range ((p : ℕ) + 1)) (s₂ := range m)
    (f := fun i => ∑ j ∈ range m, g i j) (fun i hi => by
      simp only [Finset.mem_range] at hi ⊢; omega) (fun i hi hi' => by
      simp only [Finset.mem_range] at hi hi'
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [hg, Nn_zero_of_lt (uN x) (show (p : ℕ) < i by omega), zero_mul])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_subset (s₁ := range ((q : ℕ) + 1)) (s₂ := range m)
    (f := fun j => g i j) (fun j hj => by
      simp only [Finset.mem_range] at hj ⊢; omega) (fun j hj hj' => by
      simp only [Finset.mem_range] at hj hj'
      simp only [hg, Nn_zero_of_lt (vN x) (show (q : ℕ) < j by omega), mul_zero, zero_mul])]

lemma det_NA (x : F) (m : ℕ) :
    (NA x m).det = ∏ p : Fin m, ((-1 : F) ^ (p : ℕ) * ((p : ℕ).factorial : F)) := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_congr rfl fun p _ => by simp [NA, Nn_uN_diag]
  · intro p i hpi
    exact Nn_zero_of_lt (uN x) hpi

lemma det_NB (x : F) (m : ℕ) :
    (NB x m).det = ∏ q : Fin m, (((q : ℕ).factorial : F)) := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_congr rfl fun q _ => by simp [NB, Nn_vN_diag]
  · intro q j hqj
    exact Nn_zero_of_lt (vN x) hqj

/-- **Determinant of the divided-difference matrix.** -/
theorem det_MD (x : F) (K m : ℕ) :
    (MD x K m).det = (∏ p : Fin m, ((-1 : F) ^ (p : ℕ) * ((p : ℕ).factorial : F))) *
      (DM x K m).det * ∏ q : Fin m, (((q : ℕ).factorial : F)) := by
  rw [MD_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_NA, det_NB]

lemma pochr_add (c : F) (a b : ℕ) : pochr c (a + b) = pochr c a * pochr (c + (a : F)) b := by
  unfold pochr
  rw [Finset.prod_range_add]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by push_cast; ring

/-- the binomial Hankel matrix `C(K, i+j+1)` -/
noncomputable def HB (K m : ℕ) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun i j => (K.choose ((i : ℕ) + j + 1) : F)

lemma DM_eq (x : F) (K m : ℕ) (hC : ∀ j : Fin m, pochr (x + 1) (j : ℕ) ≠ 0) :
    DM x K m = Matrix.diagonal (fun i : Fin m => pochr (x + 1) (K - 1 - (i : ℕ))) * HB K m *
      Matrix.diagonal (fun j : Fin m => (pochr (x + 1) (j : ℕ))⁻¹) := by
  ext i j
  simp only [DM, HB, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : (i : ℕ) + j + 1 ≤ K
  · have e : K - 1 - (i : ℕ) = (j : ℕ) + (K - ((i : ℕ) + j + 1)) := by omega
    rw [e, pochr_add]
    have h1 : x + 1 + ((j : ℕ) : F) = x + ((j : ℕ) : F) + 1 := by ring
    rw [h1]
    have := hC j
    field_simp
  · have : K.choose ((i : ℕ) + j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]

theorem det_DM (x : F) (K m : ℕ) (hC : ∀ j : Fin m, pochr (x + 1) (j : ℕ) ≠ 0) :
    (DM x K m).det = (∏ i : Fin m, pochr (x + 1) (K - 1 - (i : ℕ))) *
      (∏ j : Fin m, (pochr (x + 1) (j : ℕ))⁻¹) * (HB K m).det := by
  rw [DM_eq x K m hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  ring

end CatalanCore.Star.Leonard
