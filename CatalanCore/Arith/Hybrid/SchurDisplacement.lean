module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic
@[expose] public section
open Finset Matrix
namespace CatalanCore.Arith.Hybrid

/-! # The displacement identity of a Schur complement of a Loewner matrix

If the blocks `A, B, C, D` of a block matrix satisfy the Loewner commutator relations with respect
to node values (`n (x_j - x_i) M_ij = P_j - P_i`), then the cleared Schur complement
`g D - C N B` (`N A = A N = g`) is a rank-two Cauchy-like matrix:

  `g n (xc_y - xr_z) (g D_zy - (C N B)_zy) = α_z β'_y - β_z α'_y`,

with the four one-node moments
`α_z = g - (C N 1)_z`, `β_z = g Pr_z - (C N P)_z`, `α'_y = g - (1ᵀ N B)_y`,
`β'_y = g Pc_y - (Pᵀ N B)_y`.  The proof is the usual displacement-rank argument and uses only
the commutator relations and `N A = A N = g`; it is valid over any commutative ring.  This reduces
the leading cross-cell block (N3) and the weighted same-cell congruence (N1) to evaluating these
one-node moments, instead of a double contraction of the Loewner matrix by augmented vectors. -/

section Generic
variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The commutator relation `n (a_j - a_i) A_ij = P_j - P_i` transfers to the cleared inverse:
`g n (a_j - a_i) N_ij = (N P)_i (1ᵀ N)_j - (N 1)_i (Pᵀ N)_j`. -/
theorem cleared_inverse_commutator (A N : Matrix ι ι R) (g n : R)
    (hAN : A * N = g • 1) (hNA : N * A = g • 1) (a P : ι → R)
    (hA : ∀ i j, n * (a j - a i) * A i j = P j - P i) (i j : ι) :
    g * (n * (a j - a i)) * N i j =
      (∑ k, N i k * P k) * (∑ k, N k j) - (∑ k, N i k) * (∑ k, P k * N k j) := by
  have e1 : ∀ k l, N i k * (n * (a l - a k) * A k l) * N l j =
      N i k * (P l - P k) * N l j := fun k l => by rw [hA k l]
  have hs : ∑ k, ∑ l, N i k * (n * (a l - a k) * A k l) * N l j =
      ∑ k, ∑ l, N i k * (P l - P k) * N l j :=
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => e1 k l))
  -- left: ∑_k ∑_l N i k (n (a l - a k) A k l) N l j = n g (a i - a j) N i j... in terms of sums
  have hNA' : ∀ k l, ∑ m, N k m * A m l = if k = l then g else 0 := fun k l => by
    have := congrFun (congrFun hNA k) l
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, mul_ite] using this
  have hAN' : ∀ k l, ∑ m, A k m * N m l = if k = l then g else 0 := fun k l => by
    have := congrFun (congrFun hAN k) l
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, mul_ite] using this
  have L : ∑ k, ∑ l, N i k * (n * (a l - a k) * A k l) * N l j =
      n * (g * a i * N i j) - n * (g * a j * N i j) := by
    have h1 : ∑ k, ∑ l, N i k * (n * a l * A k l) * N l j = n * (g * a i * N i j) := by
      calc ∑ k, ∑ l, N i k * (n * a l * A k l) * N l j
          = ∑ l, n * a l * N l j * (∑ k, N i k * A k l) := by
            rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro l _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        _ = ∑ l, n * a l * N l j * (if i = l then g else 0) := by
            apply Finset.sum_congr rfl; intro l _; rw [hNA']
        _ = n * (g * a i * N i j) := by
            simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]; ring
    have h2 : ∑ k, ∑ l, N i k * (n * a k * A k l) * N l j = n * (g * a j * N i j) := by
      calc ∑ k, ∑ l, N i k * (n * a k * A k l) * N l j
          = ∑ k, n * a k * N i k * (∑ l, A k l * N l j) := by
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
        _ = ∑ k, n * a k * N i k * (if k = j then g else 0) := by
            apply Finset.sum_congr rfl; intro k _; rw [hAN']
        _ = n * (g * a j * N i j) := by
            simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]; ring
    rw [← h1, ← h2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  have Rr : ∑ k, ∑ l, N i k * (P l - P k) * N l j =
      (∑ k, N i k) * (∑ k, P k * N k j) - (∑ k, N i k * P k) * (∑ k, N k j) := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; ring
  rw [hs] at L
  rw [Rr] at L
  linear_combination L

/-- **Schur displacement identity.**  See the module docstring. -/
theorem schur_displacement (A N : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (D : Matrix κ κ R) (g n : R)
    (hAN : A * N = g • 1) (hNA : N * A = g • 1)
    (a P : ι → R) (xr Pr xc Pc : κ → R)
    (hA : ∀ i j, n * (a j - a i) * A i j = P j - P i)
    (hB : ∀ i y, n * (xc y - a i) * B i y = Pc y - P i)
    (hC : ∀ z i, n * (a i - xr z) * C z i = P i - Pr z)
    (hD : ∀ z y, n * (xc y - xr z) * D z y = Pc y - Pr z) (z y : κ) :
    g * (n * (xc y - xr z)) * (g * D z y - (C * N * B) z y) =
      (g - ∑ i, C z i * ∑ k, N i k) * (g * Pc y - ∑ j, (∑ k, P k * N k j) * B j y) -
      (g * Pr z - ∑ i, C z i * ∑ k, N i k * P k) * (g - ∑ j, (∑ k, N k j) * B j y) := by
  set U1 := ∑ i, C z i * ∑ k, N i k with hU1
  set UP := ∑ i, C z i * ∑ k, N i k * P k with hUP
  set W1 := ∑ j, (∑ k, N k j) * B j y with hW1
  set PW := ∑ j, (∑ k, P k * N k j) * B j y with hPW
  have hS : (C * N * B) z y = ∑ i, ∑ j, C z i * N i j * B j y := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have key : ∀ i j, g * (n * (xc y - xr z)) * (C z i * N i j * B j y) =
      (C z i * (∑ k, N i k * P k)) * ((∑ k, N k j) * B j y) -
        (C z i * (∑ k, N i k)) * ((∑ k, P k * N k j) * B j y) +
      (g * (Pc y * (C z i * N i j) - C z i * (N i j * P j)) +
      g * ((P i * N i j * B j y) - Pr z * (N i j * B j y))) := by
    intro i j
    have hB' : n * xc y * B j y = n * a j * B j y + Pc y - P j := by
      have := hB j y; linear_combination this
    have hC' : n * xr z * C z i = n * a i * C z i - P i + Pr z := by
      have := hC z i; linear_combination -this
    have hK := cleared_inverse_commutator A N g n hAN hNA a P hA i j
    linear_combination (g * C z i * N i j) * hB' - (g * N i j * B j y) * hC' +
      (C z i * B j y) * hK
  have f1 : ∑ i, ∑ j, (C z i * (∑ k, N i k * P k)) * ((∑ k, N k j) * B j y) = UP * W1 := by
    rw [hUP, hW1, Finset.sum_mul_sum]
  have f2 : ∑ i, ∑ j, (C z i * (∑ k, N i k)) * ((∑ k, P k * N k j) * B j y) = U1 * PW := by
    rw [hU1, hPW, Finset.sum_mul_sum]
  have f3 : ∑ i, ∑ j, g * (Pc y * (C z i * N i j) - C z i * (N i j * P j)) =
      g * (Pc y * U1 - UP) := by
    simp only [hU1, hUP, Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
  have f4 : ∑ i, ∑ j, g * ((P i * N i j * B j y) - Pr z * (N i j * B j y)) =
      g * (PW - Pr z * W1) := by
    rw [Finset.sum_comm]
    simp only [hPW, hW1, Finset.mul_sum, Finset.sum_mul, mul_sub, ← Finset.sum_sub_distrib]
  have hsum : g * (n * (xc y - xr z)) * (C * N * B) z y =
      UP * W1 - U1 * PW + (g * (Pc y * U1 - UP) + g * (PW - Pr z * W1)) := by
    rw [hS, Finset.mul_sum]
    simp_rw [Finset.mul_sum, key]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [f1, f2, f3, f4]
  have hD' : g * (n * (xc y - xr z)) * (g * D z y) = g * g * (Pc y - Pr z) := by
    have := hD z y; linear_combination (g * g) * this
  rw [mul_sub, hD', hsum]
  ring

end Generic

#print axioms cleared_inverse_commutator
#print axioms schur_displacement
end CatalanCore.Arith.Hybrid
