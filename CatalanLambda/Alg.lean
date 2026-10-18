module

public import CatalanLambda.Cauchy

@[expose] public section

open Finset Matrix

namespace CatalanLambda

variable {p : ℕ} [Fact p.Prime]

/-- The `K × s` matrix `C_s = [1/(a+j)]`, `0 ≤ a < K`, `1 ≤ j ≤ s`. -/
def Cm (p K s : ℕ) [Fact p.Prime] : Matrix (Fin K) (Fin s) (ZMod p) :=
  Matrix.of fun a j => (1 : ZMod p) / (((a : ℕ) : ZMod p) + 1 + ((j : ℕ) : ZMod p))

lemma det_swap {K s : ℕ} (y : ZMod p) (hy : y ≠ 0) (C : Matrix (Fin K) (Fin s) (ZMod p)) :
    (y • (1 : Matrix (Fin K) (Fin K) (ZMod p)) + C * Cᵀ).det =
      y ^ K * (y⁻¹) ^ s * (y • (1 : Matrix (Fin s) (Fin s) (ZMod p)) + Cᵀ * C).det := by
  have e1 : y • (1 : Matrix (Fin K) (Fin K) (ZMod p)) + C * Cᵀ =
      y • (1 + (y⁻¹ • C) * Cᵀ) := by
    rw [smul_add, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hy, one_smul]
  have e2 : (1 : Matrix (Fin s) (Fin s) (ZMod p)) + Cᵀ * (y⁻¹ • C) =
      y⁻¹ • (y • (1 : Matrix (Fin s) (Fin s) (ZMod p)) + Cᵀ * C) := by
    rw [smul_add, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hy, one_smul]
  rw [e1, Matrix.det_smul, Matrix.det_one_add_mul_comm, e2, Matrix.det_smul]
  simp [mul_assoc]

lemma sum_telescope (n : ℕ) (hn : n + 1 < p) :
    ∑ a ∈ range n, (1 : ZMod p) / ((((a : ℕ) : ZMod p) + 1) * (((a : ℕ) : ZMod p) + 2)) =
      (n : ZMod p) / ((n : ZMod p) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 : ((n : ZMod p) + 1) ≠ 0 := by
      have := natCast_ne_zero' (p := p) (a := n + 1) (by omega) (by omega)
      simpa using this
    have h2 : ((n : ZMod p) + 2) ≠ 0 := by
      have := natCast_ne_zero' (p := p) (a := n + 2) (by omega) (by omega)
      simpa using this
    have h3 : ((n : ZMod p) + 1 + 1) ≠ 0 := by rw [add_assoc, one_add_one_eq_two]; exact h2
    push_cast
    field_simp
    ring

/-- The algebraic core: the three determinants cannot all vanish. -/
theorem no_triple (K : ℕ) (hK : 2 ≤ K) (hKp : 2 * K ≤ p) (hKp1 : K + 1 < p) (y : ZMod p)
    (h1 : (y • (1 : Matrix (Fin K) (Fin K) (ZMod p)) + Cm p K 1 * (Cm p K 1)ᵀ).det = 0)
    (h2 : (y • (1 : Matrix (Fin K) (Fin K) (ZMod p)) + Cm p K 2 * (Cm p K 2)ᵀ).det = 0)
    (h3 : (y • (1 : Matrix (Fin K) (Fin K) (ZMod p)) + Cm p K K * (Cm p K K)ᵀ).det = 0) :
    False := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add, Matrix.det_mul, Matrix.det_transpose] at h3
    have hc : (Cm p K K).det ≠ 0 := cauchy_det_ne p K hKp
    exact hc (mul_self_eq_zero.1 h3)
  rw [det_swap y hy] at h1 h2
  have hyK : y ^ K * (y⁻¹) ^ 1 ≠ 0 := by simp [hy]
  have hyK2 : y ^ K * (y⁻¹) ^ 2 ≠ 0 := by simp [hy]
  have d1 := (mul_eq_zero.1 h1).resolve_left hyK
  have d2 := (mul_eq_zero.1 h2).resolve_left hyK2
  rw [Matrix.det_fin_one] at d1
  rw [Matrix.det_fin_two] at d2
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.mul_apply, Matrix.transpose_apply, Cm, Matrix.of_apply, Fin.sum_univ_succ] at d1 d2
  simp [Matrix.one_apply] at d1 d2
  have hG : ∑ x : Fin K, ((((x : ℕ) : ZMod p) + 1)⁻¹ * (((x : ℕ) : ZMod p) + 1 + 1)⁻¹) =
      (K : ZMod p) / ((K : ZMod p) + 1) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun a => (((a : ℕ) : ZMod p) + 1)⁻¹ * (((a : ℕ) : ZMod p) + 1 + 1)⁻¹) K,
      ← sum_telescope K hKp1]
    apply Finset.sum_congr rfl
    intro a _
    have : ((a : ℕ) : ZMod p) + 1 + 1 = (a : ZMod p) + 2 := by ring
    rw [this, one_div, mul_inv]
  have hG' : ∑ x : Fin K, ((((x : ℕ) : ZMod p) + 1 + 1)⁻¹ * (((x : ℕ) : ZMod p) + 1)⁻¹) =
      (K : ZMod p) / ((K : ZMod p) + 1) := by
    rw [← hG]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [hG', d1, zero_mul, zero_sub, neg_eq_zero, hG, mul_self_eq_zero, div_eq_zero_iff] at d2
  have hK0 : (K : ZMod p) ≠ 0 := natCast_ne_zero' (by omega) (by omega)
  have hK1 : (K : ZMod p) + 1 ≠ 0 := by
    have := natCast_ne_zero' (p := p) (a := K + 1) (by omega) hKp1
    simpa using this
  rcases d2 with h | h
  · exact hK0 h
  · exact hK1 h

end CatalanLambda
