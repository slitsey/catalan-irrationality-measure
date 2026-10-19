module

public import CatalanCore.Linalg.KrylovV2
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Transfer of bordered Krylov determinants along an intertwiner (package H5, "Transfer")

* `bkdet_transfer`: if `B₂ Φ = Φ B_y` for an `(m+n) × n` matrix `Φ`, then
  `u(B₂, Φ z) = det [W | Φ] · u_y(B_y, z)`.
* `bkdet_add_smul_one`: `u(T + β, v) = u(T, v)`.
* `mul_eq_of_mulVec`: matrix equality from vector equality.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F]

lemma mul_eq_of_mulVec {r c : ℕ} (M N : Matrix (Fin r) (Fin c) F)
    (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem bkdet_transfer {m n : ℕ} (W : Matrix (Fin (m + n)) (Fin m) F)
    (Φ : Matrix (Fin (m + n)) (Fin n) F) (B2 : Matrix (Fin (m + n)) (Fin (m + n)) F)
    (By : Matrix (Fin n) (Fin n) F) (hΦ : B2 * Φ = Φ * By) (z : Fin n → F) :
    bkdet W B2 (Φ *ᵥ z) = (bmat W Φ).det * kdet By z := by
  have hpow : ∀ k : ℕ, B2 ^ k * Φ = Φ * By ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hΦ, Matrix.mul_assoc,
        pow_succ']
  have h : krylovE B2 (Φ *ᵥ z) = Φ * krylov By z + W * (0 : Matrix (Fin m) (Fin n) F) := by
    ext i k
    simp only [krylovE, Matrix.of_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, krylov,
      Matrix.zero_apply]
    have := congrArg (fun M => (M *ᵥ z) i) (hpow k)
    simp only [← Matrix.mulVec_mulVec] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply]
  unfold bkdet
  rw [h, det_bmat_comb]
  simp [kdet, mul_comm]

lemma shift_pow_exists {N : ℕ} (T : Matrix (Fin N) (Fin N) F) (β : F) (v : Fin N → F) (k : ℕ) :
    ∃ c : ℕ → F, c k = 1 ∧ (∀ j, k < j → c j = 0) ∧
      ((T + β • (1 : Matrix (Fin N) (Fin N) F)) ^ k) *ᵥ v =
        ∑ j ∈ Finset.range (k + 1), c j • (T ^ j *ᵥ v) := by
  induction k with
  | zero => exact ⟨fun j => if j = 0 then 1 else 0, by simp, fun j hj => by simp; omega, by simp⟩
  | succ k ih =>
    obtain ⟨c, hk, hz, h⟩ := ih
    refine ⟨fun j => (if j = 0 then 0 else c (j - 1)) + β * c j, ?_, ?_, ?_⟩
    · simp [hk, hz (k + 1) (by omega)]
    · intro j hj
      show (if j = 0 then 0 else c (j - 1)) + β * c j = 0
      rw [if_neg (by omega), hz (j - 1) (by omega), hz j (by omega)]; simp
    · rw [pow_succ', ← Matrix.mulVec_mulVec, h, Matrix.mulVec_sum]
      have e1 : ∀ j, (T + β • (1 : Matrix (Fin N) (Fin N) F)) *ᵥ (c j • (T ^ j *ᵥ v)) =
          c j • (T ^ (j + 1) *ᵥ v) + (β * c j) • (T ^ j *ᵥ v) := by
        intro j
        rw [Matrix.mulVec_smul, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          pow_succ', ← Matrix.mulVec_mulVec]
        simp only [smul_add, mul_smul]
        rw [smul_comm]
      simp only [e1, Finset.sum_add_distrib]
      simp only [add_smul, Finset.sum_add_distrib]
      rw [Finset.sum_range_succ' (fun j => (if j = 0 then (0 : F) else c (j - 1)) • (T ^ j *ᵥ v))]
      rw [Finset.sum_range_succ (fun j => (β * c j) • (T ^ j *ᵥ v)) (k + 1), hz (k + 1) (by omega)]
      simp

/-- Shifting the operator by a scalar does not change the bordered Krylov determinant. -/
theorem bkdet_add_smul_one {m n : ℕ} (W : Matrix (Fin (m + n)) (Fin m) F)
    (T : Matrix (Fin (m + n)) (Fin (m + n)) F) (β : F) (v : Fin (m + n) → F) :
    bkdet W (T + β • (1 : Matrix (Fin (m + n)) (Fin (m + n)) F)) v = bkdet W T v := by
  choose c hc1 hc0 hc using fun k : ℕ => shift_pow_exists T β v k
  set M : Matrix (Fin n) (Fin n) F := Matrix.of fun j k => c (k : ℕ) (j : ℕ) with hM
  have h : krylovE (T + β • (1 : Matrix (Fin (m + n)) (Fin (m + n)) F)) v =
      krylovE T v * M + W * (0 : Matrix (Fin m) (Fin n) F) := by
    ext i k
    simp only [krylovE, Matrix.of_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply]
    have := congrFun (hc k) i
    rw [this]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, hM]
    have hsub : ∑ j ∈ Finset.range ((k : ℕ) + 1), c k j * (T ^ j *ᵥ v) i =
        ∑ j : Fin n, (T ^ (j : ℕ) *ᵥ v) i * c k j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (T ^ j *ᵥ v) i * c k j) n]
      rw [Finset.sum_subset (Finset.range_subset_range.2 (by have := k.2; omega : (k : ℕ) + 1 ≤ n))
        (fun j hj hj' => by
          simp only [Finset.mem_range] at hj hj'
          rw [hc0 k j (by omega)]; simp)]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact hsub
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · simp [hM, hc1]
    · intro i j hij
      simp only [hM, Matrix.of_apply]
      exact hc0 j i hij
  unfold bkdet
  rw [h, det_bmat_comb, hdet, one_mul]

end CatalanCore
