module

public import CatalanCore.Linalg.KrylovV2

/-!
# Bordered chain with a projector (package H4)

`bkdet_chain_proj`: if `P` is a projector killing `range W` that commutes with `T`, and `c_j` is a
chain with `T c_j = l_j c_{j+1} + (lower) + (range W)`, then
`u(T, P c_0) = (∏_k ∏_{j<k} l_j) · det [W | c_0, …, c_{n-1}]`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {m n : ℕ}

theorem bkdet_chain_proj {W : Matrix (Fin (m + n)) (Fin m) F}
    {T P : Matrix (Fin (m + n)) (Fin (m + n)) F}
    (hT : ∀ x ∈ Wsp W, T *ᵥ x ∈ Wsp W) (hPW : ∀ x ∈ Wsp W, P *ᵥ x = 0)
    (hPc : ∀ x, ∃ a : Fin m → F, P *ᵥ x = x - W *ᵥ a) (hcomm : T * P = P * T)
    (c : ℕ → Fin (m + n) → F) (l : ℕ → F)
    (hc : ∀ j, j + 1 < n → ∃ a b : F, ∃ w ∈ Wsp W,
      T *ᵥ c j = l j • c (j + 1) + a • c j + b • c (j - 1) + w) :
    bkdet W T (P *ᵥ c 0) = (∏ k : Fin n, ∏ j ∈ Finset.range k, l j) *
      (bmat W (Matrix.of fun i (j : Fin n) => c j i)).det := by
  set v : ℕ → Fin (m + n) → F := fun j => P *ᵥ c j with hv
  have hvmem : ∀ j i, i ≤ j → v i ∈ Submodule.span F (bcol W v '' Set.Iio (m + (j + 1))) := by
    intro j i hij
    exact Submodule.subset_span ⟨m + i, by simp; omega, by simp [bcol_add]⟩
  have h1 := bkdet_chain (W := W) hT v l (by
    intro j hj
    obtain ⟨a, b, w, hwm, hw⟩ := hc j hj
    have e : T *ᵥ v j = P *ᵥ (T *ᵥ c j) := by
      simp only [hv, Matrix.mulVec_mulVec, hcomm]
    have e2 : T *ᵥ v j - l j • v (j + 1) = a • v j + b • v (j - 1) := by
      rw [e, hw]
      simp only [hv, Matrix.mulVec_add, Matrix.mulVec_smul, hPW w hwm]
      abel
    rw [e2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hvmem j j le_rfl))
      (Submodule.smul_mem _ _ (hvmem j (j - 1) (by omega))))
  have h0 : v 0 = P *ᵥ c 0 := rfl
  rw [← h0, h1]
  congr 1
  -- det of the projected chain
  choose a ha using fun j : ℕ => hPc (c j)
  have hcm : colMat (bcol W v) = bmat W (Matrix.of fun i (j : Fin n) => v j i) := by
    ext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [bmat, colMat, bcol]
    · simp [bmat, colMat, bcol]
  rw [hcm]
  have hE : (Matrix.of fun i (j : Fin n) => v j i) =
      (Matrix.of fun i (j : Fin n) => c j i) * (1 : Matrix (Fin n) (Fin n) F) +
        W * (Matrix.of fun r (j : Fin n) => -(a j r)) := by
    ext i j
    have := congrFun (ha j) i
    simp only [hv, Matrix.of_apply, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
    rw [this]
    simp [Matrix.mulVec, dotProduct, sub_eq_add_neg, mul_neg, Finset.sum_neg_distrib]
  rw [hE, det_bmat_comb]
  simp

end CatalanCore
