module

public import CatalanCore.ThmA.SStep
public import CatalanCore.Linalg.KrylovEigen

/-!
# Corollary kr for the Gram matrices `N_s`, `N_{s+1}`
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

lemma Nmat_transpose {F : Type*} [Field F] (K s : ℕ) : (Nmat F K s)ᵀ = Nmat F K s := by
  simp [Nmat, Matrix.transpose_mul]

/-- **Corollary kr**: if `u(K,s) ≠ 0` then `N_s` and `N_{s+1}` have no common eigenvalue in `F`
(for every `z`, one of `det(z + N_s)`, `det(z + N_{s+1})` is nonzero). -/
theorem no_common_root_of_krylov {F : Type*} [Field F] (K s : ℕ)
    (_hF : ∀ n : ℕ, 0 < n → n ≤ K + s + 1 → (n : F) ≠ 0) (hu : uK F K s ≠ 0) (z : F) :
    (z • (1 : Matrix (Fin K) (Fin K) F) + Nmat F K s).det ≠ 0 ∨
      (z • (1 : Matrix (Fin K) (Fin K) F) + Nmat F K (s + 1)).det ≠ 0 := by
  rw [Nmat_succ]
  exact CatalanCore.no_common_root_of_kdet_ne _ (Nmat_transpose K s) _ hu z

end CatalanCore.ThmA
