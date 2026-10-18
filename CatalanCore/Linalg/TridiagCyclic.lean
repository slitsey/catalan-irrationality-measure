module

public import CatalanCore.Linalg.KrylovTri
public import CatalanCore.Linalg.Tridiag

/-!
# Cyclicity of `e₀` for an irreducible tridiagonal matrix

If all off-diagonal entries `up j` (`j + 1 < n`) of `tri n up d` are nonzero, then
`kdet (tri n up d) e₀ ≠ 0`, i.e. `e₀` is a cyclic vector.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {n : ℕ}

/-- The standard basis vector `e_j` (zero if `j ≥ n`). -/
def ev (n : ℕ) (j : ℕ) : Fin n → F := fun i => if (i : ℕ) = j then 1 else 0

lemma colMat_ev : colMat (fun j => ev (F := F) n j) = 1 := by
  ext i k
  simp only [colMat, ev, Matrix.of_apply, Matrix.one_apply]
  by_cases h : i = k
  · simp [h]
  · have h2 : (k : ℕ) ≠ i := fun h' => h (Fin.ext h'.symm)
    have h3 : (i : ℕ) ≠ k := fun h' => h (Fin.ext h')
    simp [h, h3]

lemma tri_mulVec_ev (up d : ℕ → F) (j : ℕ) (hj : j < n) :
    tri n up d *ᵥ ev n j - up j • ev n (j + 1) =
      d j • ev n j + (if 0 < j then up (j - 1) • ev n (j - 1) else 0) := by
  ext i
  have h1 : (tri n up d *ᵥ ev n j) i = tri n up d i ⟨j, hj⟩ := by
    simp only [Matrix.mulVec, dotProduct, ev]
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro m _ hm
      have : (m : ℕ) ≠ j := fun h => hm (Fin.ext h)
      simp [this]
    · simp
  by_cases hj0 : 0 < j
  · simp only [hj0, ite_true, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, h1, tri_apply, ev, smul_eq_mul]
    split_ifs <;> try (exfalso; omega)
    all_goals first | ring1 | (have e : (i : ℕ) = j := (by omega); rw [e]; ring1) | (have e : (i : ℕ) = j - 1 := (by omega); rw [e]; ring1)
  · simp only [hj0, ite_false, add_zero, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, h1, tri_apply, ev, smul_eq_mul, Pi.zero_apply]
    split_ifs <;> try (exfalso; omega)
    all_goals first | ring1 | (have e : (i : ℕ) = j := (by omega); rw [e]; ring1)

theorem kdet_tri_ev_ne_zero (up d : ℕ → F) (hup : ∀ j, j + 1 < n → up j ≠ 0) :
    kdet (tri n up d) (ev n 0) ≠ 0 := by
  rw [kdet_chain (tri n up d) (fun j => ev n j) up]
  · rw [colMat_ev, Matrix.det_one, mul_one]
    refine Finset.prod_ne_zero_iff.2 fun k _ => Finset.prod_ne_zero_iff.2 fun j hj => hup j ?_
    have := k.2
    simp at hj
    omega
  · intro j hj
    rw [tri_mulVec_ev up d j (by omega)]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, by simp, rfl⟩)) ?_
    split_ifs with h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j - 1, by simp, rfl⟩)
    · exact Submodule.zero_mem _

/-- Explicit form of `u(T, e₀)` for a tridiagonal matrix. -/
theorem kdet_tri_ev_eq (up d : ℕ → F) :
    kdet (tri n up d) (ev n 0) = ∏ k : Fin n, ∏ j ∈ Finset.range (k : ℕ), up j := by
  rw [kdet_chain (tri n up d) (fun j => ev n j) up]
  · rw [colMat_ev, Matrix.det_one, mul_one]
  · intro j hj
    rw [tri_mulVec_ev up d j (by omega)]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, by simp, rfl⟩)) ?_
    split_ifs with h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j - 1, by simp, rfl⟩)
    · exact Submodule.zero_mem _

end CatalanCore
