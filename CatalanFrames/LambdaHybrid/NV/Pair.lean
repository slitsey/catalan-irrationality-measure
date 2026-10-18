module

public import CatalanFrames.LambdaHybrid.NV.NoCommon

/-!
# The member pair: bordered no-common-root lemma (DO Lemma 2.2 + boundary value)

Member 1 has Cauchy-type columns `G₁ : A × Fin (s+1)` (the last one, `g = Fin.last s`, is the
absent node that member 2 moves into `C`); member 2 has `G₂ = G₁` with the last column deleted.
The borders `X, Y : A × Fin m` are the same for both members.

* `dual_submatrix`: `D₂(z)` is the minor of `D₁(z)` obtained by deleting row/column `g`.
* `common_root_krylov`: if `Γ̂₁` is invertible and `B₁(z) = B₂(z) = 0` for some `z ≠ 0`, then
  `k_R = 0` or `k_L = 0`.
* `pair_krylov`: the full statement including `z = 0` (boundary value): if both
  `det[G₁ Y]`, `det[G₁ X]` (the two `K × K` Cauchy determinants) are nonzero and
  `B₁(z₀) = B₂(z₀) = 0`, then `k_R = 0` or `k_L = 0`.
-/

@[expose] public section

open Matrix CatalanCore

namespace CatalanFrames.LambdaHybrid.NV

variable {F : Type*} [Field F] {A : Type*} [Fintype A] [DecidableEq A] {s m : ℕ}

/-- Member 2's columns: delete the last column of `G₁`. -/
def dropLast (G : Matrix A (Fin (s + 1)) F) : Matrix A (Fin s) F :=
  G.submatrix id Fin.castSucc

lemma dual_submatrix (z : F) (G : Matrix A (Fin (s + 1)) F) (X Y : Matrix A (Fin m) F) :
    dual z (dropLast G) X Y =
      (dual z G X Y).submatrix (Sum.map Fin.castSucc id) (Sum.map Fin.castSucc id) := by
  ext (i | i) (j | j) <;>
    simp [dual, Eblk, gramHat_eq, dropLast, Matrix.mul_apply, Matrix.one_apply,
      Matrix.fromBlocks, Matrix.submatrix_apply]

/-- **Lemma 2.2 (bordered no common root, `z ≠ 0`).** -/
theorem common_root_krylov {z : F} (hz : z ≠ 0) (G : Matrix A (Fin (s + 1)) F)
    (X Y : Matrix A (Fin m) F) (hΓ : IsUnit (gramHat G X Y).det)
    (h1 : (bordered z G X Y).det = 0) (h2 : (bordered z (dropLast G) X Y).det = 0) :
    kR (gramHat G X Y) (Fin.last s) = 0 ∨ kL (gramHat G X Y) (Fin.last s) = 0 := by
  rw [bordered_det_eq_zero_iff hz] at h1 h2
  rw [dual_submatrix] at h2
  have hf : Function.Injective (Sum.map (Fin.castSucc : Fin s → Fin (s + 1)) (id : Fin m → Fin m)) :=
    Function.Injective.sumMap (Fin.castSucc_injective _) Function.injective_id
  rcases exists_kernel_of_minor (dual z G X Y) (Sum.inl (Fin.last s)) _ hf
    (by rintro (k | k) <;> simp [Fin.castSucc_ne_last]) (by
      rintro (i | i) hi
      · have : i ≠ Fin.last s := fun h => hi (by rw [h])
        obtain ⟨a, ha⟩ := Fin.exists_castSucc_eq.2 this
        exact ⟨Sum.inl a, by simp [ha]⟩
      · exact ⟨Sum.inr i, by simp⟩) h1 h2 with ⟨x, hx0, hxg, hx⟩ | ⟨y, hy0, hyg, hy⟩
  · exact Or.inl (kR_eq_zero_of_right _ hΓ hz _ x hx0 hxg hx)
  · exact Or.inr (kL_eq_zero_of_left _ hΓ hz _ y hy0 hyg hy)

/-- `det Γ̂ = det[G X] · det[G Y]` for `e : g ⊕ m ≃ A`. -/
lemma det_gramHat {g : Type*} [Fintype g] [DecidableEq g] {m : Type*} [Fintype m] [DecidableEq m]
    (G : Matrix A g F) (X Y : Matrix A m F) (e : g ⊕ m ≃ A) :
    (gramHat G X Y).det = ((fromCols G X).submatrix e id).det * ((fromCols G Y).submatrix e id).det := by
  rw [← Matrix.det_transpose ((fromCols G X).submatrix e id), ← Matrix.det_mul]
  congr 1
  ext i j
  simp only [gramHat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id]
  exact (Equiv.sum_comp e (fun a => (fromCols G X) a i * (fromCols G Y) a j)).symm

/-- **The deliverable core (abstract).**  `e : Fin (s+1) ⊕ Fin m ≃ A` says `|G| + m = K` for
member 1.  If the two Cauchy determinants are nonzero and both bordered determinants vanish at
some `z₀ ∈ F`, then `k_R = 0` or `k_L = 0`. -/
theorem pair_krylov (G : Matrix A (Fin (s + 1)) F) (X Y : Matrix A (Fin m) F)
    (e : Fin (s + 1) ⊕ Fin m ≃ A)
    (hY : ((fromCols G Y).submatrix e id).det ≠ 0) (hX : ((fromCols G X).submatrix e id).det ≠ 0)
    (z₀ : F) (h1 : (bordered z₀ G X Y).det = 0) (h2 : (bordered z₀ (dropLast G) X Y).det = 0) :
    kR (gramHat G X Y) (Fin.last s) = 0 ∨ kL (gramHat G X Y) (Fin.last s) = 0 := by
  by_cases hz : z₀ = 0
  · subst hz
    exact absurd h1 (det_bordered_zero_ne_zero G X Y e hY hX)
  · refine common_root_krylov hz G X Y ?_ h1 h2
    rw [det_gramHat G X Y e]
    exact (isUnit_iff_ne_zero.2 (mul_ne_zero hX hY))

end CatalanFrames.LambdaHybrid.NV
