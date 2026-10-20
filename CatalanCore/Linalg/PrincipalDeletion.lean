module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

@[expose] public section

/-! # Principal deletion from simultaneous left/right kernel coordinates

No symmetry of the original matrix is needed. A coordinate set that detects
its right kernel and freely parameterizes its left kernel has an invertible
complementary principal minor.
-/

open Matrix

namespace CatalanCore.Linalg.PrincipalDeletion

variable {F : Type*} [Field F]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Block form: deleting the first coordinate set leaves a nonsingular matrix. -/
theorem det_complement_ne_zero (M : Matrix (I ⊕ J) (I ⊕ J) F)
    (hRight : ∀ v : (I ⊕ J) → F, M *ᵥ v = 0 → (∀ i, v (.inl i) = 0) → v = 0)
    (hLeft : ∀ a : I → F, ∃ w : (I ⊕ J) → F,
      M.transpose *ᵥ w = 0 ∧ ∀ i, w (.inl i) = a i) :
    (M.submatrix Sum.inr Sum.inr).det ≠ 0 := by
  have hk : ∀ v : J → F, (M.submatrix Sum.inr Sum.inr) *ᵥ v = 0 → v = 0 := by
    intro v hv
    let x : (I ⊕ J) → F := Sum.elim (fun _ => 0) v
    have hj : ∀ j, (M *ᵥ x) (.inr j) = 0 := by
      intro j
      have h := congrFun hv j
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, x] using h
    have hi : ∀ i, (M *ᵥ x) (.inl i) = 0 := by
      intro i
      obtain ⟨w, hw, hwi⟩ := hLeft (Pi.single i 1)
      have hz : w ⬝ᵥ (M *ᵥ x) = 0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hw]
        simp
      have he : w ⬝ᵥ (M *ᵥ x) = (M *ᵥ x) (.inl i) := by
        simp only [dotProduct, Fintype.sum_sum_type, hj, hwi, mul_zero,
          Finset.sum_const_zero, add_zero]
        simpa only [dotProduct, one_mul] using
          (single_dotProduct (fun j => (M *ᵥ x) (.inl j)) (1 : F) i)
      rwa [he] at hz
    have hx : x = 0 := hRight x (by ext (i | j); exact hi i; exact hj j) (fun _ => rfl)
    ext j
    exact congrFun hx (.inr j)
  have hinj : Function.Injective (M.submatrix Sum.inr Sum.inr).mulVec := by
    intro v w hvw
    have h := hk (v - w) (by rw [Matrix.mulVec_sub, hvw, sub_self])
    exact sub_eq_zero.mp h
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate-set form, with no choice of a block ordering in the statement. -/
theorem det_principal_compl_ne_zero (M : Matrix ι ι F) (s : Finset ι)
    (hRight : ∀ v : ι → F, M *ᵥ v = 0 → (∀ i ∈ s, v i = 0) → v = 0)
    (hLeft : ∀ a : s → F, ∃ w : ι → F,
      M.transpose *ᵥ w = 0 ∧ ∀ i : s, w i = a i) :
    (M.submatrix (Subtype.val : {i // i ∉ s} → ι) Subtype.val).det ≠ 0 := by
  let e : (s ⊕ {i // i ∉ s}) ≃ ι := Equiv.sumCompl (fun i => i ∈ s)
  let N := M.submatrix e e
  have hR : ∀ v : (s ⊕ {i // i ∉ s}) → F, N *ᵥ v = 0 →
      (∀ i, v (.inl i) = 0) → v = 0 := by
    intro v hv hvi
    let x : ι → F := fun i => v (e.symm i)
    have hMx : M *ᵥ x = 0 := by
      ext i
      have h := congrFun hv (e.symm i)
      simpa [N, Matrix.mulVec, dotProduct, x, ← Equiv.sum_comp e] using h
    have hx : x = 0 := hRight x hMx (fun i hi => by
      have h := hvi ⟨i, hi⟩
      simpa [x, e, Equiv.sumCompl_symm_apply_of_pos hi] using h)
    ext i
    have h := congrFun hx (e i)
    simpa [x] using h
  have hL : ∀ a : s → F, ∃ w : (s ⊕ {i // i ∉ s}) → F,
      N.transpose *ᵥ w = 0 ∧ ∀ i, w (.inl i) = a i := by
    intro a
    obtain ⟨w, hw, hwi⟩ := hLeft a
    refine ⟨w ∘ e, ?_, ?_⟩
    · ext i
      have h := congrFun hw (e i)
      simpa [N, Matrix.mulVec, dotProduct, ← Equiv.sum_comp e] using h
    · intro i
      exact hwi i
  have h := det_complement_ne_zero N hR hL
  simpa [N, e, Matrix.submatrix_submatrix, Function.comp_def] using h

end CatalanCore.Linalg.PrincipalDeletion

namespace CatalanCore.Linalg.PrincipalDeletion

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Type*} [AddCommGroup P] [Module F P]

/-- Shared polynomial-coordinate form. The left and right kernel coordinates
may have different nonzero coordinate weights. -/
theorem det_principal_compl_ne_zero_of_params (M : Matrix ι ι F) (s : Finset ι)
    (R L : P →ₗ[F] (ι → F)) (E : P →ₗ[F] (s → F))
    (a b : s → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hR : ∀ v : ι → F, M *ᵥ v = 0 → ∃ p, R p = v)
    (hL : ∀ p, M.transpose *ᵥ L p = 0)
    (hRc : ∀ p (i : s), R p i = a i * E p i)
    (hLc : ∀ p (i : s), L p i = b i * E p i)
    (hE : Function.Bijective E) :
    (M.submatrix (Subtype.val : {i // i ∉ s} → ι) Subtype.val).det ≠ 0 := by
  apply det_principal_compl_ne_zero M s
  · intro v hv hvi
    obtain ⟨p, hp⟩ := hR v hv
    have hEp : E p = 0 := by
      ext i
      have h := hvi i i.2
      rw [← hp, hRc] at h
      exact (mul_eq_zero.mp h).resolve_left (ha i)
    have hp0 : p = 0 := hE.1 (by simpa using hEp)
    rw [← hp, hp0, map_zero]
  · intro target
    obtain ⟨p, hp⟩ := hE.2 (fun i => target i / b i)
    refine ⟨L p, hL p, ?_⟩
    intro i
    rw [hLc, hp]
    field_simp [hb i]

end CatalanCore.Linalg.PrincipalDeletion

#print axioms CatalanCore.Linalg.PrincipalDeletion.det_principal_compl_ne_zero_of_params
