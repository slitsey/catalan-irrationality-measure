module

public import CatalanArchive.CatalanCore.Linalg.PrincipalDeletion.BorderLift

@[expose] public section

namespace CatalanCore.Linalg.PrincipalDeletion
open Matrix
variable {F : Type*} [Field F] {A B P : Type*}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype P] [DecidableEq P]

/-- Kernel compression with common left/right evaluation coordinates gives a
nonsingular principal minor by deleting precisely the compressed nullity. -/
theorem exists_bordered_principal_compl_ne_zero
    (M : Matrix A A F) (X Y : Matrix A B F) (V W E : Matrix A P F)
    (a b : A → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hGram : (X.transpose * Y).det ≠ 0)
    (hVzero : X.transpose * V = 0) (hWzero : Y.transpose * W = 0)
    (hVspan : ∀ v, X.transpose *ᵥ v = 0 → ∃ p, V *ᵥ p = v)
    (hWspan : ∀ v, Y.transpose *ᵥ v = 0 → ∃ p, W *ᵥ p = v)
    (hSym : (W.transpose * M * V).transpose = W.transpose * M * V)
    (hVE : ∀ p i, (V *ᵥ p) i = a i * (E *ᵥ p) i)
    (hWE : ∀ p i, (W *ᵥ p) i = b i * (E *ᵥ p) i)
    (hE : Function.Injective E.mulVecLin) :
    ∃ s : Finset A, s.card = Module.finrank F (LinearMap.ker (W.transpose * M * V).mulVecLin) ∧
      ((Matrix.fromBlocks M Y X.transpose 0).submatrix
        (Subtype.val : {i // i ∉ s.image Sum.inl} → A ⊕ B) Subtype.val).det ≠ 0 := by
  let K := W.transpose * M * V
  let U := LinearMap.ker K.mulVecLin
  let R : U →ₗ[F] ((A ⊕ B) → F) := (borderLift M X Y V).mulVecLin.comp U.subtype
  let Q : U →ₗ[F] ((A ⊕ B) → F) := (borderLift M.transpose Y X W).mulVecLin.comp U.subtype
  let Ev : U →ₗ[F] (A → F) := E.mulVecLin.comp U.subtype
  have hGt : (Y.transpose * X).det ≠ 0 := by
    have he : Y.transpose * X = (X.transpose * Y).transpose := by simp
    rw [he, Matrix.det_transpose]
    exact hGram
  have hWtY : W.transpose * Y = 0 := by
    simpa using congrArg Matrix.transpose hWzero
  have hK : ∀ p : U, K *ᵥ p.val = 0 := fun p => p.2
  refine exists_principal_compl_ne_zero (Matrix.fromBlocks M Y X.transpose 0)
    Sum.inl Sum.inl_injective R Q Ev a b ha hb ?_ ?_ ?_ ?_ ?_
  · intro u hu
    obtain ⟨p, hp, hpu⟩ := borderLift_surj M X Y V W hGram hVspan hWtY u hu
    exact ⟨⟨p, hp⟩, hpu⟩
  · intro p
    have hp : (V.transpose * M.transpose * W) *ᵥ p.val = 0 := by
      have htrans : V.transpose * M.transpose * W = K := by
        simpa [K, Matrix.transpose_mul, Matrix.mul_assoc] using hSym
      rw [htrans]
      exact hK p
    have hq := borderLift_mem M.transpose Y X W V hGt hWzero hVspan p.val hp
    simpa [Q, Matrix.fromBlocks_transpose] using hq
  · intro p i
    simpa [R, Ev, borderLift, Matrix.fromRows_mulVec] using hVE p.val i
  · intro p i
    simpa [Q, Ev, borderLift, Matrix.fromRows_mulVec] using hWE p.val i
  · intro p q hpq
    apply Subtype.ext
    exact hE hpq

/-- The complement of deleted low coordinates keeps every border coordinate. -/
def lowComplEquiv (s : Finset A) : ({a // a ∉ s} ⊕ B) ≃
    {i : A ⊕ B // i ∉ s.image Sum.inl} where
  toFun
    | .inl a => ⟨.inl a, by simpa using a.2⟩
    | .inr b => ⟨.inr b, by simp⟩
  invFun := by
    rintro ⟨a | b, hi⟩
    · exact .inl ⟨a, by simpa using hi⟩
    · exact .inr b
  left_inv := by rintro (a | b) <;> rfl
  right_inv := by rintro ⟨a | b, h⟩ <;> rfl

theorem det_low_compl_eq (M : Matrix (A ⊕ B) (A ⊕ B) F) (s : Finset A) :
    (M.submatrix (Subtype.val : {i // i ∉ s.image Sum.inl} → A ⊕ B) Subtype.val).det =
      (M.submatrix (Sum.map (Subtype.val : {a // a ∉ s} → A) id)
        (Sum.map (Subtype.val : {a // a ∉ s} → A) id)).det := by
  rw [← Matrix.det_submatrix_equiv_self (lowComplEquiv (B := B) s)]
  congr 1
  ext (a | b) (c | d) <;> rfl

end CatalanCore.Linalg.PrincipalDeletion
#print axioms CatalanCore.Linalg.PrincipalDeletion.exists_bordered_principal_compl_ne_zero
