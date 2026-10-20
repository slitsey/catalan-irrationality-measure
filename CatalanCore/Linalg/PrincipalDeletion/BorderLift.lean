module

public import CatalanCore.Linalg.PrincipalDeletion.Rescue
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

namespace CatalanCore.Linalg.PrincipalDeletion
open Matrix
variable {F : Type*} [Field F] {A B P : Type*}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype P] [DecidableEq P]

/-- Every row of an annihilator of `U` is in the kernel spanned by `V`. -/
theorem annihilator_mulVec_eq_zero (U : Matrix A B F) (V : Matrix A P F)
    (hV : ∀ w, U.transpose *ᵥ w = 0 → ∃ p, V *ᵥ p = w)
    (Z : Matrix A A F) (hZ : Z * U = 0) (v : A → F)
    (hv : V.transpose *ᵥ v = 0) : Z *ᵥ v = 0 := by
  ext i
  have hr : U.transpose *ᵥ (fun a => Z i a) = 0 := by
    ext j
    have h := congrFun (congrFun hZ i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h
  obtain ⟨p, hp⟩ := hV _ hr
  change (fun a => Z i a) ⬝ᵥ v = 0
  rw [← hp, dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, hv]
  simp

/-- The canonical lift of low coordinates into a bordered kernel. -/
noncomputable def borderLift (M : Matrix A A F) (X Y : Matrix A B F)
    (V : Matrix A P F) : Matrix (A ⊕ B) P F :=
  Matrix.fromRows V (-((X.transpose * Y)⁻¹ * X.transpose * M * V))

theorem borderLift_mem (M : Matrix A A F) (X Y : Matrix A B F)
    (V W : Matrix A P F) (hGram : (X.transpose * Y).det ≠ 0)
    (hV : X.transpose * V = 0)
    (hW : ∀ w, Y.transpose *ᵥ w = 0 → ∃ p, W *ᵥ p = w)
    (p : P → F) (hp : (W.transpose * M * V) *ᵥ p = 0) :
    (Matrix.fromBlocks M Y X.transpose 0) *ᵥ (borderLift M X Y V *ᵥ p) = 0 := by
  let Z : Matrix A A F := 1 - Y * (X.transpose * Y)⁻¹ * X.transpose
  have hZY : Z * Y = 0 := by
    have hi := Matrix.nonsing_inv_mul (X.transpose * Y) (isUnit_iff_ne_zero.mpr hGram)
    simp only [Z, Matrix.sub_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one, sub_self]
  have hv : W.transpose *ᵥ (M *ᵥ (V *ᵥ p)) = 0 := by
    simpa only [← Matrix.mulVec_mulVec] using hp
  have hz := annihilator_mulVec_eq_zero Y W hW Z hZY _ hv
  have htop : M *ᵥ (V *ᵥ p) - Y *ᵥ ((X.transpose * Y)⁻¹ *ᵥ
      (X.transpose *ᵥ (M *ᵥ (V *ᵥ p)))) = 0 := by
    simpa only [Z, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] using hz
  ext (i | j)
  · simpa [borderLift, Matrix.fromRows_mulVec, Matrix.fromBlocks_mulVec,
      Matrix.neg_mulVec, Matrix.mulVec_neg, ← Matrix.mulVec_mulVec, sub_eq_add_neg] using congrFun htop i
  · simp [borderLift, Matrix.fromRows_mulVec, Matrix.fromBlocks_mulVec,
      Matrix.mulVec_mulVec, hV]

/-- Every bordered kernel vector has a parameter in the compressed kernel. -/
theorem borderLift_surj (M : Matrix A A F) (X Y : Matrix A B F)
    (V W : Matrix A P F) (hGram : (X.transpose * Y).det ≠ 0)
    (hV : ∀ v, X.transpose *ᵥ v = 0 → ∃ p, V *ᵥ p = v)
    (hW : W.transpose * Y = 0)
    (u : (A ⊕ B) → F) (hu : (Matrix.fromBlocks M Y X.transpose 0) *ᵥ u = 0) :
    ∃ p, (W.transpose * M * V) *ᵥ p = 0 ∧ borderLift M X Y V *ᵥ p = u := by
  let v : A → F := fun i => u (.inl i)
  let q : B → F := fun j => u (.inr j)
  have heu : u = Sum.elim v q := by ext (i | j) <;> rfl
  rw [heu, Matrix.fromBlocks_mulVec] at hu
  have htop : M *ᵥ v + Y *ᵥ q = 0 := by
    ext i; simpa using congrFun hu (.inl i)
  have hbot : X.transpose *ᵥ v = 0 := by
    ext j; simpa using congrFun hu (.inr j)
  obtain ⟨p, hp⟩ := hV v hbot
  have hcomp : (W.transpose * M * V) *ᵥ p = 0 := by
    have ht := congrArg (fun w => W.transpose *ᵥ w) htop
    simpa [Matrix.mulVec_add, Matrix.mulVec_mulVec, hW, ← hp,
      Matrix.mul_assoc] using ht
  have hqi : (X.transpose * Y)⁻¹ *ᵥ (X.transpose *ᵥ (Y *ᵥ q)) = q := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hGram), Matrix.one_mulVec]
  have hq : q = -((X.transpose * Y)⁻¹ *ᵥ (X.transpose *ᵥ (M *ᵥ v))) := by
    have ht := congrArg (fun w => (X.transpose * Y)⁻¹ *ᵥ (X.transpose *ᵥ w)) htop
    simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at ht
    rw [hqi] at ht
    exact eq_neg_of_add_eq_zero_right ht
  refine ⟨p, hcomp, ?_⟩
  rw [heu]
  ext (i | j)
  · simpa [borderLift, Matrix.fromRows_mulVec] using congrFun hp i
  · simpa [borderLift, Matrix.fromRows_mulVec, Matrix.neg_mulVec,
      ← Matrix.mulVec_mulVec, hp] using congrFun hq.symm j

end CatalanCore.Linalg.PrincipalDeletion

#print axioms CatalanCore.Linalg.PrincipalDeletion.borderLift_surj
