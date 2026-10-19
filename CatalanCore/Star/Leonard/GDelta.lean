module

public import CatalanCore.Star.Leonard.KStepKS
public import CatalanCore.Star.Leonard.DeltaCB
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# `G · Δ = Num` (package H6, Schur step)

`G = det[z_0, …, z_{S-1}] = det (Rᵀ Π B)` with `B = [c_0, c_{-1}, …, c_{-(S-1)}]`, and
`Δ = det (W_Xᵀ W_Y)`.  Then `G · Δ = det (C_Aᵀ C_B)` with `C_A = [R | W_X]`, `C_B = [B | W_Y]`
(`K × (S + m)` Cauchy matrices): the Schur complement of the block matrix.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

section GD

variable [CharZero F] (m n S : ℕ) (θ : F)

/-- `B = [c_0, c_{-1}, …, c_{-(S-1)}]`. -/
noncomputable def Bm : Matrix (Fin (m + n)) (Fin S) F :=
  Matrix.of fun a k => wcol (m + n) θ (-((k : ℕ) : ℤ)) a

lemma G_eq_det : (CatalanCore.colMat fun j => zvec m n S θ j) =
    (Rm m n S θ)ᵀ * projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) * Bm m n S θ := by
  ext i k
  simp [CatalanCore.colMat, zvec, Matrix.mul_apply, Matrix.mulVec, dotProduct, Bm,
    Matrix.mul_assoc]

/-- `C_A = [R | W_X]` and `C_B = [B | W_Y]` as `K × (S+m)` matrices. -/
noncomputable def CA : Matrix (Fin (m + n)) (Fin (S + m)) F :=
  Matrix.of fun a j => Fin.addCases (fun j' : Fin S => Rm m n S θ a j')
    (fun i : Fin m => Wb (m + n) θ (bX m (S : ℤ)) a i) j

noncomputable def CB : Matrix (Fin (m + n)) (Fin (S + m)) F :=
  Matrix.of fun a j => Fin.addCases (fun j' : Fin S => Bm m n S θ a j')
    (fun i : Fin m => Wb (m + n) θ (bY m (S : ℤ)) a i) j

theorem G_mul_Delta
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    (CatalanCore.colMat fun j => zvec m n S θ j).det *
        ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det =
      ((CA m n S θ)ᵀ * CB m n S θ).det := by
  set WX := Wb (m + n) θ (bX m (S : ℤ)) with hWX
  set WY := Wb (m + n) θ (bY m (S : ℤ)) with hWY
  set R := Rm m n S θ with hR
  set B := Bm m n S θ with hB
  have hblock : (CA m n S θ)ᵀ * CB m n S θ = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (Rᵀ * B) (Rᵀ * WY) (WXᵀ * B) (WXᵀ * WY)) := by
    ext i j
    induction i using Fin.addCases with
    | left i' =>
      induction j using Fin.addCases with
      | left j' => simp [CA, CB, Matrix.mul_apply, Matrix.fromBlocks, hR, hB, hWX, hWY]
      | right j' => simp [CA, CB, Matrix.mul_apply, Matrix.fromBlocks, hR, hB, hWX, hWY]
    | right i' =>
      induction j using Fin.addCases with
      | left j' => simp [CA, CB, Matrix.mul_apply, Matrix.fromBlocks, hR, hB, hWX, hWY]
      | right j' => simp [CA, CB, Matrix.mul_apply, Matrix.fromBlocks, hR, hB, hWX, hWY]
  haveI : Invertible (WXᵀ * WY) := Matrix.invertibleOfIsUnitDet _ hΔ
  rw [hblock, Matrix.det_reindex_self, Matrix.det_fromBlocks₂₂, mul_comm]
  congr 1
  rw [G_eq_det]
  unfold projB
  rw [Matrix.invOf_eq_nonsing_inv]
  congr 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rfl


/-- The node shifts of the columns of `C_A` / `C_B`. -/
noncomputable def asv : Fin (S + m) → F :=
  Fin.addCases (fun j' : Fin S => θ + (((j' : ℕ) + 1 : ℕ) : ℤ))
    (fun i : Fin m => θ + ((bX m (S : ℤ) i : ℤ) : F))

noncomputable def bsv : Fin (S + m) → F :=
  Fin.addCases (fun j' : Fin S => θ + ((-((j' : ℕ) : ℤ) : ℤ) : F))
    (fun i : Fin m => θ + ((bY m (S : ℤ) i : ℤ) : F))

lemma CA_eq : CA m n S θ = Cm (m + n) (asv m S θ) := by
  ext a j
  induction j using Fin.addCases with
  | left j' => simp [CA, Cm, asv, Rm, wcol]; ring_nf
  | right i => simp [CA, Cm, asv, Wb, wcol]; ring_nf

lemma CB_eq : CB m n S θ = Cm (m + n) (bsv m S θ) := by
  ext a j
  induction j using Fin.addCases with
  | left j' => simp [CB, Cm, bsv, Bm, wcol]; ring_nf
  | right i => simp [CB, Cm, bsv, Wb, wcol]; ring_nf

/-- `G · Δ = V(A) V(B) · ∑_{|P| = S+m} V(P)² ∏ ρ` (Cauchy-Binet reduction of `Num`). -/
theorem G_mul_Delta_CB (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    (CatalanCore.colMat fun j => zvec m n S θ j).det *
        ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det =
      Vprod (asv m S θ) * Vprod (bsv m S θ) *
        ∑ P : {P : Finset (Fin (m + n)) // P.card = S + m},
          Vprod (fun i => (((CatalanCore.colsOf P i : Fin (m + n)) : ℕ) : F)) ^ 2 *
            ∏ i : Fin (S + m), rho (asv m S θ) (bsv m S θ)
              ((CatalanCore.colsOf P i : Fin (m + n)) : ℕ) := by
  rw [G_mul_Delta m n S θ hΔ, CA_eq, CB_eq]
  have key : ∀ (a : Fin (m + n)) (z : ℤ), ((a : ℕ) : F) + (θ + (z : F)) ≠ 0 := fun a z h =>
    gen_add hθ a z (by linear_combination h)
  refine delta_CB _ _ ?_ ?_
  · intro a j
    induction j using Fin.addCases with
    | left j' => simp only [asv, Fin.addCases_left]; exact key a _
    | right i => simp only [asv, Fin.addCases_right]; exact key a _
  · intro a j
    induction j using Fin.addCases with
    | left j' => simp only [bsv, Fin.addCases_left]; exact key a _
    | right i => simp only [bsv, Fin.addCases_right]; exact key a _

end GD

end CatalanCore.Star.Leonard
