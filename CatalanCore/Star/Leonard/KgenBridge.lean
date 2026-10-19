module

public import CatalanCore.Star.Pencil
public import CatalanCore.Linalg.KrylovV2
public import CatalanCore.Linalg.KrylovTri

/-!
# Bridge `Star.Defs.kgenCore` ↔ `bkdet` (package H7 glue)

At `K = m + n`, `U = ubasis_X`, `V = ubasis_Y`, `H = Hn = Vᵀ U`, `B = H⁻¹ Hc` and `Π N U = U B`
(`Star.Pencil`), the legacy Krylov determinant `kgenCore` (rows `w_Sᵀ (Π N)^k`, kernel basis `u_i`)
and the bordered Krylov determinant `bkdet W_Y (Π N) (Π w_S)` are related by

`c_Y^n · det[W_Y | U] · kgenCore = c_X^n · det H · bkdet W_Y (Π N) (Π w_S)`,

`c_X = Π_X(S)/∏_a(θ+a+S)`, `c_Y = Π_Y(S)/∏_a(θ+a+S)`.  (Row Krylov vs column Krylov: `B` is
self-adjoint for `H`.)
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star

variable {F : Type*} [Field F]

/-- `kgenCore` with `Fin n` indices at `K = m + n`. -/
noncomputable def kgenN (m n : ℕ) (θ : F) (J : Finset ℤ) (S : ℤ) (bx by' : Fin m → ℤ) : F :=
  Matrix.det (Matrix.of fun (k i : Fin n) =>
    (((wcol (m + n) θ S) ᵥ* ((projB (m + n) θ bx by' * Nmat (m + n) θ J) ^ (k : ℕ))) ᵥ*
      ubasis (m + n) n θ bx) i)

lemma kgenCore_eq_kgenN (m n : ℕ) (θ : F) (J : Finset ℤ) (S : ℤ) (bx by' : Fin m → ℤ) :
    kgenCore (m + n) m θ J S bx by' = kgenN m n θ J S bx by' := by
  have h : m + n - m = n := by omega
  unfold kgenCore kgenN
  generalize hd : m + n - m = d at *
  subst h
  rfl

lemma Hn_symm (K m S n : ℕ) (θ : F) : (Hn K m S n θ)ᵀ = Hn K m S n θ := by
  ext i j; simp [Hn, add_comm]

lemma Hc_symm (K m S n : ℕ) (θ : F) (J : Finset ℤ) : (Hc K m S n θ J)ᵀ = Hc K m S n θ J := by
  ext i j; simp [Hc, add_comm]

lemma conj_pow {n : ℕ} (H B : Matrix (Fin n) (Fin n) F) (hH : IsUnit H.det)
    (hconj : H * B * H⁻¹ = Bᵀ) (k : ℕ) : H * B ^ k * H⁻¹ = (Bᵀ) ^ k := by
  induction k with
  | zero => simp [Matrix.mul_nonsing_inv _ hH]
  | succ k ih =>
    have hmul : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ hH
    calc H * B ^ (k + 1) * H⁻¹ = (H * B ^ k * H⁻¹) * (H * B * H⁻¹) := by
          calc H * B ^ (k + 1) * H⁻¹ = H * B ^ k * (H⁻¹ * H) * B * H⁻¹ := by
                rw [hmul, pow_succ]; simp only [Matrix.mul_assoc, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]
      _ = (Bᵀ) ^ (k + 1) := by rw [ih, hconj, pow_succ]

/-- **The bridge.** -/
theorem kgenN_bridge {m n : ℕ} (θ : F) (J : Finset ℤ) (S : ℕ) (bx by' : Fin m → ℤ)
    (hdist : ∀ a b : Fin (m + n), ((a : ℕ) : F) = ((b : ℕ) : F) → a = b)
    (hZ : ∀ z : F, piB bx z * piB by' z = PiZ m S z)
    (hJ : ∀ j ∈ J, ∀ a : Fin (m + n), θ + ((a : ℕ) : F) + (j : F) ≠ 0)
    (hS : ∀ a : Fin (m + n), θ + ((a : ℕ) : F) + (S : F) ≠ 0)
    (hbx : ∀ (i : Fin m) (a : Fin (m + n)), θ + ((a : ℕ) : F) + (bx i : F) ≠ 0)
    (hby : ∀ (i : Fin m) (a : Fin (m + n)), θ + ((a : ℕ) : F) + (by' i : F) ≠ 0)
    (hG : IsUnit ((Wb (m + n) θ bx)ᵀ * Wb (m + n) θ by').det)
    (hH : IsUnit (Hn (m + n) m S n θ).det) :
    (piB by' (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ^ n *
        (CatalanCore.bmat (Wb (m + n) θ by') (ubasis (m + n) n θ bx)).det *
        kgenN m n θ J (S : ℤ) bx by' =
      (piB bx (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F))) ^ n *
        (Hn (m + n) m S n θ).det *
        CatalanCore.bkdet (Wb (m + n) θ by') (projB (m + n) θ bx by' * Nmat (m + n) θ J)
          (projB (m + n) θ bx by' *ᵥ wcol (m + n) θ (S : ℤ)) := by
  have hmn : m + n ≤ m + n := le_rfl
  set U := ubasis (m + n) n θ bx with hU
  set V := ubasis (m + n) n θ by' with hV
  set H := Hn (m + n) m S n θ with hHdef
  have hgram : Vᵀ * U = H := gram_eq θ S bx by' hZ
  have hcross : Vᵀ * Nmat (m + n) θ J * U = Hc (m + n) m S n θ J :=
    cross_eq θ hdist hmn S bx by' J hZ hJ
  have h2 : Vᵀ * Wb (m + n) θ by' = 0 := Wt_ubasis_cross θ hdist hmn bx by' hby
  have h3 : (Wb (m + n) θ bx)ᵀ * U = 0 := Wt_ubasis_self θ hdist hmn bx hbx
  have hproj : projB (m + n) θ bx by' = U * H⁻¹ * Vᵀ := by
    have := proj_abstract (by omega : n + m = m + n) U V (Wb (m + n) θ bx) (Wb (m + n) θ by') _ hH hG
      hgram h2 h3
    unfold projB
    exact (eq_sub_of_add_eq this).symm
  set B := H⁻¹ * Hc (m + n) m S n θ J with hB
  set Q := projB (m + n) θ bx by' * Nmat (m + n) θ J with hQ
  have hstep : Q * U = U * B := by
    rw [hQ, hproj, hB, ← hcross]
    simp only [Matrix.mul_assoc]
  have hpow : ∀ k : ℕ, Q ^ k * U = U * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hstep, Matrix.mul_assoc, ← pow_succ']
  -- the two constants
  set cX := piB bx (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F)) with hcX
  set cY := piB by' (S : F) / ∏ a : Fin (m + n), (θ + ((a : ℕ) : F) + (S : F)) with hcY
  have hwX : (wcol (m + n) θ (S : ℤ)) ᵥ* U = cX • nuS n (S : F) := by
    funext i
    have := wcol_ubasis θ hdist hmn bx (S : ℤ) (by simpa using hS) i
    simp only [Int.cast_natCast] at this
    rw [hU, this]
    simp only [Pi.smul_apply, smul_eq_mul, nuS]
    rw [hcX]; ring
  have hwY : (wcol (m + n) θ (S : ℤ)) ᵥ* V = cY • nuS n (S : F) := by
    funext i
    have := wcol_ubasis θ hdist hmn by' (S : ℤ) (by simpa using hS) i
    simp only [Int.cast_natCast] at this
    rw [hV, this]
    simp only [Pi.smul_apply, smul_eq_mul, nuS]
    rw [hcY]; ring
  -- (A) kgenN = cX^n * det R
  set R : Matrix (Fin n) (Fin n) F := Matrix.of fun (k i : Fin n) => ((nuS n (S : F)) ᵥ* B ^ (k : ℕ)) i
    with hR
  have hkgen : kgenN m n θ J (S : ℤ) bx by' = cX ^ n * R.det := by
    unfold kgenN
    have hrow : ∀ k : Fin n, ((wcol (m + n) θ (S : ℤ)) ᵥ* Q ^ (k : ℕ)) ᵥ* U =
        cX • ((nuS n (S : F)) ᵥ* B ^ (k : ℕ)) := by
      intro k
      rw [Matrix.vecMul_vecMul, hpow, ← Matrix.vecMul_vecMul, hwX, Matrix.smul_vecMul]
    have hmat : (Matrix.of fun (k i : Fin n) =>
        (((wcol (m + n) θ (S : ℤ)) ᵥ* Q ^ (k : ℕ)) ᵥ* U) i) = cX • R := by
      ext k i
      simp only [Matrix.of_apply, Matrix.smul_apply, hrow k, Pi.smul_apply, smul_eq_mul, hR]
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
  -- (B) bkdet
  set y : Fin n → F := H⁻¹ *ᵥ (Vᵀ *ᵥ wcol (m + n) θ (S : ℤ)) with hy
  have hvy : projB (m + n) θ bx by' *ᵥ wcol (m + n) θ (S : ℤ) = U *ᵥ y := by
    rw [hproj, hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hKr : krylovE Q (U *ᵥ y) = U * krylov B y + Wb (m + n) θ by' * (0 : Matrix (Fin m) (Fin n) F) := by
    ext i k
    simp only [krylovE, Matrix.of_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, krylov]
    have := congrArg (fun M => (M *ᵥ y) i) (hpow k)
    simp only [← Matrix.mulVec_mulVec] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply]
  have hbk : CatalanCore.bkdet (Wb (m + n) θ by') Q (projB (m + n) θ bx by' *ᵥ wcol (m + n) θ (S : ℤ)) =
      kdet B y * (CatalanCore.bmat (Wb (m + n) θ by') U).det := by
    unfold CatalanCore.bkdet
    rw [hvy, hKr, CatalanCore.det_bmat_comb]
    rfl
  -- (D) scaling
  set z0 : Fin n → F := H⁻¹ *ᵥ nuS n (S : F) with hz0
  have hy' : y = cY • z0 := by
    rw [hy, hz0, Matrix.mulVec_transpose, hwY, Matrix.mulVec_smul]
  have hscal : kdet B y = cY ^ n * kdet B z0 := by
    have : krylov B y = cY • krylov B z0 := by
      ext i k
      simp [krylov, hy', Matrix.mulVec_smul]
    unfold kdet
    rw [this, Matrix.det_smul, Fintype.card_fin]
  -- (E) row vs column Krylov
  have hHsymm : Hᵀ = H := Hn_symm (m + n) m S n θ
  have hHinvsymm : (H⁻¹)ᵀ = H⁻¹ := by rw [Matrix.transpose_nonsing_inv, hHsymm]
  have hconj : H * B * H⁻¹ = Bᵀ := by
    have hmulr : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ hH
    calc H * B * H⁻¹ = (H * H⁻¹) * Hc (m + n) m S n θ J * H⁻¹ := by
          rw [hB]; simp only [Matrix.mul_assoc]
      _ = Hc (m + n) m S n θ J * H⁻¹ := by rw [hmulr, Matrix.one_mul]
      _ = Bᵀ := by
          rw [hB, Matrix.transpose_mul, hHinvsymm, Hc_symm]
  have hRZ : R = (H * krylov B z0)ᵀ := by
    ext k i
    have hk := conj_pow H B hH hconj k
    simp only [hR, Matrix.of_apply, Matrix.transpose_apply]
    have : (H * krylov B z0) i k = (H *ᵥ (B ^ (k : ℕ) *ᵥ z0)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, krylov]
    rw [this, hz0, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hk,
      ← Matrix.transpose_pow, Matrix.mulVec_transpose]
  have hdetR : R.det = H.det * kdet B z0 := by
    rw [hRZ, Matrix.det_transpose, Matrix.det_mul]; rfl
  -- (F) combine
  rw [hbk, hkgen, hscal, hdetR]
  ring

end CatalanCore.Star
