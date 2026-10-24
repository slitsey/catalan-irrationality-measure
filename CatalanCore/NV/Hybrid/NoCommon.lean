module

public import CatalanCore.NV.Hybrid.Bordered
public import CatalanCore.Linalg.Krylov
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Bordered "no common root" lemma (DO Lemma 2.2)

Two parts.

1. `exists_kernel_of_minor` (pure linear algebra): if `D` and its minor `D'` (delete the index `g`)
   are both singular, then `D` has a right kernel vector with `x g = 0`, or a left kernel vector with
   `y g = 0`.  (Elementary: take a left kernel vector `y` of `D'`, extended by 0; if
   `(y D) g = 0` it is a left kernel vector of `D`, else any right kernel vector `v` of `D` has
   `v g = 0`.)
2. For `D(z) = z E + Γ̂` with `E = diag(I_s, 0_m)` and `Γ̂` invertible, such a vector forces
   `k_R = 0` or `k_L = 0`, where `T = (Γ̂⁻¹)_{GG}`, `k_R = kdet Tᵀ e_g`, `k_L = kdet T e_g`.
-/

@[expose] public section

open Matrix CatalanCore

namespace CatalanFrames.LambdaHybrid.NV

variable {F : Type*} [Field F]

section Minor

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Lemma 2.2, linear-algebra core.** `f : κ → ι` is a bijection onto `ι ∖ {g}`. -/
theorem exists_kernel_of_minor (D : Matrix ι ι F) (g : ι) (f : κ → ι) (hf : Function.Injective f)
    (hfg : ∀ k, f k ≠ g) (hsurj : ∀ i, i ≠ g → ∃ k, f k = i)
    (h1 : D.det = 0) (h2 : (D.submatrix f f).det = 0) :
    (∃ x : ι → F, x ≠ 0 ∧ x g = 0 ∧ D *ᵥ x = 0) ∨ (∃ y : ι → F, y ≠ 0 ∧ y g = 0 ∧ y ᵥ* D = 0) := by
  obtain ⟨y', hy'0, hy'⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h2
  set y : ι → F := Function.extend f y' 0 with hy
  have hyf : ∀ k, y (f k) = y' k := fun k => hf.extend_apply _ _ _
  have hyg : y g = 0 := by
    rw [hy, Function.extend_apply']
    · rfl
    · rintro ⟨k, hk⟩; exact hfg k hk
  have hyout : ∀ i, i ∉ Set.range f → y i = 0 := by
    intro i hi
    rw [hy, Function.extend_apply' _ _ _ (by simpa using hi)]; rfl
  have hy0 : y ≠ 0 := by
    intro h
    apply hy'0
    ext k
    have := hyf k
    rw [h] at this
    simpa using this.symm
  -- the `j`-th coordinate of `y D`, for `j = f l`, vanishes
  have hcol : ∀ l, (y ᵥ* D) (f l) = 0 := by
    intro l
    have h := congrFun hy' l
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, Matrix.submatrix_apply] at h
    simp only [Matrix.vecMul, dotProduct]
    rw [← h]
    refine (Fintype.sum_of_injective f hf _ _ ?_ ?_).symm
    · intro i hi; rw [hyout i hi, zero_mul]
    · intro k; rw [hyf]
  by_cases hd : (y ᵥ* D) g = 0
  · right
    refine ⟨y, hy0, hyg, ?_⟩
    ext j
    by_cases hj : j = g
    · subst hj; simpa using hd
    · obtain ⟨l, rfl⟩ := hsurj j hj
      simpa using hcol l
  · left
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h1
    refine ⟨v, hv0, ?_, hv⟩
    have hz : y ⬝ᵥ (D *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
    rw [dotProduct_mulVec] at hz
    have hsp : y ᵥ* D = Pi.single g ((y ᵥ* D) g) := by
      ext j
      by_cases hj : j = g
      · subst hj; simp
      · obtain ⟨l, rfl⟩ := hsurj j hj
        rw [hcol l, Pi.single_eq_of_ne hj]
    rw [hsp, single_dotProduct] at hz
    exact (mul_eq_zero.1 hz).resolve_left hd

end Minor

section Krylov

variable {n : ℕ}

/-- A nonzero vector `x` with `x ⬝ (Aᵏ v) = 0` for all `k` kills the Krylov determinant. -/
lemma kdet_eq_zero_of_dot (A : Matrix (Fin n) (Fin n) F) (v x : Fin n → F) (hx : x ≠ 0)
    (h : ∀ k : ℕ, x ⬝ᵥ ((A ^ k) *ᵥ v) = 0) : kdet A v = 0 := by
  refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨x, hx, ?_⟩
  ext k
  have : (x ᵥ* krylov A v) k = x ⬝ᵥ ((A ^ (k : ℕ)) *ᵥ v) := by
    simp [Matrix.vecMul, dotProduct, krylov_apply]
  rw [this, h]; rfl

end Krylov

section Dual

variable {s m : ℕ}

/-- `T = (Γ̂⁻¹)_{GG}`. -/
noncomputable def Tmat (Γ : Matrix (Fin s ⊕ Fin m) (Fin s ⊕ Fin m) F) : Matrix (Fin s) (Fin s) F :=
  (Γ⁻¹).submatrix Sum.inl Sum.inl

/-- `k_R = det [e_gᵀ Tᵏ]_{k<s}`, as the Krylov determinant of `Tᵀ` at `e_g`. -/
noncomputable def kR (Γ : Matrix (Fin s ⊕ Fin m) (Fin s ⊕ Fin m) F) (g : Fin s) : F :=
  kdet (Tmat Γ)ᵀ (Pi.single g 1)

/-- `k_L = det [Tᵏ e_g]_{k<s}`. -/
noncomputable def kL (Γ : Matrix (Fin s ⊕ Fin m) (Fin s ⊕ Fin m) F) (g : Fin s) : F :=
  kdet (Tmat Γ) (Pi.single g 1)

variable (Γ : Matrix (Fin s ⊕ Fin m) (Fin s ⊕ Fin m) F)

omit [Field F] in
lemma Eblk_mulVec {F : Type*} [Field F] (x : Fin s ⊕ Fin m → F) :
    Eblk (Fin s) (Fin m) F *ᵥ x = Sum.elim (fun j => x (Sum.inl j)) 0 := by
  ext (i | i) <;> simp [Eblk, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

omit [Field F] in
lemma vecMul_Eblk {F : Type*} [Field F] (x : Fin s ⊕ Fin m → F) :
    x ᵥ* Eblk (Fin s) (Fin m) F = Sum.elim (fun j => x (Sum.inl j)) 0 := by
  ext (i | i) <;> simp [Eblk, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

/-- Right kernel vector with `x g = 0` forces `k_R = 0`. -/
theorem kR_eq_zero_of_right (hΓ : IsUnit Γ.det) {z : F} (hz : z ≠ 0) (g : Fin s)
    (x : Fin s ⊕ Fin m → F) (hx0 : x ≠ 0) (hxg : x (Sum.inl g) = 0)
    (hD : (z • Eblk (Fin s) (Fin m) F + Γ) *ᵥ x = 0) : kR Γ g = 0 := by
  set xG : Fin s → F := fun j => x (Sum.inl j) with hxG
  have hΓx : Γ *ᵥ x = -z • Sum.elim xG 0 := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Eblk_mulVec] at hD
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_right hD
  have hx : x = -z • (Γ⁻¹ *ᵥ Sum.elim xG 0) := by
    have := congrArg (fun w => Γ⁻¹ *ᵥ w) hΓx
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hΓ, Matrix.one_mulVec,
      Matrix.mulVec_smul] at this
    exact this
  have hT : Tmat Γ *ᵥ xG = (-z⁻¹) • xG := by
    ext j
    have h := congrFun hx (Sum.inl j)
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero] at h
    simp only [Tmat, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, smul_eq_mul]
    have h' : xG j = -z * ∑ l, Γ⁻¹ (Sum.inl j) (Sum.inl l) * xG l := h
    rw [h']; field_simp
  have hxG0 : xG ≠ 0 := by
    intro h0
    apply hx0
    rw [hx, h0]
    have : (Sum.elim (0 : Fin s → F) (0 : Fin m → F)) = 0 := by ext (i | i) <;> rfl
    rw [this]; simp
  unfold kR
  refine kdet_eq_zero_of_dot _ _ xG hxG0 fun k => ?_
  have hp : ∀ k : ℕ, (Tmat Γ ^ k) *ᵥ xG = (-z⁻¹) ^ k • xG := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hT, smul_smul, pow_succ]

  rw [Matrix.dotProduct_mulVec, ← Matrix.transpose_pow, Matrix.vecMul_transpose, hp, dotProduct_single]
  simp [hxG, hxg]

/-- Left kernel vector with `y g = 0` forces `k_L = 0`. -/
theorem kL_eq_zero_of_left (hΓ : IsUnit Γ.det) {z : F} (hz : z ≠ 0) (g : Fin s)
    (y : Fin s ⊕ Fin m → F) (hy0 : y ≠ 0) (hyg : y (Sum.inl g) = 0)
    (hD : y ᵥ* (z • Eblk (Fin s) (Fin m) F + Γ) = 0) : kL Γ g = 0 := by
  set yG : Fin s → F := fun j => y (Sum.inl j) with hyG
  have hyΓ : y ᵥ* Γ = -z • Sum.elim yG 0 := by
    rw [Matrix.vecMul_add, Matrix.vecMul_smul, vecMul_Eblk] at hD
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_right hD
  have hy : y = -z • (Sum.elim yG 0 ᵥ* Γ⁻¹) := by
    have := congrArg (fun w => w ᵥ* Γ⁻¹) hyΓ
    simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hΓ, Matrix.vecMul_one,
      Matrix.smul_vecMul] at this
    exact this
  have hT : yG ᵥ* Tmat Γ = (-z⁻¹) • yG := by
    ext j
    have h := congrFun hy (Sum.inl j)
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at h
    simp only [Tmat, Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, smul_eq_mul]
    have h' : yG j = -z * ∑ l, yG l * Γ⁻¹ (Sum.inl l) (Sum.inl j) := h
    rw [h']; field_simp
  have hyG0 : yG ≠ 0 := by
    intro h0
    apply hy0
    rw [hy, h0]
    have : (Sum.elim (0 : Fin s → F) (0 : Fin m → F)) = 0 := by ext (i | i) <;> rfl
    rw [this]; simp
  unfold kL
  refine kdet_eq_zero_of_dot _ _ yG hyG0 fun k => ?_
  have hp : ∀ k : ℕ, yG ᵥ* (Tmat Γ ^ k) = (-z⁻¹) ^ k • yG := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, ih, Matrix.smul_vecMul, hT, smul_smul, pow_succ]

  rw [Matrix.dotProduct_mulVec, hp, dotProduct_single]
  simp [hyG, hyg]

end Dual

end CatalanFrames.LambdaHybrid.NV
