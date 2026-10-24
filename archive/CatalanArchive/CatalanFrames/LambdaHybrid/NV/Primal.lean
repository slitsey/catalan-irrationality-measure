module

public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.NoCommon
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# FG primal reduction: bordered pair with a rank-one weight forces a vanishing `k^gen`

Frame-free, over a field `F`, node type `A`, borders `ι`.

* `borderedN z N WX WY = [[z + N, WY], [WXᵀ, 0]]` (so `bordered z G X Y = borderedN z (G Gᵀ) X Y`).
* `projP WX WY = 1 - WY (WXᵀ WY)⁻¹ WXᵀ`, the projector onto `ker WXᵀ` along `range WY`.
* `kgenK N w WX WY U = det [wᵀ (Π N)^k u_i]` for a family `U` of columns spanning `ker WXᵀ`
  (`SpansKer`).  The determinant of a spanning family is independent of the basis up to a unit, so
  statements are made for every spanning `U`.
* `primal_pair`: if `WXᵀ WY` is invertible, `N₂` symmetric, and `borderedN z N₂` and
  `borderedN z (N₂ + τ w wᵀ)` (`τ ≠ 0`) are both singular, then `kgenR' = 0` or `kgenL' = 0`.
  No hypothesis on `z` and no invertibility of `Γ̂`.
-/

@[expose] public section

open Matrix CatalanCore

namespace CatalanArchive.CatalanFrames.LambdaHybrid.NV

variable {F : Type*} [Field F] {A : Type*} [Fintype A] [DecidableEq A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `[[z + N, WY], [WXᵀ, 0]]`. -/
def borderedN (z : F) (N : Matrix A A F) (WX WY : Matrix A (ι) F) :
    Matrix (A ⊕ ι) (A ⊕ ι) F :=
  fromBlocks (z • (1 : Matrix A A F) + N) WY WXᵀ 0

lemma bordered_eq_borderedN {g : Type*} [Fintype g] [DecidableEq g] (z : F) (G : Matrix A g F)
    (X Y : Matrix A (ι) F) : bordered z G X Y = borderedN z (G * Gᵀ) X Y := rfl

lemma borderedN_transpose (z : F) (N : Matrix A A F) (WX WY : Matrix A (ι) F) :
    (borderedN z N WX WY)ᵀ = borderedN z Nᵀ WY WX := by
  simp [borderedN, fromBlocks_transpose, transpose_add, transpose_smul]

/-- `Π = 1 - WY (WXᵀ WY)⁻¹ WXᵀ`. -/
noncomputable def projP (WX WY : Matrix A (ι) F) : Matrix A A F :=
  1 - WY * (WXᵀ * WY)⁻¹ * WXᵀ

/-- `U` (columns `u_i`) spans `ker WXᵀ`. -/
def SpansKer {n : ℕ} (WX : Matrix A (ι) F) (U : Matrix A (Fin n) F) : Prop :=
  ∀ x : A → F, WXᵀ *ᵥ x = 0 → ∃ y : Fin n → F, U *ᵥ y = x

/-- `det [wᵀ (Π N)^k u_i]_{k,i<n}`. -/
noncomputable def kgenK {n : ℕ} (N : Matrix A A F) (w : A → F) (WX WY : Matrix A (ι) F)
    (U : Matrix A (Fin n) F) : F :=
  Matrix.det (Matrix.of fun (k i : Fin n) => ((w ᵥ* ((projP WX WY * N) ^ (k : ℕ))) ᵥ* U) i)

/-- `k_R'` (kernel of `WXᵀ`). -/
noncomputable abbrev kgenR' {n : ℕ} (N : Matrix A A F) (w : A → F) (WX WY : Matrix A (ι) F)
    (U : Matrix A (Fin n) F) : F := kgenK N w WX WY U

/-- `k_L'` (`X ↔ Y`; kernel of `WYᵀ`). -/
noncomputable abbrev kgenL' {n : ℕ} (N : Matrix A A F) (w : A → F) (WX WY : Matrix A (ι) F)
    (U : Matrix A (Fin n) F) : F := kgenK N w WY WX U

/-- Right kernel vector of the bordered matrix, orthogonal to `w`, kills `k_R'`. -/
lemma kgenK_eq_zero_of_right {z : F} (N : Matrix A A F) (w : A → F) (WX WY : Matrix A (ι) F)
    (hΔ : IsUnit (WXᵀ * WY).det) (x₀ : A ⊕ ι → F) (hx0 : x₀ ≠ 0)
    (hM : borderedN z N WX WY *ᵥ x₀ = 0) (hv : Sum.elim w (0 : ι → F) ⬝ᵥ x₀ = 0)
    {n : ℕ} (U : Matrix A (Fin n) F) (hU : SpansKer WX U) :
    kgenK N w WX WY U = 0 := by
  set xt : A → F := fun a => x₀ (Sum.inl a) with hxt
  set c : ι → F := fun j => x₀ (Sum.inr j) with hc
  have hx₀ : x₀ = Sum.elim xt c := by ext (i | i) <;> rfl
  rw [hx₀, borderedN, fromBlocks_mulVec] at hM
  have h1 : (z • (1 : Matrix A A F) + N) *ᵥ xt + WY *ᵥ c = 0 := by
    ext a; simpa using congrFun hM (Sum.inl a)
  have h2 : WXᵀ *ᵥ xt = 0 := by
    ext j; simpa using congrFun hM (Sum.inr j)
  have hw : w ⬝ᵥ xt = 0 := by
    rw [hx₀] at hv; simpa [dotProduct, Fintype.sum_sum_type] using hv
  have hx0' : xt ≠ 0 := by
    intro h
    apply hx0
    have hWc : WY *ᵥ c = 0 := by simpa [h] using h1
    have hc0 : c = 0 := by
      refine Matrix.eq_zero_of_mulVec_eq_zero hΔ.ne_zero ?_
      rw [← Matrix.mulVec_mulVec, hWc, mulVec_zero]
    rw [hx₀, h, hc0]; ext (i | i) <;> rfl
  have hPWY : projP WX WY * WY = 0 := by
    have e : (WXᵀ * WY)⁻¹ * (WXᵀ * WY) = 1 := Matrix.nonsing_inv_mul _ hΔ
    rw [projP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, e, Matrix.mul_one, sub_self]
  have hPx : projP WX WY *ᵥ xt = xt := by
    simp [projP, sub_mulVec, ← Matrix.mulVec_mulVec, h2]
  have hkey : (projP WX WY * N) *ᵥ xt = (-z) • xt := by
    have h3 : projP WX WY *ᵥ ((z • (1 : Matrix A A F) + N) *ᵥ xt) = 0 := by
      have : (z • (1 : Matrix A A F) + N) *ᵥ xt = -(WY *ᵥ c) := eq_neg_of_add_eq_zero_left h1
      rw [this, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hPWY]; simp
    have h4 : z • xt + (projP WX WY * N) *ᵥ xt = 0 := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
        Matrix.mulVec_smul, hPx, Matrix.mulVec_mulVec] at h3
      exact h3
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_right h4
  have hpow : ∀ k : ℕ, ((projP WX WY * N) ^ k) *ᵥ xt = (-z) ^ k • xt := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hkey, smul_smul, pow_succ]
  obtain ⟨y, hy⟩ := hU xt h2
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0' (by rw [← hy]; simp)
  unfold kgenK
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨y, hy0, ?_⟩
  ext k
  show ((w ᵥ* ((projP WX WY * N) ^ (k : ℕ))) ᵥ* U) ⬝ᵥ y = 0
  rw [← Matrix.dotProduct_mulVec, hy, ← Matrix.dotProduct_mulVec, hpow, dotProduct_smul, hw]
  simp

lemma borderedN_add_rank_one (z : F) (τ : F) (N : Matrix A A F) (w : A → F)
    (WX WY : Matrix A (ι) F) :
    borderedN z (N + τ • vecMulVec w w) WX WY =
      borderedN z N WX WY +
        τ • vecMulVec (Sum.elim w (0 : ι → F)) (Sum.elim w (0 : ι → F)) := by
  ext (i | i) (j | j) <;> simp [borderedN, vecMulVec_apply, add_assoc]

/-- **FG primal reduction.**  Both bordered determinants vanish (at any `z`), `N₂` symmetric,
`τ ≠ 0`, `WXᵀ WY` invertible: then `k_R'` or `k_L'` vanishes (for every spanning kernel family). -/
theorem primal_pair {z : F} {τ : F} (hτ : τ ≠ 0) (N₂ : Matrix A A F) (hN : N₂ᵀ = N₂) (w : A → F)
    (WX WY : Matrix A (ι) F) (hΔ : IsUnit (WXᵀ * WY).det)
    (h₂ : (borderedN z N₂ WX WY).det = 0)
    (h₁ : (borderedN z (N₂ + τ • vecMulVec w w) WX WY).det = 0) :
    (∀ (n : ℕ) (U : Matrix A (Fin n) F), SpansKer WX U → kgenR' N₂ w WX WY U = 0) ∨
    (∀ (n : ℕ) (U : Matrix A (Fin n) F), SpansKer WY U → kgenL' N₂ w WX WY U = 0) := by
  set M₂ := borderedN z N₂ WX WY with hM₂
  set v : A ⊕ ι → F := Sum.elim w 0 with hv
  set P : Matrix ((A ⊕ ι) ⊕ Unit) ((A ⊕ ι) ⊕ Unit) F :=
    fromBlocks M₂ (Matrix.of fun i _ => v i) (Matrix.of fun _ j => -τ * v j) 1 with hP
  have hdet : P.det = 0 := by
    haveI : Invertible (1 : Matrix Unit Unit F) := invertibleOne
    rw [hP, det_fromBlocks₂₂, det_one, invOf_one, one_mul, ← h₁, borderedN_add_rank_one]
    congr 1
    ext i j
    simp [Matrix.mul_apply, vecMulVec_apply, hv, hM₂]
    ring
  have hsub : P.submatrix Sum.inl Sum.inl = M₂ := by
    ext i j; simp [hP]
  rcases exists_kernel_of_minor P (Sum.inr ()) (Sum.inl) Sum.inl_injective (by simp)
    (by rintro (i | i) hi; exacts [⟨i, rfl⟩, absurd rfl hi]) hdet (by rw [hsub]; exact h₂) with
    ⟨x, hx0, hxg, hx⟩ | ⟨y, hy0, hyg, hy⟩
  · -- right kernel vector
    left
    intro n U hU
    set x₀ : A ⊕ ι → F := fun i => x (Sum.inl i) with hx₀d
    have hxe : x = Sum.elim x₀ 0 := by
      ext (i | i)
      · rfl
      · rcases i with ⟨⟩; simpa using hxg
    have hx00 : x₀ ≠ 0 := by
      intro h; apply hx0; rw [hxe, h]; ext (i | i) <;> rfl
    rw [hxe, hP, fromBlocks_mulVec] at hx
    have e1 : M₂ *ᵥ x₀ = 0 := by
      ext i; simpa using congrFun hx (Sum.inl i)
    have e2 : v ⬝ᵥ x₀ = 0 := by
      have hC : (Matrix.of fun (_ : Unit) j => -τ * v j : Matrix Unit (A ⊕ ι) F) *ᵥ x₀ =
          fun _ => -τ * (v ⬝ᵥ x₀) := by
        ext
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      have h := congrFun hx (Sum.inr ())
      simp only [Sum.elim_inr, Pi.add_apply, Pi.zero_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, hC,
        Matrix.mulVec_zero, add_zero] at h
      simpa [hτ] using h
    exact kgenK_eq_zero_of_right N₂ w WX WY hΔ x₀ hx00 e1 e2 U hU
  · -- left kernel vector
    right
    intro n U hU
    set y₀ : A ⊕ ι → F := fun i => y (Sum.inl i) with hy₀d
    have hye : y = Sum.elim y₀ 0 := by
      ext (i | i)
      · rfl
      · rcases i with ⟨⟩; simpa using hyg
    have hy00 : y₀ ≠ 0 := by
      intro h; apply hy0; rw [hye, h]; ext (i | i) <;> rfl
    rw [← Matrix.mulVec_transpose, hye, hP, fromBlocks_transpose, fromBlocks_mulVec] at hy
    have e1 : M₂ᵀ *ᵥ y₀ = 0 := by
      ext i; simpa using congrFun hy (Sum.inl i)
    have e2 : v ⬝ᵥ y₀ = 0 := by
      have hB : (Matrix.of fun i (_ : Unit) => v i : Matrix (A ⊕ ι) Unit F)ᵀ *ᵥ y₀ =
          fun _ => v ⬝ᵥ y₀ := by
        ext; simp [Matrix.mulVec, dotProduct, mul_comm]
      have h := congrFun hy (Sum.inr ())
      simp only [Sum.elim_inr, Pi.add_apply, Pi.zero_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, hB,
        Matrix.mulVec_zero, add_zero] at h
      exact h
    rw [hM₂, borderedN_transpose, hN] at e1
    have hΔ' : IsUnit (WYᵀ * WX).det := by
      rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]; exact hΔ
    exact kgenK_eq_zero_of_right N₂ w WY WX hΔ' y₀ hy00 e1 e2 U hU

end CatalanArchive.CatalanFrames.LambdaHybrid.NV
