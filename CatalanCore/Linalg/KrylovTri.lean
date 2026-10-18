module

public import CatalanCore.Linalg.ColTriDet
public import CatalanCore.Linalg.Krylov
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Krylov determinants: triangular change of columns (L2, L3)

* `det_cols_tri`: if column `k` of `a` equals `d k` times column `k` of `b` plus an element of the
  span of the earlier columns of `b`, then `det a = (∏ d) * det b`.
* `kdet_add_vecMulVec` (L2): `u(N + w wᵀ, w) = u(N, w)`.
* `kdet_chain` (L3): if `T v_j = r_j v_{j+1} + (earlier)`, then
  `u(T, v₀) = (∏_k ∏_{j<k} r_j) · det[v₀ … v_{n-1}]`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {n : ℕ}

/-- The matrix whose `k`-th column is `a k`. -/
def colMat (a : ℕ → Fin n → F) : Matrix (Fin n) (Fin n) F := Matrix.of fun i k => a k i

lemma krylov_eq_colMat (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    krylov A v = colMat fun j => A ^ j *ᵥ v := rfl

lemma exists_coeffs_of_mem_span (f : ℕ → Fin n → F) (k : Fin n) {x : Fin n → F}
    (hx : x ∈ Submodule.span F (f '' Set.Iio (k : ℕ))) :
    ∃ c : Fin n → F, x = ∑ j ∈ Finset.Iio k, c j • f j := by
  have e : f '' Set.Iio (k : ℕ) = (fun j : Fin n => f j) '' (Set.Iio k) := by
    ext y
    simp only [Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by omega⟩, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
  rw [e] at hx
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination F).1 hx
  refine ⟨l, ?_⟩
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_of_support_subset l (s := Finset.Iio k) ?_ _ ?_
  · intro j hj
    have := hl (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hj))
    simpa using this
  · intro j _; simp

theorem det_cols_tri (a b : ℕ → Fin n → F) (d : Fin n → F)
    (h : ∀ k : Fin n, a k - d k • b k ∈ Submodule.span F (b '' Set.Iio (k : ℕ))) :
    (colMat a).det = (∏ k, d k) * (colMat b).det := by
  choose c hc using fun k => exists_coeffs_of_mem_span b k (h k)
  refine det_eq_prod_mul_det_of_colTri _ _ d c fun i k => ?_
  have := congrFun (hc k) i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
  simp only [colMat, Matrix.of_apply]
  rw [← this]
  ring

lemma mulVec_mem_span_image (X : Matrix (Fin n) (Fin n) F) (f : ℕ → Fin n → F) (s t : Set ℕ)
    (h : ∀ j ∈ s, X *ᵥ f j ∈ Submodule.span F (f '' t)) {x : Fin n → F}
    (hx : x ∈ Submodule.span F (f '' s)) : X *ᵥ x ∈ Submodule.span F (f '' t) := by
  have : Submodule.span F (f '' s) ≤ (Submodule.span F (f '' t)).comap (Matrix.mulVecLin X) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    exact h j hj
  exact this hx

/-- **L2.** `u(N + w wᵀ, w) = u(N, w)`. -/
theorem kdet_add_vecMulVec (N : Matrix (Fin n) (Fin n) F) (w : Fin n → F) :
    kdet (N + Matrix.vecMulVec w w) w = kdet N w := by
  set f : ℕ → Fin n → F := fun j => N ^ j *ᵥ w with hf
  have hA : ∀ x : Fin n → F, (N + Matrix.vecMulVec w w) *ᵥ x = N *ᵥ x + (w ⬝ᵥ x) • w := by
    intro x
    rw [Matrix.add_mulVec]
    congr 1
    ext i
    simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hP : ∀ k : ℕ, (N + Matrix.vecMulVec w w) ^ k *ᵥ w - N ^ k *ᵥ w ∈
      Submodule.span F (f '' Set.Iio k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : (N + Matrix.vecMulVec w w) ^ (k + 1) *ᵥ w - N ^ (k + 1) *ᵥ w =
          (N + Matrix.vecMulVec w w) *ᵥ ((N + Matrix.vecMulVec w w) ^ k *ᵥ w - N ^ k *ᵥ w)
            + (w ⬝ᵥ (N ^ k *ᵥ w)) • w := by
        rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.mulVec_sub, hA (N ^ k *ᵥ w)]
        abel
      rw [hstep]
      refine Submodule.add_mem _ (mulVec_mem_span_image _ f _ (Set.Iio (k + 1)) ?_ ih) ?_
      · intro j hj
        rw [hA]
        refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp, by simp [hf]⟩))
        refine Submodule.subset_span ⟨j + 1, by simp at hj ⊢; omega, by simp [hf, pow_succ', Matrix.mulVec_mulVec]⟩
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp, by simp [hf]⟩)
  rw [kdet, kdet, krylov_eq_colMat, krylov_eq_colMat]
  have := det_cols_tri (fun j => (N + Matrix.vecMulVec w w) ^ j *ᵥ w) f (fun _ => 1)
    (fun k => by simpa using hP k)
  simpa using this

/-- **L3 (chain).** If `T v_j - r_j v_{j+1}` lies in the span of `v_0, …, v_j` for `j + 1 < n`, then
`u(T, v_0) = (∏_k ∏_{j<k} r_j) · det[v_0, …, v_{n-1}]`. -/
theorem kdet_chain (T : Matrix (Fin n) (Fin n) F) (v : ℕ → Fin n → F) (r : ℕ → F)
    (hv : ∀ j, j + 1 < n →
      T *ᵥ v j - r j • v (j + 1) ∈ Submodule.span F (v '' Set.Iio (j + 1))) :
    kdet T (v 0) = (∏ k : Fin n, ∏ j ∈ Finset.range k, r j) * (colMat v).det := by
  have hP : ∀ k : ℕ, k < n → T ^ k *ᵥ v 0 - (∏ j ∈ Finset.range k, r j) • v k ∈
      Submodule.span F (v '' Set.Iio k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hmono : ∀ m ≤ k + 1, Submodule.span F (v '' Set.Iio m) ≤
          Submodule.span F (v '' Set.Iio (k + 1)) := fun m hm =>
        Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hm))
      have hstep : T ^ (k + 1) *ᵥ v 0 - (∏ j ∈ Finset.range (k + 1), r j) • v (k + 1) =
          T *ᵥ (T ^ k *ᵥ v 0 - (∏ j ∈ Finset.range k, r j) • v k)
            + (∏ j ∈ Finset.range k, r j) • (T *ᵥ v k - r k • v (k + 1)) := by
        rw [pow_succ', ← Matrix.mulVec_mulVec, Finset.prod_range_succ, Matrix.mulVec_sub,
          Matrix.mulVec_smul, smul_sub, mul_smul]
        abel
      rw [hstep]
      refine Submodule.add_mem _ (mulVec_mem_span_image _ v _ (Set.Iio (k + 1)) ?_ (ih (by omega))) ?_
      · intro j hj
        have hj' : j < k := hj
        have h1 := hv j (by omega)
        have e : T *ᵥ v j = r j • v (j + 1) + (T *ᵥ v j - r j • v (j + 1)) := by abel
        rw [e]
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨j + 1, by simp; omega, rfl⟩)) (hmono (j + 1) (by omega) h1)
      · exact Submodule.smul_mem _ _ (hv k hk)
  rw [kdet, krylov_eq_colMat]
  exact det_cols_tri _ v _ fun k => hP k k.2

end CatalanCore
