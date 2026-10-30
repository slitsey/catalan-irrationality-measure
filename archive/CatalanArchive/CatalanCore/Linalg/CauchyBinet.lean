module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Sort

/-!
# Rectangular Cauchy–Binet (and its weighted form)

For `A : Matrix (Fin n) (Fin N) R`, `B : Matrix (Fin N) (Fin n) R` over a commutative ring,
`det (A * B) = ∑_{|P| = n} det A[:,P] * det B[P,:]`.  Not in Mathlib (checked).
-/

@[expose] public section

open Finset Matrix Equiv

namespace CatalanCore

variable {R : Type*} [CommRing R] {n N : ℕ}

/-- Leibniz formula with rows indexing the product. -/
theorem det_apply_row {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m R) :
    M.det = ∑ σ : Perm m, (((Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i, M i (σ i) := by
  rw [← det_transpose, det_apply']; simp

/-- Expansion over all maps `f : Fin n → Fin N`. -/
theorem det_mul_expand (A : Matrix (Fin n) (Fin N) R) (B : Matrix (Fin N) (Fin n) R) :
    (A * B).det = ∑ f : Fin n → Fin N, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  have h : ∀ σ : Perm (Fin n), ∏ i, (A * B) i (σ i)
      = ∑ f : Fin n → Fin N, (∏ i, A i (f i)) * ∏ i, B (f i) (σ i) := by
    intro σ
    simp only [mul_apply]
    rw [Finset.prod_univ_sum]
    simp [Finset.prod_mul_distrib, Fintype.piFinset_univ]
  rw [det_apply_row]
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [det_apply_row, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id]
  ring

/-- The increasing enumeration of an `n`-subset of `Fin N`. -/
def colsOf (P : {P : Finset (Fin N) // P.card = n}) : Fin n ↪o Fin N :=
  P.1.orderEmbOfFin P.2

/-- Regrouping of a sum over injective maps into (subset, permutation). -/
theorem sum_maps_eq_sum_subsets {M : Type*} [AddCommMonoid M] (g : (Fin n → Fin N) → M)
    (hg : ∀ f, ¬ Function.Injective f → g f = 0) :
    ∑ f, g f = ∑ P : {P : Finset (Fin N) // P.card = n}, ∑ τ : Perm (Fin n), g (colsOf P ∘ τ) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun f _ hf => by
    by_contra h; exact hf (hg f h))]
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => colsOf x.1 ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (colsOf x.1).injective.comp x.2.injective
  · rintro ⟨P, τ⟩ _ ⟨P', τ'⟩ _ h
    have hr : ∀ (Q : {P : Finset (Fin N) // P.card = n}) (σ : Perm (Fin n)),
        Finset.univ.image (colsOf Q ∘ σ) = Q.1 := by
      intro Q σ
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
      constructor
      · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
      · intro hx
        have : x ∈ Set.range (colsOf Q) := by
          rw [colsOf, Finset.range_orderEmbOfFin]; exact hx
        obtain ⟨j, rfl⟩ := this
        exact ⟨σ.symm j, by simp⟩
    have hPP : P = P' := Subtype.ext (by rw [← hr P τ, ← hr P' τ', h])
    subst hPP
    have : τ = τ' := by
      refine Equiv.ext fun i => ?_; exact (colsOf P).injective (congrFun h i)
    subst this; rfl
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hc : (Finset.univ.image f).card = n := by
      rw [Finset.card_image_of_injective _ hf]; simp
    set Q : {P : Finset (Fin N) // P.card = n} := ⟨Finset.univ.image f, hc⟩
    have hmem : ∀ i, ∃ j, colsOf Q j = f i := by
      intro i
      have : f i ∈ Set.range (colsOf Q) := by
        rw [colsOf, Finset.range_orderEmbOfFin]; simp [Q]
      exact this
    choose t ht using hmem
    have hti : Function.Injective t := fun a b hab => hf (by rw [← ht a, ← ht b, hab])
    refine ⟨⟨Q, Equiv.ofBijective t (Finite.injective_iff_bijective.mp hti)⟩, by simp, ?_⟩
    ext i; simp [ht]
  · intro _ _; rfl

/-- **Rectangular Cauchy–Binet.** -/
theorem det_mul_eq_sum_subsets (A : Matrix (Fin n) (Fin N) R) (B : Matrix (Fin N) (Fin n) R) :
    (A * B).det = ∑ P : {P : Finset (Fin N) // P.card = n},
      (A.submatrix id (colsOf P)).det * (B.submatrix (colsOf P) id).det := by
  rw [det_mul_expand, sum_maps_eq_sum_subsets]
  · refine Finset.sum_congr rfl fun P _ => ?_
    have h1 : ∀ τ : Perm (Fin n), (B.submatrix (colsOf P ∘ τ) id).det
        = (((Perm.sign τ : ℤˣ) : ℤ) : R) * (B.submatrix (colsOf P) id).det := by
      intro τ
      have := det_permute τ (B.submatrix (colsOf P) id)
      simpa [Function.comp_def, submatrix_apply] using this
    simp only [h1]
    rw [det_apply_row (A.submatrix id (colsOf P)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [submatrix_apply, id, Function.comp_apply]
    ring
  · intro f hf
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
      by_contra h; exact hf fun a b hab => by_contra fun hne => h ⟨a, b, hab, hne⟩
    rw [mul_eq_zero_of_right _ (det_zero_of_row_eq hne (by ext k; simp [hij]))]

/-- **Weighted Cauchy–Binet** (Heine-type kernel formula). -/
theorem det_transpose_mul_diagonal_mul (A : Matrix (Fin N) (Fin n) R) (t : Fin N → R)
    (B : Matrix (Fin N) (Fin n) R) :
    (Aᵀ * diagonal t * B).det = ∑ P : {P : Finset (Fin N) // P.card = n},
      (∏ p ∈ P.1, t p) * (A.submatrix (colsOf P) id).det * (B.submatrix (colsOf P) id).det := by
  rw [det_mul_eq_sum_subsets]
  refine Finset.sum_congr rfl fun P _ => ?_
  have h : (Aᵀ * diagonal t).submatrix id (colsOf P)
      = (A.submatrix (colsOf P) id)ᵀ * diagonal (t ∘ colsOf P) := by
    ext i j
    simp [mul_apply, diagonal_apply, Finset.sum_ite_eq']
  have hp : ∏ p ∈ P.1, t p = ∏ i, t (colsOf P i) := by
    have := Finset.prod_map Finset.univ (colsOf P).toEmbedding t
    rw [colsOf, Finset.map_orderEmbOfFin_univ] at this
    exact this
  rw [h, det_mul, det_transpose, det_diagonal, hp]
  simp
  ring

end CatalanCore
