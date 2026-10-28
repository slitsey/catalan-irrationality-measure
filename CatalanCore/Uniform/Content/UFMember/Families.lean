module

public import CatalanCore.Linalg.TwoLevelDet
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# UF member package, step 1a: the two-level principle from kernel families

Abstract setting: a domain `R`, a field `K`, a ring map `φ : R → K` whose kernel is `(π)` for a
prime `π`, and every element of `K` a fraction `φ r / φ d` (true for `phiP p`, where
`K = 𝔽_p(X)` is the fraction field of the image `𝔽_p[X]`).

`two_level_dvd_det_of_families`: let `Y` be square over `R`.  Suppose there are `a` row vectors
`X i` and `a` column vectors `Z j` over `R`, with linearly independent reductions, such that
`X·Y ≡ 0` and `Y·Z ≡ 0` modulo `π`, and `X·Y·Z = π·H` with `rank (H mod π) ≤ b`.  Then
`π^(a + (a - b)) ∣ det Y`.

No change of basis of the whole space is assumed: the families are completed to bases of `K^κ`
(`exists_completion`), and the completions are lifted to `R` by clearing denominators.  This is
what makes the principle apply to a principal minor of a matrix that carries a two-level witness
(`UFMember.Minor`): the kernel vectors of the full matrix that are supported on the retained
indices form such families, although the full changes of basis do not restrict.
-/

open Matrix Finset Module

namespace CatalanCore.Uniform.Content.UFMember

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- Clearing denominators for a vector over `K`. -/
theorem exists_vec_lift {κ : Type*} [Fintype κ] (φ : R →+* K)
    (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z) (w : κ → K) :
    ∃ (c : R) (x : κ → R), φ c ≠ 0 ∧ ∀ t, φ (x t) = φ c * w t := by
  classical
  choose r d hd hrd using fun t => hlift (w t)
  refine ⟨∏ t, d t, fun t => r t * ∏ u ∈ univ.erase t, d u, ?_, fun t => ?_⟩
  · rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun t _ => hd t
  · rw [map_mul, map_prod, map_prod, hrd t,
      ← Finset.mul_prod_erase univ (fun u => φ (d u)) (mem_univ t)]
    ring

/-- Completion of a family with independent reductions to a matrix that is invertible modulo `π`,
for a prescribed identification `e` of the index sets. -/
theorem exists_completion {κ : Type*} [Fintype κ] [DecidableEq κ] (φ : R →+* K)
    (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z) {a : ℕ} (X : Matrix (Fin a) κ R)
    (hX : LinearIndependent K (fun i t => φ (X i t)))
    (e : Fin a ⊕ Fin (Fintype.card κ - a) ≃ κ) :
    ∃ Wr : Matrix (Fin (Fintype.card κ - a)) κ R,
      IsUnit (((Matrix.fromRows X Wr).submatrix id e).map φ) := by
  classical
  set v : Fin a → κ → K := fun i t => φ (X i t) with hv
  set S : Submodule K (κ → K) := Submodule.span K (Set.range v)
  obtain ⟨T, hT⟩ := S.exists_isCompl
  have hS : finrank K S = a := by
    simpa using finrank_span_eq_card hX
  have hn : finrank K S + finrank K T = Fintype.card κ := by
    rw [Submodule.finrank_add_eq_of_isCompl hT, Module.finrank_fintype_fun_eq_card]
  let bT : Basis (Fin (Fintype.card κ - a)) K T := Module.finBasisOfFinrankEq K T (by omega)
  choose c x hc hx using fun j => exists_vec_lift φ hlift (bT j : κ → K)
  refine ⟨fun j t => x j t, ?_⟩
  rw [← linearIndependent_rows_iff_isUnit]
  set w : Fin (Fintype.card κ - a) → κ → K := fun j => φ (c j) • (bT j : κ → K) with hw
  have hw' : LinearIndependent K w := by
    have h1 : LinearIndependent K (fun j => (bT j : κ → K)) :=
      bT.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
    have h2 := h1.units_smul (fun j => Units.mk0 (φ (c j)) (hc j))
    convert h2 using 1
    funext j
    simp [w, Units.smul_def]
  have hdisj : Disjoint (Submodule.span K (Set.range v)) (Submodule.span K (Set.range w)) := by
    refine hT.disjoint.mono_right (Submodule.span_le.2 ?_)
    rintro _ ⟨j, rfl⟩
    exact T.smul_mem _ (bT j).2
  have hsum : LinearIndependent K (Sum.elim v w) := hX.sum_type hw' hdisj
  have hinj : Function.Injective (LinearMap.funLeft K K e) :=
    LinearMap.funLeft_injective_of_surjective _ _ e e.surjective
  have h3 := hsum.map' (LinearMap.funLeft K K e) (LinearMap.ker_eq_bot.2 hinj)
  convert h3 using 1
  funext α β
  rcases α with i | j
  · show φ (X i (e β)) = φ (X i (e β))
    rfl
  · show φ (x j (e β)) = φ (c j) * (bT j : κ → K) (e β)
    exact hx j (e β)

/-- **Two-level principle from kernel families.** -/
theorem two_level_dvd_det_of_families {κ : Type*} [Fintype κ] [DecidableEq κ]
    (φ : R →+* K) {π : R} (hπ : Prime π) (hker : ∀ x, φ x = 0 ↔ π ∣ x)
    (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z) {a : ℕ}
    (Y : Matrix κ κ R) (X : Matrix (Fin a) κ R) (Z : Matrix κ (Fin a) R)
    (hX : LinearIndependent K (fun i t => φ (X i t)))
    (hZ : LinearIndependent K (fun j t => φ (Z t j)))
    (hXY : ∀ i t, π ∣ (X * Y) i t) (hYZ : ∀ t j, π ∣ (Y * Z) t j)
    (H : Matrix (Fin a) (Fin a) R) (hH : X * Y * Z = π • H) (b : ℕ)
    (hrank : (H.map φ).rank ≤ b) :
    π ^ (a + (a - b)) ∣ Y.det := by
  classical
  have ha : a ≤ Fintype.card κ := by
    simpa using hX.fintype_card_le_finrank
  let e : Fin a ⊕ Fin (Fintype.card κ - a) ≃ κ :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  obtain ⟨Wr, hWr⟩ := exists_completion φ hlift X hX e
  obtain ⟨Wc, hWc⟩ := exists_completion φ hlift Zᵀ hZ e
  choose QX hQX using hXY
  choose QZ hQZ using hYZ
  have hXY' : X * Y = π • Matrix.of QX := by ext i t; simp [hQX i t]
  have hYZ' : Y * Z = π • Matrix.of QZ := by ext t j; simp [hQZ t j]
  set L := (Matrix.fromRows X Wr).submatrix id e
  set P := ((Matrix.fromRows Zᵀ Wc).submatrix id e)ᵀ
  have hL : φ L.det ≠ 0 := by
    rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hWr).ne_zero
  have hP : φ P.det ≠ 0 := by
    rw [Matrix.det_transpose, RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hWc).ne_zero
  have hLMP : L * Y.submatrix e e * P =
      Matrix.fromRows X Wr * Y * Matrix.fromCols Z Wcᵀ := by
    have hPe : P = (Matrix.fromCols Z Wcᵀ).submatrix e id := by
      simp only [P, Matrix.transpose_submatrix, Matrix.transpose_fromRows, Matrix.transpose_transpose]
    rw [hPe, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  have hform : L * Y.submatrix e e * P =
      Matrix.fromBlocks (π • H) (π • (Matrix.of QX * Wcᵀ)) (π • (Wr * Matrix.of QZ))
        (Wr * Y * Wcᵀ) := by
    rw [hLMP, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, hH, hXY', Matrix.mul_assoc Wr Y Z,
      hYZ', Matrix.smul_mul, Matrix.mul_smul]
  have h := CatalanCore.Linalg.two_level_dvd_det_of_primitive_changes φ hπ hker (Y.submatrix e e) L P hL hP H
    (Matrix.of QX * Wcᵀ) (Wr * Matrix.of QZ) (Wr * Y * Wcᵀ) b hrank hform
  rwa [Matrix.det_submatrix_equiv_self, Fintype.card_fin] at h

end CatalanCore.Uniform.Content.UFMember
