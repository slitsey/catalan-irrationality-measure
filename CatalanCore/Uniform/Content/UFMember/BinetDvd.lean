module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Tactic

@[expose] public section

/-!
# UF member package: Cauchy–Binet in divisibility form

`det_mul_dvd_of_rows`: for `A : κ × ι` and `B : ι × κ`, if `d` divides every maximal row minor
`det B[f, ·]` (`f : κ → ι` injective), then `d ∣ det (A B)`.  Proof: multilinearity of `det` in
the rows, `det (A B) = Σ_f (Π_i A_{i,f i}) det B[f, ·]`, and non-injective `f` give repeated
rows.  `det_mul_mul_dvd_of_minors` is the two-sided version: `d` dividing every `|κ|`-minor of
`M` divides `det (X M Z)`.  This is all of Cauchy–Binet that the member transfer needs.
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFMember

variable {R : Type*} [CommRing R] {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
  [DecidableEq ι]

/-- **Cauchy–Binet, divisibility form (rows).** -/
theorem det_mul_dvd_of_rows (A : Matrix κ ι R) (B : Matrix ι κ R) (d : R)
    (h : ∀ f : κ → ι, Function.Injective f → d ∣ (B.submatrix f id).det) :
    d ∣ (A * B).det := by
  have hrow : (A * B : Matrix κ κ R) = fun i => ∑ l, A i l • B l := by
    funext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have hexp : (A * B).det = ∑ r : κ → ι, (∏ i, A i (r i)) * (B.submatrix r id).det := by
    have h1 : (A * B).det = Matrix.detRowAlternating (fun i => ∑ l, A i l • B l) := by
      rw [← hrow]; rfl
    have hs := (Matrix.detRowAlternating (R := R) (n := κ)).toMultilinearMap.map_sum
      (fun (i : κ) (l : ι) => A i l • B l)
    rw [h1]
    refine hs.trans (Finset.sum_congr rfl fun r _ => ?_)
    have := (Matrix.detRowAlternating (R := R) (n := κ)).map_smul_univ (fun i => A i (r i))
      (fun i => B (r i))
    rw [smul_eq_mul] at this
    exact this
  rw [hexp]
  refine Finset.dvd_sum fun r _ => ?_
  by_cases hr : Function.Injective r
  · exact dvd_mul_of_dvd_right (h r hr) _
  · have h0 : (B.submatrix r id).det = 0 := by
      simp only [Function.Injective, not_forall] at hr
      obtain ⟨i, j, hij, hne⟩ := hr
      exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
    rw [h0, mul_zero]
    exact dvd_zero _

/-- **Cauchy–Binet, divisibility form (columns).** -/
theorem det_mul_dvd_of_cols (A : Matrix κ ι R) (B : Matrix ι κ R) (d : R)
    (h : ∀ g : κ → ι, Function.Injective g → d ∣ (A.submatrix id g).det) :
    d ∣ (A * B).det := by
  rw [← Matrix.det_transpose, Matrix.transpose_mul]
  refine det_mul_dvd_of_rows Bᵀ Aᵀ d fun g hg => ?_
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  exact h g hg

/-- **Cauchy–Binet, two-sided divisibility form.** -/
theorem det_mul_mul_dvd_of_minors (X : Matrix κ ι R) (M : Matrix ι ι R) (Z : Matrix ι κ R)
    (d : R) (h : ∀ f g : κ → ι, Function.Injective f → Function.Injective g →
      d ∣ (M.submatrix f g).det) :
    d ∣ (X * M * Z).det := by
  rw [Matrix.mul_assoc]
  refine det_mul_dvd_of_rows X (M * Z) d fun f hf => ?_
  have e : (M * Z).submatrix f id = M.submatrix f id * Z := by
    ext i j; simp [Matrix.mul_apply]
  rw [e]
  refine det_mul_dvd_of_cols (M.submatrix f id) Z d fun g hg => ?_
  exact h f g hf hg

/-- Minors through primitive changes of basis: `(det L · det P)^|κ| det Bl[e₁,e₂]` is a
`|κ|`-minor combination of `L Bl P` (adjugates). -/
theorem det_submatrix_mul_pow_dvd (Bl L P : Matrix ι ι R) (e₁ e₂ : κ → ι) (d : R)
    (h : ∀ f g : κ → ι, Function.Injective f → Function.Injective g →
      d ∣ ((L * Bl * P).submatrix f g).det) :
    d ∣ (L.det * P.det) ^ Fintype.card κ * (Bl.submatrix e₁ e₂).det := by
  have hadj : L.adjugate * (L * Bl * P) * P.adjugate = (L.det * P.det) • Bl := by
    calc L.adjugate * (L * Bl * P) * P.adjugate
        = (L.adjugate * L) * Bl * (P * P.adjugate) := by simp only [Matrix.mul_assoc]
      _ = (L.det • (1 : Matrix ι ι R)) * Bl * (P.det • (1 : Matrix ι ι R)) := by
          rw [Matrix.adjugate_mul, Matrix.mul_adjugate]
      _ = (L.det * P.det) • Bl := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
          rw [mul_comm]
  have hsub : ((L.det * P.det) • Bl).submatrix e₁ e₂ =
      L.adjugate.submatrix e₁ id * (L * Bl * P) * P.adjugate.submatrix id e₂ := by
    rw [← hadj]
    ext i j
    simp [Matrix.mul_apply]
  have := det_mul_mul_dvd_of_minors (L.adjugate.submatrix e₁ id) (L * Bl * P)
    (P.adjugate.submatrix id e₂) d h
  have hsm : ((L.det * P.det) • Bl).submatrix e₁ e₂ = (L.det * P.det) • Bl.submatrix e₁ e₂ := by
    ext i j; simp
  rw [← hsub, hsm, Matrix.det_smul] at this
  exact this

end CatalanCore.Uniform.Content.UFMember
