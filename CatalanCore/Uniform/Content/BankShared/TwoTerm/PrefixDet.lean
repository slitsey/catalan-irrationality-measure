module

public import CatalanCore.Linalg.TwoLevelDet

@[expose] public section
set_option Elab.async false

/-! # The determinant step of the prefix rule (paper `prefix-rule-2026-10-29`, Step 5)

Pure algebra over a commutative domain `R` with a prime `π` and a reduction `φ : R → K`
(`ker φ = (π)`):

* `pow_dvd_det_rowcol`: if the rows in `A` and the columns in `B` of `M` are divisible by `π` and
  the `A × B` corner by `π²`, then `π^(|A| + |B|) ∣ det M`;
* `det_ne_zero_of_pivots`: a matrix that is the identity outside the pivot rows `T` and diagonal
  with nonzero entries on `T × T` is nonsingular;
* `pow_dvd_det_of_pivots`: row vectors `ℓ i` (`i ∈ T`) killing `B` modulo `π`, column vectors
  `κ j` (`j ∈ T'`) killing `B` modulo `π`, with pairings `ℓ i ᵀ B κ j ≡ 0 (mod π²)` and
  pivots (`φ (ℓ i i) ≠ 0`, `φ (ℓ i i') = 0` for other pivots `i'`), give
  `π^(|T| + |T'|) ∣ det B`.  No unimodular completion is needed: the change of basis is the
  identity off the pivots. -/

open Matrix Finset

namespace CatalanCore.Uniform.Content.BankShared.TwoTerm

section PrefixDet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Rows, columns and corner.** -/
theorem pow_dvd_det_rowcol {R : Type*} [CommRing R] (π : R) (M : Matrix ι ι R) (A B : Finset ι)
    (hrow : ∀ i ∈ A, ∀ j, π ∣ M i j) (hcol : ∀ i, ∀ j ∈ B, π ∣ M i j)
    (hcorner : ∀ i ∈ A, ∀ j ∈ B, π ^ 2 ∣ M i j) :
    π ^ (A.card + B.card) ∣ M.det := by
  let dA : ι → R := fun i => if i ∈ A then π else 1
  let dB : ι → R := fun j => if j ∈ B then π else 1
  have hd : ∀ i j, ∃ c, M i j = dA i * dB j * c := by
    intro i j
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ B
    · obtain ⟨c, hc⟩ := hcorner i hi j hj
      exact ⟨c, by simp only [dA, dB, if_pos hi, if_pos hj]; rw [hc]; ring⟩
    · obtain ⟨c, hc⟩ := hrow i hi j
      exact ⟨c, by simp only [dA, dB, if_pos hi, if_neg hj]; rw [hc]; ring⟩
    · obtain ⟨c, hc⟩ := hcol i j hj
      exact ⟨c, by simp only [dA, dB, if_neg hi, if_pos hj]; rw [hc]; ring⟩
    · exact ⟨M i j, by simp only [dA, dB, if_neg hi, if_neg hj]; ring⟩
  choose N hN using hd
  have hM : M = diagonal dA * Matrix.of N * diagonal dB := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, hN i j]
    ring
  have hA : ∏ i, dA i = π ^ A.card := by
    simp only [dA]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  have hB : ∏ j, dB j = π ^ B.card := by
    simp only [dB]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  rw [hM, det_mul, det_mul, det_diagonal, det_diagonal, hA, hB, pow_add]
  exact ⟨(Matrix.of N).det, by ring⟩

/-- **Pivot matrices are nonsingular.** -/
theorem det_ne_zero_of_pivots {K : Type*} [Field K] (T : Finset ι) (M : Matrix ι ι K)
    (hout : ∀ i, i ∉ T → ∀ j, i ≠ j → M i j = 0) (hout1 : ∀ i, i ∉ T → M i i = 1)
    (hin : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → M i j = 0) (hdiag : ∀ i ∈ T, M i i ≠ 0) :
    M.det ≠ 0 := by
  rw [det_apply, Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.one_apply]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    by_cases hi : i ∈ T
    · exact hdiag i hi
    · rw [hout1 i hi]; exact one_ne_zero
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      push_neg at h
      exact hσ (Equiv.ext h)
    obtain ⟨i', hi'⟩ : ∃ i', M (σ i') i' = 0 := by
      by_cases h1 : σ i ∈ T
      · by_cases h2 : i ∈ T
        · exact ⟨i, hin _ h1 _ h2 hi⟩
        · refine ⟨σ.symm i, ?_⟩
          have e : σ (σ.symm i) = i := σ.apply_symm_apply i
          rw [e]
          have hne : i ≠ σ.symm i := by
            intro h
            apply hi
            have := congrArg σ h
            rw [e] at this
            exact this
          exact hout i h2 (σ.symm i) hne
      · exact ⟨i, hout _ h1 _ hi⟩
    rw [Finset.prod_eq_zero (f := fun j => M (σ j) j) (Finset.mem_univ i') hi', smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The pivot form of Step 5.** -/
theorem pow_dvd_det_of_pivots {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    (φ : R →+* K) {π : R} (hπ : Prime π) (hker : ∀ x, φ x = 0 ↔ π ∣ x)
    (B : Matrix ι ι R) (T T' : Finset ι) (ℓ κ : ι → ι → R)
    (hℓd : ∀ i ∈ T, φ (ℓ i i) ≠ 0) (hℓo : ∀ i ∈ T, ∀ i' ∈ T, i ≠ i' → φ (ℓ i i') = 0)
    (hκd : ∀ j ∈ T', φ (κ j j) ≠ 0) (hκo : ∀ j ∈ T', ∀ j' ∈ T', j ≠ j' → φ (κ j j') = 0)
    (hrow : ∀ i ∈ T, ∀ l, π ∣ ∑ k, ℓ i k * B k l)
    (hcol : ∀ j ∈ T', ∀ k, π ∣ ∑ l, B k l * κ j l)
    (hpair : ∀ i ∈ T, ∀ j ∈ T', π ^ 2 ∣ ∑ k, ∑ l, ℓ i k * B k l * κ j l) :
    π ^ (T.card + T'.card) ∣ B.det := by
  let L : Matrix ι ι R := Matrix.of fun i k => if i ∈ T then ℓ i k else (1 : Matrix ι ι R) i k
  let P : Matrix ι ι R := Matrix.of fun l j => if j ∈ T' then κ j l else (1 : Matrix ι ι R) l j
  have hL : ∀ (Q : Matrix ι ι R) i l, (L * Q) i l = if i ∈ T then ∑ k, ℓ i k * Q k l else Q i l := by
    intro Q i l
    by_cases hi : i ∈ T
    · simp [L, Matrix.mul_apply, hi]
    · simp [L, Matrix.mul_apply, hi, Matrix.one_apply]
  have hP : ∀ (Q : Matrix ι ι R) i j, (Q * P) i j = if j ∈ T' then ∑ l, Q i l * κ j l else Q i j := by
    intro Q i j
    by_cases hj : j ∈ T'
    · simp [P, Matrix.mul_apply, hj]
    · simp [P, Matrix.mul_apply, hj, Matrix.one_apply]
  have hswap : ∀ i j, ∑ l, (∑ k, ℓ i k * B k l) * κ j l = ∑ k, ∑ l, ℓ i k * B k l * κ j l := by
    intro i j
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hdvd : π ^ (T.card + T'.card) ∣ (L * B * P).det := by
    refine pow_dvd_det_rowcol π (L * B * P) T T' ?_ ?_ ?_
    · intro i hi j
      rw [hP]
      simp only [hL B i, if_pos hi]
      split_ifs with hj
      · rw [hswap]
        exact (dvd_pow_self π two_ne_zero).trans (hpair i hi j hj)
      · exact hrow i hi j
    · intro i j hj
      rw [hP, if_pos hj]
      by_cases hi : i ∈ T
      · simp only [hL B i, if_pos hi]
        rw [hswap]
        exact (dvd_pow_self π two_ne_zero).trans (hpair i hi j hj)
      · simp only [hL B i, if_neg hi]
        exact hcol j hj i
    · intro i hi j hj
      rw [hP, if_pos hj]
      simp only [hL B i, if_pos hi]
      rw [hswap]
      exact hpair i hi j hj
  have hLne : φ L.det ≠ 0 := by
    rw [RingHom.map_det]
    refine det_ne_zero_of_pivots T _ ?_ ?_ ?_ ?_
    · intro i hi j hij
      simp [L, hi, Matrix.one_apply_ne hij]
    · intro i hi
      simp [L, hi]
    · intro i hi j hj hij
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, L, Matrix.of_apply, if_pos hi]
      exact hℓo i hi j hj hij
    · intro i hi
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, L, Matrix.of_apply, if_pos hi]
      exact hℓd i hi
  have hPne : φ P.det ≠ 0 := by
    rw [← Matrix.det_transpose, RingHom.map_det]
    refine det_ne_zero_of_pivots T' _ ?_ ?_ ?_ ?_
    · intro j hj l hjl
      simp [P, hj, Matrix.one_apply_ne (Ne.symm hjl)]
    · intro j hj
      simp [P, hj]
    · intro j hj l hl hjl
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, P,
        Matrix.of_apply, if_pos hj]
      exact hκo j hj l hl hjl
    · intro j hj
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, P,
        Matrix.of_apply, if_pos hj]
      exact hκd j hj
  have hndL : ¬ π ∣ L.det := fun h => hLne ((hker _).2 h)
  have hndP : ¬ π ∣ P.det := fun h => hPne ((hker _).2 h)
  rw [det_mul, det_mul] at hdvd
  have h1 : π ^ (T.card + T'.card) ∣ L.det * (B.det * P.det) := by
    rw [← mul_assoc]; exact hdvd
  have h2 := hπ.pow_dvd_of_dvd_mul_left _ hndL h1
  rw [mul_comm] at h2
  exact hπ.pow_dvd_of_dvd_mul_left _ hndP h2

end PrefixDet

end CatalanCore.Uniform.Content.BankShared.TwoTerm

#print axioms CatalanCore.Uniform.Content.BankShared.TwoTerm.pow_dvd_det_rowcol
#print axioms CatalanCore.Uniform.Content.BankShared.TwoTerm.det_ne_zero_of_pivots
#print axioms CatalanCore.Uniform.Content.BankShared.TwoTerm.pow_dvd_det_of_pivots
