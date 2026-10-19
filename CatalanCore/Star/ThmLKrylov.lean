module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Star.ThmLKrylov: `det` of the adjugate-Krylov matrix of a pencil `zH - G`

`adj(zH - G) = adj(charmatrix B) * (adj H).map C` with `B = H⁻¹ G`, and the coefficients
`P m` of `adj (charmatrix B)` satisfy `P m = B * P (m+1) + c_{m+1} • 1`, `P (n-1) = 1`,
so `P (n-1-k) = p_k(B)` with `p_k` monic of degree `k`.
-/

@[expose] public section

open Matrix Polynomial

namespace CatalanCore.Star.ThmL

variable {F : Type*} [Field F] {n : ℕ}

/-- `z•H - G` over `F[z]`. -/
noncomputable def zpen (H G : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F[X] :=
  Matrix.of fun r c => X * C (H r c) - C (G r c)

/-- Krylov matrix with rows `ν^T B^k`. -/
noncomputable def krylovMat (B : Matrix (Fin n) (Fin n) F) (ν : Fin n → F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of fun k i => (ν ᵥ* B ^ (k : ℕ)) i

/-- `C[k,i] = coeff_{n-1-k}` of `(ν^T adj(zH-G))_i`. -/
noncomputable def adjKry (H G : Matrix (Fin n) (Fin n) F) (ν : Fin n → F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of fun k i => (∑ r, C (ν r) * (adjugate (zpen H G)) r i).coeff (n - 1 - k)

lemma adjKry_apply (H G : Matrix (Fin n) (Fin n) F) (ν : Fin n → F) (k i : Fin n) :
    adjKry H G ν k i = (∑ r, C (ν r) * (adjugate (zpen H G)) r i).coeff (n - 1 - k) := rfl

lemma krylovMat_apply (B : Matrix (Fin n) (Fin n) F) (ν : Fin n → F) (k i : Fin n) :
    krylovMat B ν k i = (ν ᵥ* B ^ (k : ℕ)) i := rfl

/-- Coefficient matrices of `adj (charmatrix B)`. -/
noncomputable def adjCoeff (B : Matrix (Fin n) (Fin n) F) (m : ℕ) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun r i => (adjugate (charmatrix B) r i).coeff m

lemma adjCoeff_rec (B : Matrix (Fin n) (Fin n) F) (m : ℕ) :
    adjCoeff B m = B * adjCoeff B (m + 1) + (B.charpoly.coeff (m + 1)) • (1 : Matrix _ _ F) := by
  ext r i
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) F[X] => (M r i).coeff (m + 1))
    (mul_adjugate (charmatrix B))
  have e : (charmatrix B).det = B.charpoly := rfl
  simp only [Matrix.mul_apply, charmatrix_apply, diagonal_apply, Matrix.smul_apply, e,
    Matrix.one_apply] at h
  simp only [adjCoeff, of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  simp only [sub_mul, ite_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, zero_mul, coeff_sub, finsetSum_coeff, coeff_C_mul, coeff_X_mul] at h
  by_cases hri : r = i
  · subst hri
    simp only [smul_eq_mul, ite_true, mul_one] at h ⊢
    linear_combination h
  · simp only [hri, ite_false, mul_zero, smul_eq_mul, coeff_zero, add_zero] at h ⊢
    linear_combination h

lemma adjCoeff_eventually_zero (B : Matrix (Fin n) (Fin n) F) :
    ∃ D, ∀ m ≥ D, adjCoeff B m = 0 := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ r i : Fin n, (adjugate (charmatrix B) r i).natDegree ≤ D := by
    obtain ⟨D, hD⟩ := (Set.finite_range (fun p : Fin n × Fin n => (adjugate (charmatrix B) p.1 p.2).natDegree)).bddAbove
    exact ⟨D, fun r i => hD ⟨(r, i), rfl⟩⟩
  refine ⟨D + 1, fun m hm => ?_⟩
  ext r i
  have := coeff_eq_zero_of_natDegree_lt (p := adjugate (charmatrix B) r i)
    (lt_of_le_of_lt (hD r i) (by omega : D < m))
  simpa [adjCoeff] using this

lemma charpoly_coeff_eq_zero (B : Matrix (Fin n) (Fin n) F) {m : ℕ} (hm : n < m) :
    B.charpoly.coeff m = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  simpa using hm

lemma adjCoeff_zero_of_ge (B : Matrix (Fin n) (Fin n) F) {m : ℕ} (hm : n ≤ m) :
    adjCoeff B m = 0 := by
  obtain ⟨D, hD⟩ := adjCoeff_eventually_zero B
  have key : ∀ d m : ℕ, n ≤ m → D ≤ m + d → adjCoeff B m = 0 := by
    intro d
    induction d with
    | zero => intro m _ h; exact hD m (by omega)
    | succ d ih =>
      intro m hnm h
      rw [adjCoeff_rec, ih (m + 1) (by omega) (by omega), charpoly_coeff_eq_zero B (by omega)]
      simp
  exact key D m hm (by omega)

lemma adjCoeff_top (B : Matrix (Fin n) (Fin n) F) (hn : 0 < n) :
    adjCoeff B (n - 1) = 1 := by
  have h := adjCoeff_rec B (n - 1)
  rw [adjCoeff_zero_of_ge B (by omega : n ≤ n - 1 + 1)] at h
  have hc : B.charpoly.coeff (n - 1 + 1) = 1 := by
    have : n - 1 + 1 = n := by omega
    rw [this]
    have := (Matrix.charpoly_monic B).coeff_natDegree
    simpa using this
  rw [hc] at h
  simpa using h

/-- `P (n-1-k)` is a monic polynomial of degree `k` in `B`. -/
lemma adjCoeff_poly (B : Matrix (Fin n) (Fin n) F) :
    ∀ k : ℕ, k < n → ∃ p : F[X], p.Monic ∧ p.natDegree = k ∧
      adjCoeff B (n - 1 - k) = aeval B p := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact ⟨1, monic_one, natDegree_one, by simp [adjCoeff_top B hk]⟩
  | succ k ih =>
    intro hk
    obtain ⟨p, hm, hd, he⟩ := ih (by omega)
    have hXp : (X * p).natDegree = k + 1 := by rw [natDegree_X_mul hm.ne_zero, hd]
    have hlt : (C (B.charpoly.coeff (n - 1 - k))).natDegree < (X * p).natDegree := by
      rw [natDegree_C, hXp]; omega
    refine ⟨X * p + C (B.charpoly.coeff (n - 1 - k)), ?_, ?_, ?_⟩
    · exact (monic_X.mul hm).add_of_left (degree_lt_degree hlt)
    · rw [natDegree_add_eq_left_of_natDegree_lt hlt, hXp]
    · have := adjCoeff_rec B (n - 1 - (k + 1))
      have e : n - 1 - (k + 1) + 1 = n - 1 - k := by omega
      rw [e, he] at this
      rw [this]
      simp [map_add, map_mul, Algebra.algebraMap_eq_smul_one]

lemma zpen_eq (H G : Matrix (Fin n) (Fin n) F) (hH : IsUnit H.det) :
    zpen H G = (C : F →+* F[X]).mapMatrix H * charmatrix (H⁻¹ * G) := by
  have h1 : (C : F →+* F[X]).mapMatrix H * (C : F →+* F[X]).mapMatrix (H⁻¹ * G)
      = (C : F →+* F[X]).mapMatrix G := by
    rw [← map_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hH, Matrix.one_mul]
  rw [charmatrix, mul_sub, h1]
  ext r c
  simp [zpen, Matrix.mul_apply, Matrix.scalar_apply, diagonal_apply]

lemma adjKry_eq (H G : Matrix (Fin n) (Fin n) F) (hH : IsUnit H.det) (ν : Fin n → F)
    (k i : Fin n) :
    adjKry H G ν k i =
      (ν ᵥ* (adjCoeff (H⁻¹ * G) (n - 1 - k) * adjugate H)) i := by
  rw [adjKry_apply, zpen_eq H G hH, adjugate_mul_distrib, ← RingHom.map_adjugate]
  simp [adjCoeff, Matrix.mul_apply, Matrix.vecMul, dotProduct, finsetSum_coeff, coeff_C_mul,
    coeff_mul_C]

/-- Unit lower triangular `L` with `adjCoeff B (n-1-k) = Σ_j L k j • B^j`. -/
lemma exists_L (B : Matrix (Fin n) (Fin n) F) :
    ∃ L : Matrix (Fin n) (Fin n) F, (∀ k j : Fin n, k < j → L k j = 0) ∧ (∀ k, L k k = 1) ∧
      ∀ k : Fin n, adjCoeff B (n - 1 - k) = ∑ j : Fin n, L k j • B ^ (j : ℕ) := by
  have h : ∀ k : Fin n, ∃ p : F[X], p.Monic ∧ p.natDegree = k ∧
      adjCoeff B (n - 1 - k) = aeval B p := fun k => adjCoeff_poly B k k.2
  choose p hm hd he using h
  refine ⟨Matrix.of fun k j => (p k).coeff j, ?_, ?_, ?_⟩
  · intro k j hkj
    exact coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hkj)
  · intro k
    have := (hm k).coeff_natDegree
    rw [hd] at this
    simpa using this
  · intro k
    rw [he k, aeval_eq_sum_range' (n := n) (by rw [hd]; exact k.2),
      ← Fin.sum_univ_eq_sum_range (fun j => (p k).coeff j • B ^ j)]
    rfl

theorem adjKry_eq_mul (H G : Matrix (Fin n) (Fin n) F) (hH : IsUnit H.det) (ν : Fin n → F) :
    ∃ L : Matrix (Fin n) (Fin n) F, L.IsLowerTriangular ∧ (∀ k, L k k = 1) ∧
      adjKry H G ν = L * (krylovMat (H⁻¹ * G) ν * adjugate H) := by
  obtain ⟨L, hL0, hL1, hL⟩ := exists_L (H⁻¹ * G)
  refine ⟨L, fun i j hij => hL0 i j hij, hL1, ?_⟩
  ext k i
  rw [adjKry_eq H G hH, hL k]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, krylovMat, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul, Matrix.smul_apply]
  rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem det_adjKry (H G : Matrix (Fin n) (Fin n) F) (hH : IsUnit H.det) (ν : Fin n → F) :
    (adjKry H G ν).det = (krylovMat (H⁻¹ * G) ν).det * H.det ^ (n - 1) := by
  obtain ⟨L, hL, hL1, he⟩ := adjKry_eq_mul H G hH ν
  rw [he, det_mul, det_mul, det_of_isLowerTriangular L hL]
  simp [hL1, det_adjugate]

end CatalanCore.Star.ThmL
