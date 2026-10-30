module

public import CatalanCore.Linalg.KrylovTri
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Bordered Krylov determinants (package H3, part 1)

`bmat W E = [W | E]` (a `(m+n) × (m+n)` matrix: `m` border columns, then `n` more) and
`bkdet W B v = det [W | v, B v, …, B^{n-1} v]`, the bordered Krylov determinant `u(B, v)`.

* `det_bmat_comb`: replacing the Krylov block by `E M + W X` multiplies the determinant by `det M`.
* `bkdet_cross_ratio` (bordered L1): if `B, T` preserve `range W`, commute modulo `range W`, and
  `T` has a cyclic start vector, then `u(B,v) u(T,v') = u(B,v') u(T,v)`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {m n : ℕ}

/-- `[W | E]`. -/
def bmat (W : Matrix (Fin (m + n)) (Fin m) F) (E : Matrix (Fin (m + n)) (Fin n) F) :
    Matrix (Fin (m + n)) (Fin (m + n)) F :=
  Matrix.of fun i j => Fin.addCases (W i) (E i) j

/-- The Krylov block `[v, B v, …, B^{n-1} v]`. -/
def krylovE (B : Matrix (Fin (m + n)) (Fin (m + n)) F) (v : Fin (m + n) → F) :
    Matrix (Fin (m + n)) (Fin n) F :=
  Matrix.of fun i k => ((B ^ (k : ℕ)) *ᵥ v) i

/-- Bordered Krylov determinant `u(B, v) = det [W | v, B v, …, B^{n-1} v]`. -/
def bkdet (W : Matrix (Fin (m + n)) (Fin m) F) (B : Matrix (Fin (m + n)) (Fin (m + n)) F)
    (v : Fin (m + n) → F) : F :=
  (bmat W (krylovE B v)).det

/-- The submodule `range W`. -/
def Wsp (W : Matrix (Fin (m + n)) (Fin m) F) : Submodule F (Fin (m + n) → F) :=
  LinearMap.range (Matrix.mulVecLin W)

lemma mem_Wsp {W : Matrix (Fin (m + n)) (Fin m) F} {x : Fin (m + n) → F} :
    x ∈ Wsp W ↔ ∃ a, W *ᵥ a = x := Iff.rfl

lemma bmat_mulVec (W : Matrix (Fin (m + n)) (Fin m) F) (E : Matrix (Fin (m + n)) (Fin n) F)
    (z : Fin (m + n) → F) :
    bmat W E *ᵥ z = W *ᵥ (fun i => z (Fin.castAdd n i)) + E *ᵥ (fun j => z (Fin.natAdd m j)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, bmat, Fin.sum_univ_add]

lemma det_bmat_comb (W : Matrix (Fin (m + n)) (Fin m) F) (E : Matrix (Fin (m + n)) (Fin n) F)
    (M : Matrix (Fin n) (Fin n) F) (X : Matrix (Fin m) (Fin n) F) :
    (bmat W (E * M + W * X)).det = M.det * (bmat W E).det := by
  have h : bmat W (E * M + W * X) = bmat W E *
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 X 0 M) := by
    ext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [bmat, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]
    · simp [bmat, Matrix.mul_apply, Fin.sum_univ_add]
      exact add_comm _ _
  rw [h, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp [mul_comm]

/-! ### Cyclic spanning -/

/-- If `u(T, v₀) ≠ 0`, every vector is a combination of `T^j v₀` modulo `range W`. -/
lemma exists_comb_of_bkdet_ne_zero {W : Matrix (Fin (m + n)) (Fin m) F}
    {T : Matrix (Fin (m + n)) (Fin (m + n)) F} {v₀ : Fin (m + n) → F}
    (hcyc : bkdet W T v₀ ≠ 0) (y : Fin (m + n) → F) :
    ∃ c : Fin n → F, y - ∑ j : Fin n, c j • (T ^ (j : ℕ) *ᵥ v₀) ∈ Wsp W := by
  have hu : IsUnit (bmat W (krylovE T v₀)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hcyc)
  set P := bmat W (krylovE T v₀) with hP
  set z := P⁻¹ *ᵥ y with hz
  have hy : P *ᵥ z = y := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
      Matrix.one_mulVec]
  refine ⟨fun j => z (Fin.natAdd m j), ?_⟩
  rw [← hy, hP, bmat_mulVec]
  refine ⟨fun i => z (Fin.castAdd n i), ?_⟩
  have : krylovE T v₀ *ᵥ (fun j => z (Fin.natAdd m j)) =
      ∑ j : Fin n, z (Fin.natAdd m j) • (T ^ (j : ℕ) *ᵥ v₀) := by
    ext i
    simp [Matrix.mulVec, dotProduct, krylovE, Finset.sum_apply, mul_comm]
  rw [this]
  abel

/-! ### Commuting operators modulo `range W` -/

section Cross

variable {W : Matrix (Fin (m + n)) (Fin m) F} {N T : Matrix (Fin (m + n)) (Fin (m + n)) F}

lemma pow_mem_Wsp (hN : ∀ x ∈ Wsp W, N *ᵥ x ∈ Wsp W) (k : ℕ) :
    ∀ x ∈ Wsp W, N ^ k *ᵥ x ∈ Wsp W := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih => intro x hx; rw [pow_succ', ← Matrix.mulVec_mulVec]; exact hN _ (ih x hx)

lemma comm_pow_mem (hN : ∀ x ∈ Wsp W, N *ᵥ x ∈ Wsp W)
    (hc : ∀ x, (N * T - T * N) *ᵥ x ∈ Wsp W) (k : ℕ) (x : Fin (m + n) → F) :
    (N ^ k * T - T * N ^ k) *ᵥ x ∈ Wsp W := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have : (N ^ (k + 1) * T - T * N ^ (k + 1)) *ᵥ x =
        N *ᵥ ((N ^ k * T - T * N ^ k) *ᵥ x) + (N * T - T * N) *ᵥ (N ^ k *ᵥ x) := by
      simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, pow_succ',
        Matrix.mul_assoc, Matrix.sub_mul]
      abel
    rw [this]
    exact Submodule.add_mem _ (hN _ (ih x)) (hc _)


/-- A matrix that preserves `range W`, commutes with `T` modulo `range W`, and maps a cyclic vector
into `range W`, maps everything into `range W`. -/
lemma mem_Wsp_of_cyclic {E : Matrix (Fin (m + n)) (Fin (m + n)) F}
    (hT : ∀ x ∈ Wsp W, T *ᵥ x ∈ Wsp W) (hE : ∀ x ∈ Wsp W, E *ᵥ x ∈ Wsp W)
    (hc : ∀ x, (E * T - T * E) *ᵥ x ∈ Wsp W) {v₀ : Fin (m + n) → F}
    (hcyc : bkdet W T v₀ ≠ 0) (h0 : E *ᵥ v₀ ∈ Wsp W) (x : Fin (m + n) → F) :
    E *ᵥ x ∈ Wsp W := by
  have hi : ∀ i : ℕ, E *ᵥ (T ^ i *ᵥ v₀) ∈ Wsp W := by
    intro i
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have : E *ᵥ (T ^ (i + 1) *ᵥ v₀) =
          (E * T - T * E) *ᵥ (T ^ i *ᵥ v₀) + T *ᵥ (E *ᵥ (T ^ i *ᵥ v₀)) := by
        rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec]
        abel
      rw [this]
      exact Submodule.add_mem _ (hc _) (hT _ ih)
  obtain ⟨c, hc'⟩ := exists_comb_of_bkdet_ne_zero hcyc x
  have hx : x = (x - ∑ j : Fin n, c j • (T ^ (j : ℕ) *ᵥ v₀)) +
      ∑ j : Fin n, c j • (T ^ (j : ℕ) *ᵥ v₀) := by abel
  rw [hx, Matrix.mulVec_add, Matrix.mulVec_sum]
  refine Submodule.add_mem _ (hE _ hc') (Submodule.sum_mem _ fun j _ => ?_)
  rw [Matrix.mulVec_smul]
  exact Submodule.smul_mem _ _ (hi _)

/-- The factorisation of the Krylov block of `N` through that of `T`, modulo `range W`. -/
lemma exists_krylovE_factor (hN : ∀ x ∈ Wsp W, N *ᵥ x ∈ Wsp W)
    (hT : ∀ x ∈ Wsp W, T *ᵥ x ∈ Wsp W) (hc : ∀ x, (N * T - T * N) *ᵥ x ∈ Wsp W)
    {v₀ : Fin (m + n) → F} (hcyc : bkdet W T v₀ ≠ 0) :
    ∃ M : Matrix (Fin n) (Fin n) F, ∀ v, ∃ X : Matrix (Fin m) (Fin n) F,
      krylovE N v = krylovE T v * M + W * X := by
  choose c hc' using fun k : Fin n => exists_comb_of_bkdet_ne_zero hcyc (N ^ (k : ℕ) *ᵥ v₀)
  refine ⟨Matrix.of fun j k => c k j, fun v => ?_⟩
  have key : ∀ k : Fin n, ∀ x, (N ^ (k : ℕ) - ∑ j : Fin n, c k j • T ^ (j : ℕ)) *ᵥ x ∈ Wsp W := by
    intro k
    refine mem_Wsp_of_cyclic hT ?_ ?_ hcyc ?_
    · intro x hx
      rw [Matrix.sub_mulVec, Matrix.sum_mulVec]
      refine Submodule.sub_mem _ (pow_mem_Wsp hN _ x hx) (Submodule.sum_mem _ fun j _ => ?_)
      rw [Matrix.smul_mulVec]
      exact Submodule.smul_mem _ _ (pow_mem_Wsp hT _ x hx)
    · intro x
      have hcomm : Commute (∑ j : Fin n, c k j • T ^ (j : ℕ)) T :=
        Commute.sum_left _ _ _ fun j _ => ((Commute.refl T).pow_left _).smul_left _
      have : ((N ^ (k : ℕ) - ∑ j : Fin n, c k j • T ^ (j : ℕ)) * T -
          T * (N ^ (k : ℕ) - ∑ j : Fin n, c k j • T ^ (j : ℕ))) =
          (N ^ (k : ℕ) * T - T * N ^ (k : ℕ)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, hcomm.eq]; abel
      rw [this]
      exact comm_pow_mem hN hc _ x
    · have := hc' k
      rw [Matrix.sub_mulVec, Matrix.sum_mulVec]
      convert this using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_mulVec]
    
  have hX : ∀ k : Fin n, ∃ b : Fin m → F, W *ᵥ b = (N ^ (k : ℕ) - ∑ j : Fin n, c k j • T ^ (j : ℕ)) *ᵥ v :=
    fun k => key k v
  choose b hb using hX
  refine ⟨Matrix.of fun i k => b k i, ?_⟩
  ext i k
  have := congrFun (hb k) i
  simp only [Matrix.sub_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  simp only [krylovE, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
  have h2 : (W * Matrix.of fun i k => b k i) i k = (W *ᵥ b k) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h3 : ∑ j, W i j * b k j = (W *ᵥ b k) i := rfl
  rw [h3, this]
  have h4 : ∑ j : Fin n, ((T ^ (j : ℕ)) *ᵥ v) i * c k j = ∑ x : Fin n, c k x * (T ^ (x : ℕ) *ᵥ v) i :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h4]; ring

/-- **L1, bordered cross-ratio lemma.** -/
theorem bkdet_cross_ratio (hN : ∀ x ∈ Wsp W, N *ᵥ x ∈ Wsp W)
    (hT : ∀ x ∈ Wsp W, T *ᵥ x ∈ Wsp W) (hc : ∀ x, (N * T - T * N) *ᵥ x ∈ Wsp W)
    {v₀ : Fin (m + n) → F} (hcyc : bkdet W T v₀ ≠ 0) (v v' : Fin (m + n) → F) :
    bkdet W N v * bkdet W T v' = bkdet W N v' * bkdet W T v := by
  obtain ⟨M, hM⟩ := exists_krylovE_factor hN hT hc hcyc
  obtain ⟨X, hX⟩ := hM v
  obtain ⟨X', hX'⟩ := hM v'
  simp only [bkdet, hX, hX', det_bmat_comb]
  ring

end Cross

/-! ### Sequence form, L2 and L3 -/

section Seq

variable (W : Matrix (Fin (m + n)) (Fin m) F)

/-- The column sequence `W₀, …, W_{m-1}, e₀, e₁, …`. -/
def bcol (e : ℕ → Fin (m + n) → F) : ℕ → Fin (m + n) → F :=
  fun j => if h : j < m then fun i => W i ⟨j, by omega⟩ else e (j - m)

lemma bmat_krylovE_eq_colMat (B : Matrix (Fin (m + n)) (Fin (m + n)) F) (v : Fin (m + n) → F) :
    bmat W (krylovE B v) = colMat (bcol W fun k => B ^ k *ᵥ v) := by
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [bmat, colMat, bcol]
  · simp [bmat, colMat, bcol, krylovE]

lemma bkdet_eq (B : Matrix (Fin (m + n)) (Fin (m + n)) F) (v : Fin (m + n) → F) :
    bkdet W B v = (colMat (bcol W fun k => B ^ k *ᵥ v)).det := by
  rw [bkdet, bmat_krylovE_eq_colMat]

lemma mem_span_bcol_of_mem_Wsp (e : ℕ → Fin (m + n) → F) {x : Fin (m + n) → F}
    (hx : x ∈ Wsp W) (k : ℕ) (hk : m ≤ k) : x ∈ Submodule.span F (bcol W e '' Set.Iio k) := by
  obtain ⟨a, rfl⟩ := hx
  have : W *ᵥ a = ∑ j : Fin m, a j • bcol W e (j : ℕ) := by
    ext i
    simp [Matrix.mulVec, dotProduct, bcol, Finset.sum_apply, mul_comm]
  change W *ᵥ a ∈ _
  rw [this]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_, rfl⟩)
  have := j.2
  simp only [Set.mem_Iio]; omega

lemma bcol_of_lt (e : ℕ → Fin (m + n) → F) {j : ℕ} (hj : j < m) :
    bcol W e j ∈ Wsp W := by
  refine ⟨Pi.single ⟨j, hj⟩ 1, ?_⟩
  ext i
  simp [bcol, hj, Matrix.mulVec, dotProduct, Pi.single_apply]

omit [Field F] in
lemma bcol_add (e : ℕ → Fin (m + n) → F) (j : ℕ) : bcol W e (m + j) = e j := by
  simp [bcol]

end Seq

variable {W : Matrix (Fin (m + n)) (Fin m) F}

/-- **L2, bordered.** If `B` preserves `range W` then adding a term `φ(x) v` to `B` does not change
`u(·, v)`. -/
theorem bkdet_add_vecMulVec {B : Matrix (Fin (m + n)) (Fin (m + n)) F}
    (hB : ∀ x ∈ Wsp W, B *ᵥ x ∈ Wsp W) (c v : Fin (m + n) → F) :
    bkdet W (B + Matrix.vecMulVec v c) v = bkdet W B v := by
  set B' := B + Matrix.vecMulVec v c with hB'
  set b := bcol W (fun k => B ^ k *ᵥ v) with hb
  have hA : ∀ x : Fin (m + n) → F, B' *ᵥ x = B *ᵥ x + (c ⬝ᵥ x) • v := by
    intro x
    rw [hB', Matrix.add_mulVec]
    congr 1
    ext i
    simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hv : v ∈ Submodule.span F (b '' Set.Iio (m + 1)) :=
    Submodule.subset_span ⟨m, by simp, by simp [hb, bcol]⟩
  have hmono : ∀ k l, k ≤ l → Submodule.span F (b '' Set.Iio k) ≤ Submodule.span F (b '' Set.Iio l) :=
    fun k l h => Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))
  have hP : ∀ k : ℕ, B' ^ k *ᵥ v - B ^ k *ᵥ v ∈ Submodule.span F (b '' Set.Iio (m + k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : B' ^ (k + 1) *ᵥ v - B ^ (k + 1) *ᵥ v =
          B' *ᵥ (B' ^ k *ᵥ v - B ^ k *ᵥ v) + (c ⬝ᵥ (B ^ k *ᵥ v)) • v := by
        rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.mulVec_sub, hA (B ^ k *ᵥ v)]
        abel
      rw [hstep]
      refine Submodule.add_mem _ (mulVec_mem_span_image B' b _ (Set.Iio (m + (k + 1))) ?_ ih) ?_
      · intro j hj
        rw [hA]
        have hj' : j < m + k := hj
        refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (hmono _ _ (by omega) hv))
        by_cases hjm : j < m
        · exact mem_span_bcol_of_mem_Wsp W _ (hB _ (bcol_of_lt W _ hjm)) _ (by omega)
        · obtain ⟨j', rfl⟩ : ∃ j', j = m + j' := ⟨j - m, by omega⟩
          refine Submodule.subset_span ⟨m + (j' + 1), by simp at hj ⊢; omega, ?_⟩
          simp [hb, bcol_add, pow_succ', Matrix.mulVec_mulVec, bcol_add]
      · exact Submodule.smul_mem _ _ (hmono _ _ (by omega) hv)
  rw [bkdet_eq, bkdet_eq]
  have := det_cols_tri (bcol W fun k => B' ^ k *ᵥ v) b (fun _ => 1) (fun k => by
    by_cases hk : (k : ℕ) < m
    · have : bcol W (fun k => B' ^ k *ᵥ v) k = b k := by simp [hb, bcol, hk]
      simp [this]
    · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = m + j := ⟨k - m, by omega⟩
      have e1 : bcol W (fun k => B' ^ k *ᵥ v) k = B' ^ j *ᵥ v := by
        rw [hj, bcol_add]
      have e2 : b k = B ^ j *ᵥ v := by rw [hb, hj, bcol_add]
      rw [e1, e2, one_smul]
      have := hP j
      rwa [hj])
  simpa using this

/-- **L3, bordered chain.** If `T` preserves `range W` and `T v_j - r_j v_{j+1}` lies in
`range W + span(v_0..v_j)`, then `u(T, v₀) = (∏_k ∏_{j<k} r_j) · det [W | v₀, …, v_{n-1}]`. -/
theorem bkdet_chain {T : Matrix (Fin (m + n)) (Fin (m + n)) F}
    (hT : ∀ x ∈ Wsp W, T *ᵥ x ∈ Wsp W) (v : ℕ → Fin (m + n) → F) (r : ℕ → F)
    (hv : ∀ j, j + 1 < n →
      T *ᵥ v j - r j • v (j + 1) ∈ Submodule.span F (bcol W v '' Set.Iio (m + (j + 1)))) :
    bkdet W T (v 0) = (∏ k : Fin n, ∏ j ∈ Finset.range k, r j) * (colMat (bcol W v)).det := by
  set b := bcol W v with hb
  have hmono : ∀ k l, k ≤ l → Submodule.span F (b '' Set.Iio k) ≤ Submodule.span F (b '' Set.Iio l) :=
    fun k l h => Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))
  have hP : ∀ k : ℕ, k < n → T ^ k *ᵥ v 0 - (∏ j ∈ Finset.range k, r j) • v k ∈
      Submodule.span F (b '' Set.Iio (m + k)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hvk : ∀ j, v j ∈ Submodule.span F (b '' Set.Iio (m + j + 1)) := fun j =>
        Submodule.subset_span ⟨m + j, by simp, by simp [hb, bcol_add]⟩
      have hstep : T ^ (k + 1) *ᵥ v 0 - (∏ j ∈ Finset.range (k + 1), r j) • v (k + 1) =
          T *ᵥ (T ^ k *ᵥ v 0 - (∏ j ∈ Finset.range k, r j) • v k)
            + (∏ j ∈ Finset.range k, r j) • (T *ᵥ v k - r k • v (k + 1)) := by
        rw [pow_succ', ← Matrix.mulVec_mulVec, Finset.prod_range_succ, Matrix.mulVec_sub,
          Matrix.mulVec_smul, smul_sub, mul_smul]
        abel
      rw [hstep]
      refine Submodule.add_mem _ (mulVec_mem_span_image T b _ (Set.Iio (m + (k + 1))) ?_
        (ih (by omega))) ?_
      · intro j hj
        have hj' : j < m + k := hj
        by_cases hjm : j < m
        · exact mem_span_bcol_of_mem_Wsp W _ (hT _ (bcol_of_lt W _ hjm)) _ (by omega)
        · obtain ⟨j', rfl⟩ : ∃ j', j = m + j' := ⟨j - m, by omega⟩
          have hbj : b (m + j') = v j' := by simp [hb, bcol_add]
          rw [hbj]
          have h1 := hv j' (by omega)
          have e : T *ᵥ v j' = r j' • v (j' + 1) + (T *ᵥ v j' - r j' • v (j' + 1)) := by abel
          rw [e]
          refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨m + (j' + 1), by simp; omega, by simp [hb, bcol_add]⟩)) (hmono _ _ (by omega) h1)
      · exact Submodule.smul_mem _ _ (hmono _ _ (by omega) (hv k hk))
  rw [bkdet_eq]
  have := det_cols_tri (bcol W fun k => T ^ k *ᵥ v 0) b
    (fun k => if (k : ℕ) < m then 1 else ∏ j ∈ Finset.range ((k : ℕ) - m), r j) (fun k => by
    by_cases hk : (k : ℕ) < m
    · have : bcol W (fun k => T ^ k *ᵥ v 0) k = b k := by simp [hb, bcol, hk]
      simp [this, hk]
    · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = m + j := ⟨k - m, by omega⟩
      have e1 : bcol W (fun k => T ^ k *ᵥ v 0) k = T ^ j *ᵥ v 0 := by rw [hj, bcol_add]
      have e2 : b k = v j := by rw [hb, hj, bcol_add]
      rw [e1, e2, if_neg hk, hj]
      have := hP j (by have := k.2; omega)
      simpa using this)
  rw [this]
  congr 1
  rw [Fin.prod_univ_add]
  simp

end CatalanCore
