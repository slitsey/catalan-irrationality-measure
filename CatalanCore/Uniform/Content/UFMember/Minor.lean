module

public import CatalanCore.Uniform.Content.UFMember.Families

@[expose] public section

/-!
# UF member package, step 1b: two-level data pass to minors (abstract form)

Let `Bl` be square over `R` (index `ι`) with changes of basis `L, P` invertible modulo `π` such that
`L·Bl·P` is divisible by `π` on the rows and on the columns of `s`, and `L·Bl·P = π·N` on
`s × s` with `rank (N mod π) ≤ b`.  Then for ANY injective row and column maps
`e₁ e₂ : κ → ι` (delete `k = |ι| - |κ|` rows and `k` columns),

  `π^(a + (a - b)) ∣ det (Bl.submatrix e₁ e₂)`,   `a = |s| + |κ| - |ι|`  (`= |s| - k`).

Proof idea (this replaces the Smith-length transfer A1–A3 of `smith-deletion/THEOREM.md`).  The
rows of `L mod π` indexed by `s` span the left kernel `U` of `Bl mod π`; the vectors of `U`
supported on `range e₁` form a subspace of dimension `≥ |s| - k`.  A basis of it, lifted to
`R` as `R`-combinations of the rows of `L`, is a left kernel family of the minor; likewise on the
right.  Their divided pairing is `A·N·Bᵀ` modulo `π`, of rank `≤ b`: the corrections coming from
the deleted coordinates are divisible by `π²`.  `two_level_dvd_det_of_families` concludes.
No determinant of the full matrix and no Smith form is used.
-/

open Matrix Finset Module

namespace CatalanCore.Uniform.Content.UFMember

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- `R`-combinations of the rows `s` of `L`. -/
def rowComb {α ι : Type*} [Fintype ι] {s : Finset ι} (A : Matrix α s R) (L : Matrix ι ι R) :
    Matrix α ι R :=
  A * L.submatrix Subtype.val id
/-- A product through a masked index: restricting the middle index to `range e`. -/
lemma submatrix_mul_of_mask {α β ι κ : Type*} [Fintype ι] [Fintype κ]
    (A A' : Matrix α ι R) (M : Matrix ι β R) (e : κ → ι) (he : Function.Injective e)
    (h0 : ∀ i u, u ∉ Set.range e → A' i u = 0) (h1 : ∀ i v, A' i (e v) = A i (e v)) :
    A.submatrix id e * M.submatrix e id = A' * M := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Fintype.sum_of_injective e he _ _ (fun u hu => by rw [h0 i u hu, zero_mul])
    (fun v => by rw [h1 i v]; rfl)

/-- The same with the mask on the right factor. -/
lemma submatrix_mul_of_mask' {α β ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix α ι R) (Z Z' : Matrix ι β R) (e : κ → ι) (he : Function.Injective e)
    (h0 : ∀ u j, u ∉ Set.range e → Z' u j = 0) (h1 : ∀ v j, Z' (e v) j = Z (e v) j) :
    M.submatrix id e * Z.submatrix e id = M * Z' := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Fintype.sum_of_injective e he _ _ (fun u hu => by rw [h0 u j hu, mul_zero])
    (fun v => by rw [h1 v j]; rfl)

/-- **Left kernel family of a minor.**  From the rows `s` of `L`, a family of `|s| + |κ| - |ι|`
`R`-combinations of those rows whose reductions are supported on `range e`, independent there,
and in the left kernel of `Bl mod π`. -/
theorem exists_left_family {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : R →+* K) {π : R} (hker : ∀ x, φ x = 0 ↔ π ∣ x)
    (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z)
    (Bl L P : Matrix ι ι R) (hL : φ L.det ≠ 0) (hP : φ P.det ≠ 0) (s : Finset ι)
    (hrow : ∀ i ∈ s, ∀ j, π ∣ (L * Bl * P) i j) (e : κ → ι) (he : Function.Injective e) :
    ∃ A : Matrix (Fin (s.card + Fintype.card κ - Fintype.card ι)) s R,
      LinearIndependent K (fun i v => φ ((rowComb A L) i (e v))) ∧
      (∀ i u, u ∉ Set.range e → π ∣ (rowComb A L) i u) ∧
      (∀ i u, π ∣ (rowComb A L * Bl) i u) := by
  classical
  set a := s.card + Fintype.card κ - Fintype.card ι with ha_def
  set Lb := L.map φ
  set Ab := Bl.map φ
  set Pb := P.map φ
  have hPu : IsUnit Pb.det := by
    show IsUnit (φ.mapMatrix P).det
    rw [← RingHom.map_det]; exact isUnit_iff_ne_zero.2 hP
  have hLu : IsUnit Lb := by
    rw [Matrix.isUnit_iff_isUnit_det]
    show IsUnit (φ.mapMatrix L).det
    rw [← RingHom.map_det]; exact isUnit_iff_ne_zero.2 hL
  -- the rows `s` of `L mod π` are left kernel vectors of `Bl mod π`
  have hker1 : ∀ i ∈ s, ∀ t, (Lb * Ab) i t = 0 := by
    intro i hi t
    have h0 : ∀ u, (Lb * Ab * Pb) i u = 0 := fun u => by
      rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
      exact (hker _).2 (hrow i hi u)
    have hc : Lb * Ab = Lb * Ab * Pb * Pb⁻¹ := (Matrix.mul_nonsing_inv_cancel_right _ _ hPu).symm
    rw [hc, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun u _ => by rw [h0 u, zero_mul]
  let rows : s → ι → K := fun i => Lb i
  have hrowsLI : LinearIndependent K rows :=
    (linearIndependent_rows_iff_isUnit.2 hLu).comp _ Subtype.val_injective
  set U : Submodule K (ι → K) := Submodule.span K (Set.range rows)
  let sv : κ → ι → K := fun v => Pi.single (e v) (1 : K)
  have hsvLI : LinearIndependent K sv := by
    have := (Pi.basisFun K ι).linearIndependent.comp e he
    convert this using 1
    funext v
    simp [sv, Pi.basisFun_apply]
  set V : Submodule K (ι → K) := Submodule.span K (Set.range sv)
  have hUr : finrank K U = s.card := by
    simpa using finrank_span_eq_card hrowsLI
  have hVr : finrank K V = Fintype.card κ := finrank_span_eq_card hsvLI
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U V
  have hle : finrank K ↥(U ⊔ V) ≤ Fintype.card ι := by
    simpa using Submodule.finrank_le (U ⊔ V)
  have ha : a ≤ finrank K ↥(U ⊓ V) := by omega
  let bI := Module.finBasis K ↥(U ⊓ V)
  let g : Fin a → ι → K := fun i => (bI (Fin.castLE ha i) : ι → K)
  have hgU : ∀ i, g i ∈ U := fun i => (Submodule.mem_inf.1 (bI (Fin.castLE ha i)).2).1
  have hgV : ∀ i, g i ∈ V := fun i => (Submodule.mem_inf.1 (bI (Fin.castLE ha i)).2).2
  have hV0 : ∀ x ∈ V, ∀ u, u ∉ Set.range e → x u = 0 := by
    intro x hx u hu
    have hVk : V ≤ LinearMap.ker (LinearMap.proj u : (ι → K) →ₗ[K] K) := by
      rw [Submodule.span_le]
      rintro _ ⟨v, rfl⟩
      have hne : u ≠ e v := fun h => hu ⟨v, h.symm⟩
      simp [sv, Pi.single_apply, hne]
    simpa using hVk hx
  have hUk : ∀ x ∈ U, ∀ u, ∑ t, x t * Ab t u = 0 := by
    intro x hx u
    have hUk' : U ≤ LinearMap.ker
        ((LinearMap.proj u : (ι → K) →ₗ[K] K).comp (Matrix.vecMulLinear Ab)) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      have := hker1 t.1 t.2 u
      rw [Matrix.mul_apply] at this
      simpa [rows, Matrix.vecMul, dotProduct] using this
    simpa [Matrix.vecMul, dotProduct] using hUk' hx
  choose α hα using fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hgU i)
  choose c A hc hA using fun i => exists_vec_lift φ hlift (α i)
  have hXf : ∀ i u, φ ((rowComb (Matrix.of A) L) i u) = φ (c i) * g i u := by
    intro i u
    rw [rowComb, Matrix.mul_apply, map_sum, ← hα i, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, map_mul, hA, Pi.smul_apply,
      smul_eq_mul, rows, Lb, Matrix.map_apply]
    ring
  refine ⟨Matrix.of A, ?_, ?_, ?_⟩
  · -- independence of the restricted reductions
    let incl : ↥(U ⊓ V) →ₗ[K] V := Submodule.inclusion inf_le_right
    let restr : V →ₗ[K] (κ → K) := (LinearMap.funLeft K K e).comp V.subtype
    have hrestr : LinearMap.ker restr = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply Subtype.ext
      funext u
      by_cases hu : u ∈ Set.range e
      · obtain ⟨v, rfl⟩ := hu
        exact congrFun hxy v
      · rw [hV0 _ x.2 u hu, hV0 _ y.2 u hu]
    have h1 : LinearIndependent K (fun i => bI (Fin.castLE ha i)) :=
      bI.linearIndependent.comp _ (Fin.castLE_injective ha)
    have h2 := (h1.map' incl (LinearMap.ker_eq_bot.2 (Submodule.inclusion_injective _))).map'
      restr hrestr
    have h3 := h2.units_smul (fun i => Units.mk0 (φ (c i)) (hc i))
    convert h3 using 1
    funext i v
    rw [hXf]
    rfl
  · intro i u hu
    rw [← hker, hXf, hV0 _ (hgV i) u hu, mul_zero]
  · intro i u
    rw [← hker, Matrix.mul_apply, map_sum]
    calc ∑ t, φ ((rowComb (Matrix.of A) L) i t * Bl t u)
        = φ (c i) * ∑ t, g i t * Ab t u := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [map_mul, hXf]; simp only [Ab, Matrix.map_apply]; ring
      _ = 0 := by rw [hUk _ (hgU i) u, mul_zero]

/-- **Two-level data pass to minors.** -/
theorem two_level_dvd_det_submatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (φ : R →+* K) {π : R} (hπ : Prime π) (hker : ∀ x, φ x = 0 ↔ π ∣ x)
    (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z)
    (Bl L P : Matrix ι ι R) (hL : φ L.det ≠ 0) (hP : φ P.det ≠ 0) (s : Finset ι)
    (hrow : ∀ i ∈ s, ∀ j, π ∣ (L * Bl * P) i j) (hcol : ∀ i, ∀ j ∈ s, π ∣ (L * Bl * P) i j)
    (N : Matrix s s R) (hN : ∀ i j : s, (L * Bl * P) i j = π * N i j) (b : ℕ)
    (hb : (N.map φ).rank ≤ b) (e₁ e₂ : κ → ι) (he₁ : Function.Injective e₁)
    (he₂ : Function.Injective e₂) :
    π ^ ((s.card + Fintype.card κ - Fintype.card ι) +
      ((s.card + Fintype.card κ - Fintype.card ι) - b)) ∣ (Bl.submatrix e₁ e₂).det := by
  classical
  set a := s.card + Fintype.card κ - Fintype.card ι
  have hπ0 : φ π = 0 := (hker π).2 dvd_rfl
  obtain ⟨A, hA1, hA2, hA3⟩ :=
    exists_left_family φ hker hlift Bl L P hL hP s hrow e₁ he₁
  have hT : Pᵀ * Blᵀ * Lᵀ = (L * Bl * P)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨B, hB1, hB2, hB3⟩ := exists_left_family φ hker hlift Blᵀ Pᵀ Lᵀ
    (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) s
    (fun i hi j => by rw [hT]; exact hcol j i hi) e₂ he₂
  set Xf : Matrix (Fin a) ι R := rowComb A L with hXf
  set Zf : Matrix ι (Fin a) R := (rowComb B Pᵀ)ᵀ with hZf
  -- divided pieces
  choose X1 hX1 using fun i u => (em (u ∈ Set.range e₁)).elim
    (fun h => (⟨0, Or.inl h⟩ : ∃ q : R, u ∈ Set.range e₁ ∨ Xf i u = π * q))
    (fun h => let ⟨q, hq⟩ := hA2 i u h; ⟨q, Or.inr hq⟩)
  set X1' : Matrix (Fin a) ι R := Matrix.of fun i u => if u ∈ Set.range e₁ then 0 else X1 i u
  set Xm := Xf - π • X1'
  have hXm0 : ∀ i u, u ∉ Set.range e₁ → Xm i u = 0 := by
    intro i u hu
    rcases hX1 i u with h | h
    · exact absurd h hu
    · have hu' : ¬ ∃ y, e₁ y = u := hu
      simp [Xm, X1', hu', h]
  have hXm1 : ∀ i v, Xm i (e₁ v) = Xf i (e₁ v) := by
    intro i v; simp [Xm, X1']
  have hB2' : ∀ u j, u ∉ Set.range e₂ → π ∣ Zf u j := by
    intro u j hu; exact hB2 j u hu
  choose Z1 hZ1 using fun u j => (em (u ∈ Set.range e₂)).elim
    (fun h => (⟨0, Or.inl h⟩ : ∃ q : R, u ∈ Set.range e₂ ∨ Zf u j = π * q))
    (fun h => let ⟨q, hq⟩ := hB2' u j h; ⟨q, Or.inr hq⟩)
  set Z1' : Matrix ι (Fin a) R := Matrix.of fun u j => if u ∈ Set.range e₂ then 0 else Z1 u j
  set Zm := Zf - π • Z1'
  have hZm0 : ∀ u j, u ∉ Set.range e₂ → Zm u j = 0 := by
    intro u j hu
    rcases hZ1 u j with h | h
    · exact absurd h hu
    · have hu' : ¬ ∃ y, e₂ y = u := hu
      simp [Zm, Z1', hu', h]
  have hZm1 : ∀ v j, Zm (e₂ v) j = Zf (e₂ v) j := by
    intro v j; simp [Zm, Z1']
  choose QA hQA using hA3
  choose QB hQB using fun u j => (show π ∣ (Bl * Zf) u j by
    have h := hB3 j u
    have e : (Bl * Zf) u j = (rowComb B Pᵀ * Blᵀ) j u := by
      rw [← Matrix.transpose_apply (Bl * Zf), Matrix.transpose_mul, hZf,
        Matrix.transpose_transpose]
    rw [e]; exact h)
  have hQA' : Xf * Bl = π • Matrix.of QA := by ext i u; simp [hQA i u]
  have hQB' : Bl * Zf = π • Matrix.of QB := by ext u j; simp [hQB u j]
  have hLBP : L.submatrix (Subtype.val : s → ι) id * Bl * P.submatrix id (Subtype.val : s → ι) =
      π • N := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hN i j
  have hXBZ : Xf * Bl * Zf = π • (A * N * Bᵀ) := by
    calc Xf * Bl * Zf = A * (L.submatrix (Subtype.val : s → ι) id * Bl *
          P.submatrix id (Subtype.val : s → ι)) * Bᵀ := by
          rw [hXf, hZf]
          unfold rowComb
          rw [Matrix.transpose_mul, Matrix.transpose_submatrix, Matrix.transpose_transpose]
          simp only [Matrix.mul_assoc]
      _ = π • (A * N * Bᵀ) := by
          rw [hLBP, Matrix.mul_smul, Matrix.smul_mul]
  -- the minor and its families
  set X : Matrix (Fin a) κ R := Xf.submatrix id e₁
  set Z : Matrix κ (Fin a) R := Zf.submatrix e₂ id
  have hXY : X * Bl.submatrix e₁ e₂ = (Xm * Bl).submatrix id e₂ :=
    submatrix_mul_of_mask Xf Xm (Bl.submatrix id e₂) e₁ he₁ hXm0 hXm1
  have hYZ : Bl.submatrix e₁ e₂ * Z = (Bl * Zm).submatrix e₁ id :=
    submatrix_mul_of_mask' (Bl.submatrix e₁ id) Zf Zm e₂ he₂ hZm0 hZm1
  have hXYZ : X * Bl.submatrix e₁ e₂ * Z = Xm * Bl * Zm := by
    rw [hXY]
    exact submatrix_mul_of_mask' (Xm * Bl) Zf Zm e₂ he₂ hZm0 hZm1
  set E := X1' * Bl * Z1' - X1' * Matrix.of QB - Matrix.of QA * Z1'
  have hH : X * Bl.submatrix e₁ e₂ * Z = π • (A * N * Bᵀ + π • E) := by
    rw [hXYZ]
    have e1 : Xm * Bl * Zm = Xf * Bl * Zf - Xf * Bl * (π • Z1') - π • (X1' * (Bl * Zf))
        + π • X1' * Bl * (π • Z1') := by
      simp only [Xm, Zm, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc]
      module
    rw [e1, hXBZ, hQA', hQB']
    simp only [Matrix.smul_mul, Matrix.mul_smul, E, smul_sub, smul_add, smul_smul]
    module
  have hrank : ((A * N * Bᵀ + π • E).map φ).rank ≤ b := by
    have hm : (A * N * Bᵀ + π • E).map φ =
        A.map φ * N.map φ * (Bᵀ).map φ := by
      rw [Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]
      have : (π • E).map φ = 0 := by ext i j; simp [hπ0]
      rw [this, add_zero]
    rw [hm]
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hb
  refine two_level_dvd_det_of_families φ hπ hker hlift (Bl.submatrix e₁ e₂) X Z hA1 ?_ ?_ ?_
    _ hH b hrank
  · convert hB1 using 1
    funext j t
    rfl
  · intro i t
    rw [hXY, Matrix.submatrix_apply]
    have : Xm * Bl = Xf * Bl - π • (X1' * Bl) := by
      simp only [Xm, Matrix.sub_mul, Matrix.smul_mul]
    rw [this, hQA', Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
      smul_eq_mul, ← mul_sub]
    exact dvd_mul_right _ _
  · intro t j
    rw [hYZ, Matrix.submatrix_apply]
    have : Bl * Zm = Bl * Zf - π • (Bl * Z1') := by
      simp only [Zm, Matrix.mul_sub, Matrix.mul_smul]
    rw [this, hQB', Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
      smul_eq_mul, ← mul_sub]
    exact dvd_mul_right _ _

end CatalanCore.Uniform.Content.UFMember
