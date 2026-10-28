module

public import CatalanCore.Uniform.Content.UFMember.Schur

@[expose] public section

/-!
# UF member package: the Smith witness from kernel FAMILIES of the Schur complement

`exists_twoLevel_of_families`: two-level data `(L₂, P₂, s, N₂)` of a square `W` exist as soon
as there are `a` left and `a` right kernel vectors of `W mod π` (independent reductions) whose
divided pairing `X W Z / π` has rank `≤ b` modulo `π`; the changes of basis are completions
(`exists_completion`).  `ThreeLevelWit.ofSchurFamilies` composes this with `ofSchur`.

So the frame obligations for the Smith layer of one full hybrid matrix at one prime are:

1. an integral lift `Bl` of `p² Ψ`;
2. `det Q` primitive (`Q` the core block; monic in the scaled gauge);
3. `det Q · T' - S' adj Q R' = p · W` (distinct border residues);
4. `σ` left and `σ` right kernel vectors of `W mod p` (the `J`-supported kernels) and the
   identity `X W Z = p · H` with `H mod p` a weighted Cauchy matrix on the retained poles
   ((S6)–(S8)); its rank is bounded by `Smith.rank_le_card_of_sum`.
-/

open Polynomial Matrix Finset Module CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.UFMember

section Abstract

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- **Two-level data from kernel families.** -/
theorem exists_twoLevel_of_families {B : Type*} [Fintype B] [DecidableEq B]
    (φ : R →+* K) {π : R} (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z) {a : ℕ}
    (W : Matrix B B R) (X : Matrix (Fin a) B R) (Z : Matrix B (Fin a) R)
    (hX : LinearIndependent K (fun i t => φ (X i t)))
    (hZ : LinearIndependent K (fun j t => φ (Z t j)))
    (hXW : ∀ i t, π ∣ (X * W) i t) (hWZ : ∀ t j, π ∣ (W * Z) t j)
    (H : Matrix (Fin a) (Fin a) R) (hH : X * W * Z = π • H) (b : ℕ)
    (hrank : (H.map φ).rank ≤ b) :
    ∃ (L₂ P₂ : Matrix B B R) (s : Finset B) (N₂ : Matrix s s R),
      φ L₂.det ≠ 0 ∧ φ P₂.det ≠ 0 ∧ (∀ i ∈ s, ∀ j, π ∣ (L₂ * W * P₂) i j) ∧
      (∀ i, ∀ j ∈ s, π ∣ (L₂ * W * P₂) i j) ∧
      (∀ i j : s, (L₂ * W * P₂) i j = π * N₂ i j) ∧ (N₂.map φ).rank ≤ b ∧ s.card = a := by
  classical
  have ha : a ≤ Fintype.card B := by simpa using hX.fintype_card_le_finrank
  let e : Fin a ⊕ Fin (Fintype.card B - a) ≃ B :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  obtain ⟨Wr, hWr⟩ := exists_completion φ hlift X hX e
  obtain ⟨Wc, hWc⟩ := exists_completion φ hlift Zᵀ hZ e
  set L0 := Matrix.fromRows X Wr
  set P0 := Matrix.fromCols Z Wcᵀ
  let L₂ : Matrix B B R := L0.submatrix e.symm id
  let P₂ : Matrix B B R := P0.submatrix id e.symm
  have hP0 : P0 = (Matrix.fromRows Zᵀ Wc)ᵀ := by
    rw [Matrix.transpose_fromRows, Matrix.transpose_transpose]
  have hprod : ∀ β γ, (L₂ * W * P₂) β γ = (L0 * W * P0) (e.symm β) (e.symm γ) := by
    intro β γ; simp [L₂, P₂, Matrix.mul_apply]
  have hblk : L0 * W * P0 = Matrix.fromBlocks (X * W * Z) (X * W * Wcᵀ) (Wr * W * Z)
      (Wr * W * Wcᵀ) := by
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  let s : Finset B := univ.map (Function.Embedding.inl.trans e.toEmbedding)
  have hmem : ∀ β ∈ s, ∃ i, e.symm β = Sum.inl i := by
    intro β hβ
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hβ
    exact ⟨i, e.symm_apply_apply _⟩
  let idx : s → Fin a := fun β => (hmem β.1 β.2).choose
  have hidx : ∀ β : s, e.symm β.1 = Sum.inl (idx β) := fun β => (hmem β.1 β.2).choose_spec
  refine ⟨L₂, P₂, s, H.submatrix idx idx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : L₂ = ((L0.submatrix id e).submatrix e.symm e.symm) := by
      ext β γ; simp [L₂]
    rw [h1, Matrix.det_submatrix_equiv_self, RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hWr).ne_zero
  · have h1 : P₂ = (((Matrix.fromRows Zᵀ Wc).submatrix id e)ᵀ).submatrix e.symm e.symm := by
      ext β γ; simp [P₂, hP0]
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_transpose, RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hWc).ne_zero
  · intro β hβ γ
    obtain ⟨i, hi⟩ := hmem β hβ
    rw [hprod, hi, hblk]
    rcases e.symm γ with j | j
    · simp only [Matrix.fromBlocks_apply₁₁]
      rw [Matrix.mul_apply]
      exact Finset.dvd_sum fun t _ => Dvd.dvd.mul_right (hXW i t) _
    · simp only [Matrix.fromBlocks_apply₁₂]
      rw [Matrix.mul_apply]
      exact Finset.dvd_sum fun t _ => Dvd.dvd.mul_right (hXW i t) _
  · intro β γ hγ
    obtain ⟨j, hj⟩ := hmem γ hγ
    rw [hprod, hj, hblk]
    rcases e.symm β with i | i
    · simp only [Matrix.fromBlocks_apply₁₁]
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      exact Finset.dvd_sum fun t _ => Dvd.dvd.mul_left (hWZ t j) _
    · simp only [Matrix.fromBlocks_apply₂₁]
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      exact Finset.dvd_sum fun t _ => Dvd.dvd.mul_left (hWZ t j) _
  · intro β γ
    rw [hprod, hidx β, hidx γ, hblk, Matrix.fromBlocks_apply₁₁, hH]
    simp
  · have e1 : (H.submatrix idx idx).map φ = (H.map φ).submatrix idx idx := rfl
    rw [e1]
    exact (Matrix.rank_submatrix_le _ _ _).trans hrank
  · simp [s]

/-- Two-level data of a square matrix `W` (changes of basis, kernel set, divided block). -/
structure TwoLevelData (φ : R →+* K) (π : R) {B : Type*} [Fintype B] [DecidableEq B]
    (W : Matrix B B R) (a b : ℕ) where
  L₂ : Matrix B B R
  P₂ : Matrix B B R
  s : Finset B
  N₂ : Matrix s s R
  hL₂ : φ L₂.det ≠ 0
  hP₂ : φ P₂.det ≠ 0
  hrow : ∀ i ∈ s, ∀ j, π ∣ (L₂ * W * P₂) i j
  hcol : ∀ i, ∀ j ∈ s, π ∣ (L₂ * W * P₂) i j
  hN₂ : ∀ i j : s, (L₂ * W * P₂) i j = π * N₂ i j
  hb : (N₂.map φ).rank ≤ b
  hcard : s.card = a

/-- Two-level data from kernel families (choice of the data of `exists_twoLevel_of_families`). -/
noncomputable def TwoLevelData.ofFamilies {B : Type*} [Fintype B] [DecidableEq B]
    (φ : R →+* K) {π : R} (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z) {a : ℕ}
    (W : Matrix B B R) (X : Matrix (Fin a) B R) (Z : Matrix B (Fin a) R)
    (hX : LinearIndependent K (fun i t => φ (X i t)))
    (hZ : LinearIndependent K (fun j t => φ (Z t j)))
    (hXW : ∀ i t, π ∣ (X * W) i t) (hWZ : ∀ t j, π ∣ (W * Z) t j)
    (H : Matrix (Fin a) (Fin a) R) (hH : X * W * Z = π • H) (b : ℕ)
    (hrank : (H.map φ).rank ≤ b) : TwoLevelData φ π W a b :=
  have h := exists_twoLevel_of_families φ hlift W X Z hX hZ hXW hWZ H hH b hrank
  { L₂ := h.choose
    P₂ := h.choose_spec.choose
    s := h.choose_spec.choose_spec.choose
    N₂ := h.choose_spec.choose_spec.choose_spec.choose
    hL₂ := h.choose_spec.choose_spec.choose_spec.choose_spec.1
    hP₂ := h.choose_spec.choose_spec.choose_spec.choose_spec.2.1
    hrow := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
    hcol := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
    hN₂ := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.1
    hb := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.1
    hcard := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2 }

end Abstract

variable {p : ℕ} [Fact p.Prime] {C B : Type*} [Fintype C] [DecidableEq C] [Fintype B]
  [DecidableEq B]

/-- **Smith witness from the Schur complement and two-level data of `W`.** -/
noncomputable def ThreeLevelWit.ofSchurData (M : Matrix (C ⊕ B) (C ⊕ B) ℚ[X])
    (Bl : Matrix (C ⊕ B) (C ⊕ B) (LocRing p)[X])
    (hB : ∀ i j, toQ p (Bl i j) = Polynomial.C ((p : ℚ) ^ 2) * M i j)
    (hQ : phiP p Bl.toBlocks₁₁.det ≠ 0) (W : Matrix B B (LocRing p)[X])
    (hW : Bl.toBlocks₁₁.det • Bl.toBlocks₂₂ - Bl.toBlocks₂₁ * Bl.toBlocks₁₁.adjugate *
      Bl.toBlocks₁₂ = Polynomial.C ((p : ℕ) : LocRing p) • W) {a b : ℕ}
    (D : TwoLevelData (phiP p) (Polynomial.C ((p : ℕ) : LocRing p)) W a b) :
    ThreeLevelWit p M b :=
  ThreeLevelWit.ofSchur M Bl hB hQ W hW D.L₂ D.P₂ D.hL₂ D.hP₂ D.s D.hrow D.hcol D.N₂ D.hN₂ b D.hb

/-- Its price is `2h - (|B| + a + (a - b))`, i.e. `2|C| + m - (σ + (σ - b))`. -/
theorem ThreeLevelWit.ofSchurData_price (M : Matrix (C ⊕ B) (C ⊕ B) ℚ[X])
    (Bl : Matrix (C ⊕ B) (C ⊕ B) (LocRing p)[X])
    (hB : ∀ i j, toQ p (Bl i j) = Polynomial.C ((p : ℚ) ^ 2) * M i j)
    (hQ : phiP p Bl.toBlocks₁₁.det ≠ 0) (W : Matrix B B (LocRing p)[X])
    (hW : Bl.toBlocks₁₁.det • Bl.toBlocks₂₂ - Bl.toBlocks₂₁ * Bl.toBlocks₁₁.adjugate *
      Bl.toBlocks₁₂ = Polynomial.C ((p : ℕ) : LocRing p) • W) {a b : ℕ}
    (D : TwoLevelData (phiP p) (Polynomial.C ((p : ℕ) : LocRing p)) W a b) :
    (ThreeLevelWit.ofSchurData M Bl hB hQ W hW D).price =
      2 * Fintype.card (C ⊕ B) - (Fintype.card B + (a + (a - b))) := by
  have ht : (borderSet C B).card = Fintype.card B := by simp [borderSet]
  have hs : (borderSub C D.s).card = a := by simp [borderSub, D.hcard]
  show 2 * Fintype.card (C ⊕ B) - ((borderSet C B).card + ((borderSub C D.s).card +
    ((borderSub C D.s).card - b))) = _
  rw [ht, hs]

end CatalanCore.Uniform.Content.UFMember
