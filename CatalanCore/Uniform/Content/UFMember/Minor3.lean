module

public import CatalanCore.Uniform.Content.UFMember.Minor
public import CatalanCore.Uniform.Content.UFMember.BinetDvd

@[expose] public section

/-!
# UF member package: three-level data pass to minors (abstract form)

The Smith layer of `smith-deletion/THEOREM.md` is a THREE-level statement in the scaled gauge:
after the unit core shear, `L A P = diag(Q_c, π W)` and `W` carries two-level data (kernels of
size `σ` supported on `J`, divided pairing of rank `≤ s`), so `v(det A) ≥ m + σ + (σ - s)`.
Abstractly, for `M = L·Bl·P` (`L, P` invertible modulo `π`) we assume, with `s ⊆ t`:

* (H1) the rows `t` of `M` are divisible by `π`;
* (H2) the rows `s` of `M` are divisible by `π²`;
* (H3) the columns `s` of `M` are divisible by `π`;
* (H4) on rows `t`, the columns `s` are divisible by `π²`;
* (H5) `M = π² N₂` on `s × s`, with `rank (N₂ mod π) ≤ b`.

`three_level_dvd_det_submatrix`: for ANY injective `e₁ e₂ : κ → ι` (delete `k` rows and `k`
columns),

  `π^((|t| - k) + (a + (a - b))) ∣ det Bl[e₁, e₂]`,   `a = |s| - k`.

Proof: every `|κ|`-minor of `M` factors as `π^{#rows in t}` times a minor of `M` with the rows `t`
divided by `π`; the latter matrix has two-level data with IDENTITY changes of basis, so
`two_level_dvd_det_submatrix` bounds its minors.  Cauchy–Binet in divisibility form
(`det_submatrix_mul_pow_dvd`) carries the minor bound from `M` back to `Bl` through the
adjugates of `L`, `P`.  For `k = 0` this is `v(det Bl) ≥ |t| + |s| + (|s| - b)`; a deletion costs
at most `k` in the denominator exponent (`3k` in valuation against `2k` in size), which is the
debit of Theorem SD.
-/

open Matrix Finset Module

namespace CatalanCore.Uniform.Content.UFMember

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- The number of rows of an injective row map landing in `t`. -/
lemma card_filter_mem_ge {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) (t : Finset ι) :
    t.card + Fintype.card κ - Fintype.card ι ≤ (univ.filter fun v => f v ∈ t).card := by
  classical
  have himg : (univ.filter fun v => f v ∈ t).image f = univ.image f ∩ t := by
    ext x
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_inter]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨⟨v, rfl⟩, hv⟩
    · rintro ⟨⟨v, rfl⟩, hv⟩; exact ⟨v, hv, rfl⟩
  have h1 := Finset.card_union_add_card_inter (univ.image f) t
  have h2 : (univ.image f ∪ t).card ≤ Fintype.card ι := Finset.card_le_univ _
  have h3 : (univ.image f).card = Fintype.card κ := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
  have h4 : ((univ.filter fun v => f v ∈ t).image f).card =
      (univ.filter fun v => f v ∈ t).card := Finset.card_image_of_injective _ hf
  rw [himg] at h4
  omega

/-- **Minors of three-level data.** -/
theorem three_level_minor_dvd {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (φ : R →+* K) {π : R} (hπ : Prime π) (hker : ∀ x, φ x = 0 ↔ π ∣ x)
    (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z)
    (M : Matrix ι ι R) (t s : Finset ι) (hst : s ⊆ t)
    (H1 : ∀ i ∈ t, ∀ j, π ∣ M i j) (H2 : ∀ i ∈ s, ∀ j, π ^ 2 ∣ M i j)
    (H3 : ∀ i, ∀ j ∈ s, π ∣ M i j) (H4 : ∀ i ∈ t, ∀ j ∈ s, π ^ 2 ∣ M i j)
    (N₂ : Matrix s s R) (H5 : ∀ i j : s, M i j = π ^ 2 * N₂ i j) (b : ℕ)
    (hb : (N₂.map φ).rank ≤ b) (f g : κ → ι) (hf : Function.Injective f)
    (hg : Function.Injective g) :
    π ^ ((t.card + Fintype.card κ - Fintype.card ι) +
      ((s.card + Fintype.card κ - Fintype.card ι) +
        ((s.card + Fintype.card κ - Fintype.card ι) - b))) ∣ (M.submatrix f g).det := by
  classical
  have hπ0 : π ≠ 0 := hπ.ne_zero
  choose q hq using H1
  let N : Matrix ι ι R := Matrix.of fun i j => if h : i ∈ t then q i h j else M i j
  let dv : ι → R := fun i => if i ∈ t then π else 1
  have hMN : M.submatrix f g = Matrix.diagonal (fun v => dv (f v)) * N.submatrix f g := by
    ext v w
    rw [Matrix.diagonal_mul]
    by_cases h : f v ∈ t
    · simp [N, dv, h, hq (f v) h (g w)]
    · simp [N, dv, h]
  have hprod : ∏ v, dv (f v) = π ^ (univ.filter fun v => f v ∈ t).card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hsq : ∀ x y : R, π ^ 2 ∣ π * x → x = y → π ∣ y := by
    intro x y h hxy
    rw [← hxy]
    rw [pow_two] at h
    exact (mul_dvd_mul_iff_left hπ0).1 h
  have hrow : ∀ i ∈ s, ∀ j, π ∣ ((1 : Matrix ι ι R) * N * (1 : Matrix ι ι R)) i j := by
    intro i hi j
    rw [Matrix.one_mul, Matrix.mul_one]
    have hit := hst hi
    have h2 := H2 i hi j
    rw [hq i hit j] at h2
    exact hsq _ _ h2 (by simp [N, hit])
  have hcol : ∀ i, ∀ j ∈ s, π ∣ ((1 : Matrix ι ι R) * N * (1 : Matrix ι ι R)) i j := by
    intro i j hj
    rw [Matrix.one_mul, Matrix.mul_one]
    by_cases hit : i ∈ t
    · have h4 := H4 i hit j hj
      rw [hq i hit j] at h4
      exact hsq _ _ h4 (by simp [N, hit])
    · simpa [N, hit] using H3 i j hj
  have hN : ∀ i j : s, ((1 : Matrix ι ι R) * N * (1 : Matrix ι ι R)) i j = π * N₂ i j := by
    intro i j
    rw [Matrix.one_mul, Matrix.mul_one]
    have hit := hst i.2
    have h5 := H5 i j
    rw [hq i hit j, pow_two, mul_assoc] at h5
    have := mul_left_cancel₀ hπ0 h5
    simp [N, hit, this]
  have h2 := two_level_dvd_det_submatrix φ hπ hker hlift N 1 1 (by simp) (by simp) s hrow hcol
    N₂ hN b hb f g hf hg
  rw [hMN, Matrix.det_mul, Matrix.det_diagonal, hprod, pow_add]
  exact mul_dvd_mul (pow_dvd_pow π (card_filter_mem_ge f hf t)) h2

/-- **Three-level data pass to minors.** -/
theorem three_level_dvd_det_submatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (φ : R →+* K) {π : R} (hπ : Prime π) (hker : ∀ x, φ x = 0 ↔ π ∣ x)
    (hlift : ∀ z : K, ∃ r d : R, φ d ≠ 0 ∧ φ r = φ d * z)
    (Bl L P : Matrix ι ι R) (hL : φ L.det ≠ 0) (hP : φ P.det ≠ 0) (t s : Finset ι)
    (hst : s ⊆ t)
    (H1 : ∀ i ∈ t, ∀ j, π ∣ (L * Bl * P) i j) (H2 : ∀ i ∈ s, ∀ j, π ^ 2 ∣ (L * Bl * P) i j)
    (H3 : ∀ i, ∀ j ∈ s, π ∣ (L * Bl * P) i j)
    (H4 : ∀ i ∈ t, ∀ j ∈ s, π ^ 2 ∣ (L * Bl * P) i j)
    (N₂ : Matrix s s R) (H5 : ∀ i j : s, (L * Bl * P) i j = π ^ 2 * N₂ i j) (b : ℕ)
    (hb : (N₂.map φ).rank ≤ b) (e₁ e₂ : κ → ι) :
    π ^ ((t.card + Fintype.card κ - Fintype.card ι) +
      ((s.card + Fintype.card κ - Fintype.card ι) +
        ((s.card + Fintype.card κ - Fintype.card ι) - b))) ∣ (Bl.submatrix e₁ e₂).det := by
  have h := det_submatrix_mul_pow_dvd Bl L P e₁ e₂ _ fun f g hf hg =>
    three_level_minor_dvd φ hπ hker hlift (L * Bl * P) t s hst H1 H2 H3 H4 N₂ H5 b hb f g hf hg
  have hnd : ¬ π ∣ (L.det * P.det) ^ Fintype.card κ := by
    intro h'
    rcases hπ.dvd_or_dvd (hπ.dvd_of_dvd_pow h') with h'' | h''
    · exact hL ((hker _).2 h'')
    · exact hP ((hker _).2 h'')
  exact hπ.pow_dvd_of_dvd_mul_left _ hnd h

end CatalanCore.Uniform.Content.UFMember
