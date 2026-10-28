module

public import CatalanCore.Uniform.Content.UFMoments.Own
public import CatalanCore.Uniform.Content.UFMoments.Phi2

@[expose] public section

/-!
# UF moments, step (b): transport of the own-fiber moment between nodes of one joint type

For a colour-block-diagonal core `D` (over any commutative ring), the own-fiber moment of a node
with own border part `s` (supported on its colour `τ`) is

  `G₀(s, ℓ_t) = (ℓ_t - d) - (s D⁻¹)·(ℓ - d)`.

`inv_restrict`: the colour block of `D⁻¹` is the inverse of the colour block of `D`.
`own_fiber_form`: `G₀` and `Σ g` are computed inside the own colour block.
`transport`: if a second node (colour `τ'`) has a chain equivalence `e` to the first under which
the blocks and border parts agree modulo `π²` and the prefixes are shifted by `κ` (with
`ℓ_t' = ℓ_t + κ`), then `G₀' ≡ G₀ + κ(1 - Σ g)` and `Σ g' ≡ Σ g` modulo `π²`.
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The colour block of a matrix. -/
abbrev blk {α : Type*} (D : Matrix ι ι α) (col : ι → ZMod p) (τ : ZMod p) :
    Matrix {a // col a = τ} {a // col a = τ} α :=
  D.submatrix Subtype.val Subtype.val

/-- The colour block of an inverse. -/
theorem inv_restrict (D : Matrix ι ι R) (col : ι → ZMod p) (hD : IsUnit D.det)
    (hb : ∀ a b, col a ≠ col b → D a b = 0) (τ : ZMod p) :
    IsUnit (blk D col τ).det ∧
      (blk D col τ)⁻¹ =
        blk D⁻¹ col τ := by
  have hinv := inv_colour_zero D col hD hb
  have hmul : blk D col τ *
      blk D⁻¹ col τ = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have h1 := congrFun (congrFun (mul_nonsing_inv D hD) i.1) j.1
    rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun a => col a = τ)] at h1
    have h0 : ∑ k : {a // ¬ col a = τ}, D i.1 k.1 * D⁻¹ k.1 j.1 = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rw [hb i.1 k.1 (by rw [i.2]; exact Ne.symm k.2), zero_mul]
    rw [h0, add_zero] at h1
    simp only [blk, Matrix.submatrix_apply]
    rw [h1, Matrix.one_apply, Matrix.one_apply]
    simp only [Subtype.ext_iff]
  refine ⟨?_, Matrix.inv_eq_right_inv hmul⟩
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this

/-- Own-fiber form of `s D⁻¹ · v` for `s` supported on the colour `τ`. -/
theorem own_fiber_form (D : Matrix ι ι R) (col : ι → ZMod p) (hD : IsUnit D.det)
    (hb : ∀ a b, col a ≠ col b → D a b = 0) (τ : ZMod p) (s v : ι → R)
    (hs : ∀ a, col a ≠ τ → s a = 0) :
    (s ᵥ* D⁻¹) ⬝ᵥ v = ∑ i : {a // col a = τ},
      ((fun i : {a // col a = τ} => s i.1) ᵥ*
        (blk D col τ)⁻¹) i * v i.1 := by
  have hinv := inv_colour_zero D col hD hb
  rw [(inv_restrict D col hD hb τ).2, dotProduct,
    ← Fintype.sum_subtype_add_sum_subtype (fun a => col a = τ)]
  have h0 : ∑ k : {a // ¬ col a = τ}, (s ᵥ* D⁻¹) k.1 * v k.1 = 0 :=
    Finset.sum_eq_zero fun k _ => by
      have : (s ᵥ* D⁻¹) k.1 = 0 := by
        simp only [vecMul, dotProduct]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : col j = τ
        · rw [hinv j k.1 (by rw [hj]; exact Ne.symm k.2), mul_zero]
        · rw [hs j hj, zero_mul]
      rw [this, zero_mul]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [vecMul, dotProduct, blk, Matrix.submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => col a = τ)]
  have h1 : ∑ k : {a // ¬ col a = τ}, s k.1 * D⁻¹ k.1 i.1 = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hs k.1 k.2, zero_mul]
  rw [h1, add_zero]

/-- Reindexing a fiber computation along a chain equivalence. -/
theorem reindex_form {o o' : Type*} [Fintype o] [DecidableEq o] [Fintype o'] [DecidableEq o']
    (e : o ≃ o') (M : Matrix o o R) (s v : o → R) :
    ∑ i, (s ᵥ* M⁻¹) i * v i =
      ∑ j, ((s ∘ e.symm) ᵥ* (M.submatrix e.symm e.symm)⁻¹) j * v (e.symm j) := by
  rw [Matrix.inv_submatrix_equiv, ← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [vecMul, dotProduct, Matrix.submatrix_apply, Function.comp]
  exact (Equiv.sum_comp e.symm _).symm

/-- **Transport of the own-fiber moment along a chain equivalence.** -/
theorem transport (π : R) (D : Matrix ι ι R) (col : ι → ZMod p) (hD : IsUnit D.det)
    (hb : ∀ a b, col a ≠ col b → D a b = 0) (τ τ0 : ZMod p)
    (e : {a // col a = τ} ≃ {a // col a = τ0}) (s s0 ℓ : ι → R)
    (hs : ∀ a, col a ≠ τ → s a = 0) (hs0 : ∀ a, col a ≠ τ0 → s0 a = 0) (ℓt0 κ d : R)
    (hDD : ∀ i j : {a // col a = τ0}, ∃ x, D (e.symm i).1 (e.symm j).1 = D i.1 j.1 + π ^ 2 * x)
    (hss : ∀ i : {a // col a = τ0}, ∃ x, s (e.symm i).1 = s0 i.1 + π ^ 2 * x)
    (hℓ : ∀ i : {a // col a = τ0}, ∃ x, ℓ (e.symm i).1 = ℓ i.1 + κ + π ^ 2 * x) :
    (∃ x, ((ℓt0 + κ) - d) - (s ᵥ* D⁻¹) ⬝ᵥ (fun a => ℓ a - d) =
      ((ℓt0 - d) - (s0 ᵥ* D⁻¹) ⬝ᵥ (fun a => ℓ a - d)) + κ * (1 - ∑ j, (s0 ᵥ* D⁻¹) j) +
        π ^ 2 * x) ∧
    (∃ x, ∑ j, (s ᵥ* D⁻¹) j = ∑ j, (s0 ᵥ* D⁻¹) j + π ^ 2 * x) := by
  choose ED hED using hDD
  choose es hes using hss
  choose eℓ heℓ using hℓ
  set B0 := blk D col τ0
  have hU := (inv_restrict D col hD hb τ).1
  have hU0 := (inv_restrict D col hD hb τ0).1
  have hsub : (blk D col τ).submatrix e.symm e.symm = B0 + π ^ 2 • Matrix.of ED := by
    ext i j
    simp only [blk, B0, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul]
    exact hED i j
  have hsv : (fun i : {a // col a = τ} => s i.1) ∘ e.symm =
      (fun i : {a // col a = τ0} => s0 i.1) + π ^ 2 • es := by
    funext i
    simp only [Function.comp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hes i
  have hdet' : IsUnit (B0 + π ^ 2 • Matrix.of ED).det := by
    rw [← hsub, Matrix.det_submatrix_equiv_self]; exact hU
  -- fiber forms
  have hform : ∀ v : ι → R, (s ᵥ* D⁻¹) ⬝ᵥ v = ∑ j : {a // col a = τ0},
      (((fun i : {a // col a = τ0} => s0 i.1) + π ^ 2 • es) ᵥ*
        (B0 + π ^ 2 • Matrix.of ED)⁻¹) j * v (e.symm j).1 := by
    intro v
    rw [own_fiber_form D col hD hb τ s v hs, reindex_form e, hsv, hsub]
  have hform0 : ∀ v : ι → R, (s0 ᵥ* D⁻¹) ⬝ᵥ v = ∑ j : {a // col a = τ0},
      ((fun i : {a // col a = τ0} => s0 i.1) ᵥ* B0⁻¹) j * v j.1 :=
    fun v => own_fiber_form D col hD hb τ0 s0 v hs0
  have hsum : ∀ (s' : ι → R), ∑ j, (s' ᵥ* D⁻¹) j = (s' ᵥ* D⁻¹) ⬝ᵥ (fun _ => 1) := by
    intro s'; simp [dotProduct]
  obtain ⟨r, hr⟩ := vecMul_inv_perturb π B0 (Matrix.of ED) hU0 hdet'
    (fun i : {a // col a = τ0} => s0 i.1) es
  constructor
  · obtain ⟨x, hx⟩ := own_shift π B0 (Matrix.of ED) hU0 hdet' (fun i => s0 i.1) es
      (fun i => ℓ i.1) eℓ ℓt0 0 d κ
    refine ⟨x, ?_⟩
    rw [hform, hform0, hsum s0, hform0]
    have e1 : ∀ j : {a // col a = τ0}, ℓ (e.symm j).1 - d = (ℓ j.1 + κ + π ^ 2 * eℓ j) - d :=
      fun j => by rw [heℓ j]
    simp_rw [e1]
    rw [mul_zero, add_zero] at hx
    rw [hx]
    simp only [mul_one]
  · refine ⟨∑ j, r j, ?_⟩
    rw [hsum s, hsum s0, hform, hform0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hr j]
    ring

end CatalanCore.Uniform.Content.UFMoments
