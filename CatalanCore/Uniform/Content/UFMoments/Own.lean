module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# UF moments, step (b): transport of the own-fiber moment to second order

For one border node with own chain block `D` (invertible), own border entries `s` and prefix values
`ℓ` on the chain and `ℓ_t` at the node, the own-fiber moment along a direction `d` is

  `G(d) = (ℓ_t - d) - Σ_i g_i (ℓ_i - d)`,   `g = s D⁻¹`.

`own_shift`: if a second node has data `D' ≡ D`, `s' ≡ s` modulo `π²` and prefix values shifted by
a COMMON constant `κ` modulo `π²` (`ℓ' ≡ ℓ + κ`, `ℓ'_t ≡ ℓ_t + κ`), then

  `G'(d) ≡ G(d) + κ (1 - Σ g)   (mod π²)`.

With `κ = π κ₁` (the regular prefix step `p(h(t') - h(t))`) and `G(d) = π G₁` this gives
`G₁' ≡ G₁ + κ₁ B (mod π)`: on a joint type the own part of `Φ₂` is `const + h̃(t̄)`.
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFMoments

variable {R : Type*} [CommRing R] {o : Type*} [Fintype o] [DecidableEq o]

/-- A `π²`-perturbation of an invertible block perturbs `s D⁻¹` by `π²`. -/
theorem vecMul_inv_perturb (π : R) (D ED : Matrix o o R) (hD : IsUnit D.det)
    (hD' : IsUnit (D + π ^ 2 • ED).det) (s es : o → R) :
    ∃ r : o → R, ∀ i, ((s + π ^ 2 • es) ᵥ* (D + π ^ 2 • ED)⁻¹) i = (s ᵥ* D⁻¹) i + π ^ 2 * r i := by
  set D' := D + π ^ 2 • ED
  have hres : D⁻¹ = D'⁻¹ + π ^ 2 • (D⁻¹ * ED * D'⁻¹) := by
    have h1 : D⁻¹ * D' = 1 + π ^ 2 • (D⁻¹ * ED) := by
      simp only [D', Matrix.mul_add, Matrix.mul_smul, nonsing_inv_mul _ hD]
    calc D⁻¹ = D⁻¹ * D' * D'⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hD', Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have hD'inv : D'⁻¹ = D⁻¹ - π ^ 2 • (D⁻¹ * ED * D'⁻¹) := eq_sub_of_add_eq hres.symm
  have h3 : s ᵥ* D'⁻¹ = s ᵥ* D⁻¹ - π ^ 2 • (s ᵥ* (D⁻¹ * ED * D'⁻¹)) := by
    conv_lhs => rw [hD'inv]
    rw [vecMul_sub, vecMul_smul]
  refine ⟨es ᵥ* D'⁻¹ - s ᵥ* (D⁻¹ * ED * D'⁻¹), fun i => ?_⟩
  rw [add_vecMul, smul_vecMul, h3]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Own-fiber transport to second order.** -/
theorem own_shift (π : R) (D ED : Matrix o o R) (hD : IsUnit D.det)
    (hD' : IsUnit (D + π ^ 2 • ED).det) (s es ℓ eℓ : o → R) (ℓt et d κ : R) :
    ∃ e : R,
      ((ℓt + κ + π ^ 2 * et) - d) - ∑ i, ((s + π ^ 2 • es) ᵥ* (D + π ^ 2 • ED)⁻¹) i *
          ((ℓ i + κ + π ^ 2 * eℓ i) - d) =
        ((ℓt - d) - ∑ i, (s ᵥ* D⁻¹) i * (ℓ i - d)) + κ * (1 - ∑ i, (s ᵥ* D⁻¹) i) +
          π ^ 2 * e := by
  obtain ⟨r, hr⟩ := vecMul_inv_perturb π D ED hD hD' s es
  set g := s ᵥ* D⁻¹
  refine ⟨et - ∑ i, (g i * eℓ i + r i * ((ℓ i + κ + π ^ 2 * eℓ i) - d)), ?_⟩
  have hsum : ∑ i, ((s + π ^ 2 • es) ᵥ* (D + π ^ 2 • ED)⁻¹) i * ((ℓ i + κ + π ^ 2 * eℓ i) - d) =
      ∑ i, g i * (ℓ i - d) + κ * ∑ i, g i +
        π ^ 2 * ∑ i, (g i * eℓ i + r i * ((ℓ i + κ + π ^ 2 * eℓ i) - d)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hr i]
    ring
  rw [hsum]
  ring

end CatalanCore.Uniform.Content.UFMoments
