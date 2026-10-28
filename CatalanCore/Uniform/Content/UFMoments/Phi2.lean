module

public import CatalanCore.Uniform.Content.UFMoments.Resolvent
public import CatalanCore.Uniform.Content.UFMoments.Cross
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# UF moments: the second-order function of a border node (steps (a) + (a') of (S7))

Abstract setting: a commutative ring `R` with `π` and a residue map `res : R →+* k` (`res π = 0`),
core nodes `ι` coloured by residues `col : ι → ZMod p`, embedded by an injective `φ : ZMod p →+* k`.
The core matrix is `Q = D + π E`, `D` block diagonal (own fibers, invertible), `E` cross-fiber
with Loewner reductions; the border row is `σ = s + π s'` with `s` on the own colour `τ`.
For a response `x` (`Q x = y`) and the own-fiber moment `G₀ = y_t - g·y` (`g = s D⁻¹`) assumed
divisible by `π` (`G₀ = π G₁`: the class direction), `phi2_expansion` gives

  `y_t - σ·x = π (G₁ - Bk + π Rem)`,
  `res Bk = B · Σ_{c ≠ τ} m(c)/(φ c - φ τ)`,  `B = res(1 - Σ g)`,  `m(c) = Σ_{col a = c} ζ̄_a ȳ_a`,

`ζ = D⁻¹ y`.  With `u_c = -B ȳ_c`, `B² m(c) = u_cᵀ Q̄_c⁻¹ u_c = γ(c)`: the cross-fiber part of
`Φ₂ = (G₁ - Bk)/α` is `-Σ_c γ(c)/(B²(c - τ))`, the `γ`-part of (S7).
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse of a colour-block-diagonal matrix is colour-block-diagonal. -/
theorem inv_colour_zero (D : Matrix ι ι R) (col : ι → ZMod p) (hD : IsUnit D.det)
    (h : ∀ a b, col a ≠ col b → D a b = 0) : ∀ a b, col a ≠ col b → D⁻¹ a b = 0 := by
  letI := D.invertibleOfIsUnitDet hD
  have h1 : D.BlockTriangular (fun a => (col a).val) := fun i j hij =>
    h i j (fun e => by dsimp only at hij; rw [e] at hij; exact lt_irrefl _ hij)
  have h2 : D.BlockTriangular (fun a => OrderDual.toDual (col a).val) := fun i j hij =>
    h i j (fun e => by dsimp only at hij; rw [e] at hij; exact lt_irrefl _ hij)
  have k1 := Matrix.blockTriangular_inv_of_blockTriangular h1
  have k2 := Matrix.blockTriangular_inv_of_blockTriangular h2
  intro a b hab
  rcases lt_trichotomy (col a).val (col b).val with hlt | heq | hgt
  · exact k2 (show OrderDual.toDual (col b).val < OrderDual.toDual (col a).val from hlt)
  · exact absurd (ZMod.val_injective p heq) hab
  · exact k1 hgt

variable {k : Type*} [Field k] [DecidableEq k]

/-- **The second-order expansion of a border moment, reduced.** -/
theorem phi2_expansion (π : R) (res : R →+* k) (hπ : res π = 0) (φ : ZMod p →+* k) (hφ : Function.Injective φ)
    (col : ι → ZMod p) (τ : ZMod p)
    (D E : Matrix ι ι R) (hD : IsUnit D.det)
    (hDb : ∀ a b, col a ≠ col b → D a b = 0)
    (y : ι → R) (yt : R)
    (hE0 : ∀ a b, col a = col b → E a b = 0)
    (hE : ∀ a b, col a ≠ col b → res (E a b) = (res (y b) - res (y a)) / (φ (col b) - φ (col a)))
    (s s' : ι → R) (hs : ∀ a, col a ≠ τ → s a = 0) (hs'0 : ∀ a, col a = τ → s' a = 0)
    (hs' : ∀ a, col a ≠ τ → res (s' a) = (res (y a) - res yt) / (φ (col a) - φ τ))
    (x : ι → R) (hx : D *ᵥ x + π • (E *ᵥ x) = y)
    (G₁ : R) (hG : yt - (s ᵥ* D⁻¹) ⬝ᵥ y = π * G₁) :
    ∃ Bk Rem : R, yt - (s + π • s') ⬝ᵥ x = π * (G₁ - Bk + π * Rem) ∧
      res Bk = res (1 - ∑ j, (s ᵥ* D⁻¹) j) *
        ∑ c : ZMod p, if c = τ then 0 else
          (∑ a ∈ univ.filter (fun a => col a = c), res ((D⁻¹ *ᵥ y) a) * res (y a)) /
            (φ c - φ τ) := by
  set g := s ᵥ* D⁻¹
  set ζ := D⁻¹ *ᵥ y
  have hmo := moment_second_order π D E hD y x hx s s' yt
  refine ⟨s' ⬝ᵥ ζ - g ⬝ᵥ (E *ᵥ ζ), s' ⬝ᵥ (D⁻¹ *ᵥ (E *ᵥ x)) -
      s ⬝ᵥ (D⁻¹ *ᵥ (E *ᵥ (D⁻¹ *ᵥ (E *ᵥ x)))), ?_, ?_⟩
  · rw [hmo, dotProduct_mulVec, dotProduct_mulVec s D⁻¹ (E *ᵥ ζ), hG]
    ring
  · -- reduce and apply `cross_eval`
    have hginv := inv_colour_zero D col hD hDb
    have hg : ∀ a, col a ≠ τ → g a = 0 := by
      intro a ha
      simp only [g, vecMul, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : col j = τ
      · rw [hginv j a (by rw [hj]; exact Ne.symm ha), mul_zero]
      · rw [hs j hj, zero_mul]
    have hcol : ∀ a, col a ≠ τ → φ (col a) ≠ φ τ := fun a ha h => ha (hφ h)
    have key := cross_eval (fun a => φ (col a)) (φ τ) (fun a => res (y a)) (res yt)
      (fun a => res (g a)) (fun a => res (ζ a)) (fun a => res (s' a)) (E.map res)
      (fun a ha => by
        have : col a ≠ τ := fun h => ha (by rw [h])
        rw [hg a this, map_zero])
      (fun j a hj ha => by
        have hj' : col j = τ := hφ hj
        have ha' : col a ≠ τ := fun h => ha (by rw [h])
        rw [Matrix.map_apply, hE j a (by rw [hj']; exact Ne.symm ha'), hj])
      (fun j a hj ha => by
        rw [Matrix.map_apply, hE0 j a (by rw [hφ hj, hφ ha]), map_zero])
      (fun a ha => hs' a (fun h => ha (by rw [h])))
      (fun a ha => by rw [hs'0 a (hφ ha), map_zero])
    have hG0 : res yt - (fun a => res (g a)) ⬝ᵥ (fun a => res (y a)) = 0 := by
      have := congrArg res hG
      simp only [map_sub, map_mul, hπ, zero_mul, dotProduct, map_sum] at this
      simpa [dotProduct] using this
    have lhs : res (s' ⬝ᵥ ζ - g ⬝ᵥ (E *ᵥ ζ)) =
        (fun a => res (s' a)) ⬝ᵥ (fun a => res (ζ a)) -
          (fun a => res (g a)) ⬝ᵥ (E.map res *ᵥ fun a => res (ζ a)) := by
      simp only [dotProduct, mulVec, map_sum, map_mul, map_sub, Matrix.map_apply]
    have e1 : ∀ a, (if φ (col a) = φ τ then 0 else
        res (ζ a) * ((1 - ∑ j, res (g j)) * res (y a) - 0) / (φ (col a) - φ τ)) =
        if col a = τ then 0 else
          res (1 - ∑ j, g j) * (res (ζ a) * res (y a)) / (φ (col a) - φ τ) := by
      intro a
      by_cases ha : col a = τ
      · simp [ha]
      · have : φ (col a) ≠ φ τ := hcol a ha
        simp only [this, ha, ↓reduceIte, map_sub, map_one, map_sum]
        ring
    rw [lhs, key, hG0, Finset.mul_sum]
    simp_rw [e1]
    rw [← Finset.sum_fiberwise univ col (fun a => if col a = τ then 0 else
      res (1 - ∑ j, g j) * (res (ζ a) * res (y a)) / (φ (col a) - φ τ))]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c = τ
    · simp only [hc, ↓reduceIte, mul_zero]
      apply Finset.sum_eq_zero
      intro a ha
      have hac : col a = τ := (Finset.mem_filter.1 ha).2
      simp only [hac, ↓reduceIte]
    · simp only [hc, ↓reduceIte]
      rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hac : col a = c := (Finset.mem_filter.1 ha).2
      simp only [hac, hc, ↓reduceIte]
      ring

end CatalanCore.Uniform.Content.UFMoments
