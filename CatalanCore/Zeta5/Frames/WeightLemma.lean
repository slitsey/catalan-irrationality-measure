module

public import CatalanCore.Zeta5.Local.BasisChange
public import CatalanCore.Zeta5.Local.Val

@[expose] public section

/-!
# ZC10: the Gauss-DVR weight lemma

If `v^G(M_{ij}) ≥ w_i + w_j` for the Gram matrix `M` written in a `ℤ_p`-unimodular basis, then
`v^G(det) ≥ 2 ∑ w_i`.

* `zc10_weight`: generic form. `G` is a Gram matrix over `ℚ[X]` in some basis, `Cm` a rational
  change of basis whose determinant is a `p`-adic unit (`det ≠ 0`, `v_p(det) = 0`), and
  `Cm G Cmᵀ` has entry bounds `w_i + w_j`; then `v^G(det G) ≥ 2 ∑ w`.
* `zc10_delta`: the Hankel form `Δ_K`: polynomials `E_a` of degree `< h = 37 n` whose coefficient
  matrix is a `p`-adic unit, with `v^G(μ_X(D_N⁶ E_a E_b / D_K)) ≥ w_a + w_b`, give
  `v^G(Δ_K) ≥ 2 ∑ w`.
-/

open Finset Polynomial

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

/-- The inverse of a `p`-adic unit is a `p`-adic integer. -/
lemma VG_inv_unit {d : ℚ} (hd : d ≠ 0) (hv : padicValRat p d = 0) : VG p d⁻¹ 0 := by
  have := VG.inv (p := p) (r := 0) hd (by rw [hv]; simp)
  simpa using this

/-- **ZC10, generic form.** -/
theorem zc10_weight {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℚ[X])
    (Cm : Matrix ι ι ℚ) (hdet : Cm.det ≠ 0) (hunit : padicValRat p Cm.det = 0) (w : ι → ℚ)
    (h : ∀ i j, GV p ((Cm.map (C : ℚ →+* ℚ[X]) * G * (Cm.map (C : ℚ →+* ℚ[X])).transpose) i j)
      (w i + w j)) :
    GV p G.det (2 * ∑ i, w i) := by
  have hdetM : (Cm.map (C : ℚ →+* ℚ[X]) * G * (Cm.map (C : ℚ →+* ℚ[X])).transpose).det =
      C (Cm.det ^ 2) * G.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, map_pow]
    ring
  have key := det_GV (p := p) _ w w h
  rw [hdetM] at key
  have hΔ : G.det = C ((Cm.det ^ 2)⁻¹) * (C (Cm.det ^ 2) * G.det) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hdet), C_1, one_mul]
  rw [hΔ]
  have hu : VG p ((Cm.det ^ 2)⁻¹) 0 := by
    refine (VG_inv_unit (p := p) (pow_ne_zero _ hdet) ?_)
    rw [padicValRat.pow, hunit]; simp
  have e : ∑ i, w i + ∑ i, w i = 2 * ∑ i, w i := by ring
  rw [e] at key
  simpa using GV.C_mul hu key

/-- **ZC10, Hankel form.** Polynomials `E_a` (`a < 37 n`) of degree `< 37 n` with a `p`-adic
unit coefficient matrix and entry bounds `w_a + w_b` for `μ_X(D_N⁶ E_a E_b / D_K)` give
`v^G(Δ_K) ≥ 2 ∑ w`. -/
theorem zc10_delta (n : ℕ) (E : Fin (37 * n) → ℚ[X]) (hE : ∀ a, (E a).natDegree < 37 * n)
    (hdet : (coeffMat E).det ≠ 0) (hunit : padicValRat p (coeffMat E).det = 0)
    (w : Fin (37 * n) → ℚ)
    (h : ∀ a b, GV p (μX (40 * n) (D (3 * n) ^ 6 * E a * E b)) (w a + w b)) :
    GV p (Δ n) (2 * ∑ a, w a) := by
  have hbc := det_basis_change n E hE
  have key := det_GV (p := p) (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)) w w
    (fun i j => by simpa using h i j)
  rw [hbc] at key
  have hΔ : Δ n = C (((coeffMat E).det ^ 2)⁻¹) * (C ((coeffMat E).det ^ 2) * Δ n) := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hdet), C_1, one_mul]
  rw [hΔ]
  have hu : VG p (((coeffMat E).det ^ 2)⁻¹) 0 := by
    refine (VG_inv_unit (p := p) (pow_ne_zero _ hdet) ?_)
    rw [padicValRat.pow, hunit]; simp
  have e : ∑ i, w i + ∑ i, w i = 2 * ∑ i, w i := by ring
  rw [e] at key
  simpa using GV.C_mul hu key

end Apery
