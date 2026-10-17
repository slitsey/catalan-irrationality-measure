module

public import CatalanArchive.CatalanMeasure.Parametric.ContactShift
public import Mathlib.Tactic.Ring

/-!
# Uniform shifts of the monomial contact basis

These concrete polynomials are the simpler basis suggested by the finite
row-space checks. Their shift relation has a single boundary term. Equality
of this basis with the actual Chebyshev row space remains a separate theorem.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

set_option autoImplicit false

open Polynomial

noncomputable def monomialContactD (f V : ℚ[X]) (L u : ℕ) : ℚ[X] :=
  f * contactTrunc L (X ^ (u + 1) * V)

noncomputable def monomialContactQ (f W : ℚ[X]) (u : ℕ) : ℚ[X] :=
  f * X ^ (u + 1) * W

theorem monomialContactQ_shift (f W : ℚ[X]) (u : ℕ) :
    monomialContactQ f W (u + 1) = X * monomialContactQ f W u := by
  unfold monomialContactQ
  rw [pow_succ]
  ring

theorem monomialContactD_boundary (f V : ℚ[X]) {L : ℕ} (hL : 0 < L) (u : ℕ) :
    monomialContactD f V L (u + 1) +
      f * monomial L ((X ^ (u + 1) * V).coeff (L - 1)) =
      X * monomialContactD f V L u := by
  have h := contactTrunc_X_boundary hL (X ^ (u + 1) * V)
  have hshift : X * (X ^ (u + 1) * V) = X ^ ((u + 1) + 1) * V := by
    rw [pow_succ]
    ring
  rw [hshift] at h
  have hh := congrArg (fun A : ℚ[X] => f * A) h
  simp only [mul_add] at hh
  unfold monomialContactD
  convert hh using 1 <;> ring

end CatalanMeasure.Parametric
