module

public import CatalanCore.Star.Leonard.Refl
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Jets of `∏ (1 + c_i W)` modulo `W⁴` (tool for package H2)

`R4 F = F[X]/(X⁴)`; `phi : F[X] →ₐ R4`.  For the arithmetic progression `c_i = S + 2(i+1)` the
product `∏_{i<m} (1 + c_i X)` has, modulo `X⁴`, the closed-form low coefficients (scaled by 6 to
avoid division):  `6, 6mc, 3m(m-1)c² - m(m²-1), m(m-1)(m-2)c³ - (m-2)c m(m²-1)` with `c = S+m+1`.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- `F[X]/(X⁴)`. -/
abbrev R4 (F : Type*) [Field F] := F[X] ⧸ Ideal.span {(X : F[X]) ^ 4}

/-- The quotient map. -/
noncomputable def phi (F : Type*) [Field F] : F[X] →ₐ[F] R4 F := Ideal.Quotient.mkₐ F _

lemma phi_eq_zero_iff {f : F[X]} : phi F f = 0 ↔ (X : F[X]) ^ 4 ∣ f := by
  unfold phi
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

lemma phi_X_pow_four : (phi F X) ^ 4 = 0 := by
  rw [← map_pow, phi_eq_zero_iff]

/-- Scaled jet coefficients: `A k m S`. -/
noncomputable def jA0 : F := 6
noncomputable def jA1 (m : ℕ) (S : F) : F := 6 * m * (S + m + 1)
noncomputable def jA2 (m : ℕ) (S : F) : F :=
  3 * m * (m - 1) * (S + m + 1) ^ 2 - m * (m ^ 2 - 1)
noncomputable def jA3 (m : ℕ) (S : F) : F :=
  m * (m - 1) * (m - 2) * (S + m + 1) ^ 3 - (m - 2) * (S + m + 1) * (m * (m ^ 2 - 1))

lemma jA1_succ (m : ℕ) (S : F) : jA1 (m + 1) S = jA1 m S + (S + 2 * ((m : F) + 1)) * 6 := by
  unfold jA1; push_cast; ring

lemma jA2_succ (m : ℕ) (S : F) : jA2 (m + 1) S = jA2 m S + (S + 2 * ((m : F) + 1)) * jA1 m S := by
  unfold jA2 jA1; push_cast; ring

lemma jA3_succ (m : ℕ) (S : F) : jA3 (m + 1) S = jA3 m S + (S + 2 * ((m : F) + 1)) * jA2 m S := by
  unfold jA3 jA2; push_cast; ring

/-- The reflected progression product, modulo `X⁴`. -/
lemma jet_prod (S : F) (m : ℕ) :
    (6 : R4 F) * phi F (∏ i ∈ Finset.range m, lin (S + 2 * ((i : F) + 1)) 1) =
      6 + algebraMap F (R4 F) (jA1 m S) * phi F X + algebraMap F (R4 F) (jA2 m S) * phi F X ^ 2
        + algebraMap F (R4 F) (jA3 m S) * phi F X ^ 3 := by
  induction m with
  | zero => simp [jA1, jA2, jA3]
  | succ m ih =>
    have hC : ∀ c : F, phi F (C c) = algebraMap F (R4 F) c := fun c => by
      rw [← Polynomial.algebraMap_eq]; exact (phi F).commutes c
    have hl : phi F (lin (S + 2 * ((m : F) + 1)) 1) =
        algebraMap F (R4 F) (S + 2 * ((m : F) + 1)) * phi F X + 1 := by
      simp [lin, hC]
    have e6 : (6 : R4 F) * (phi F (∏ i ∈ Finset.range m, lin (S + 2 * ((i : F) + 1)) 1) *
        phi F (lin (S + 2 * ((m : F) + 1)) 1)) =
        (6 * phi F (∏ i ∈ Finset.range m, lin (S + 2 * ((i : F) + 1)) 1)) *
          phi F (lin (S + 2 * ((m : F) + 1)) 1) := by ring
    rw [Finset.prod_range_succ, map_mul, e6, ih, hl, jA1_succ, jA2_succ, jA3_succ]
    simp only [map_add, map_mul, map_ofNat, map_natCast, map_one]
    linear_combination (algebraMap F (R4 F) (jA3 m S) * (algebraMap F (R4 F) S + 2 * ((m : R4 F) + 1))) *
      (phi_X_pow_four (F := F))

end CatalanCore.Star.Leonard
