module

public import CatalanCore.Star.Leonard.ThetaZero
public import CatalanCore.Star.Leonard.DeltaUnit

/-!
# `θ → 0` for `kgen`

`kgen K m S θ = F θ` for all rationals `0 < θ < 1`, with `F` continuous at `0`, implies the same
at `θ = 0`.  The border determinant does not vanish at `0`: it is the product formula of
`Delta_closed`, an `ℓ`-unit (hence nonzero) for a large prime `ℓ`.
-/

@[expose] public section

open Finset Matrix Filter Topology CatalanCore.ThmA

namespace CatalanCore.Star

open CatalanCore.Star.Leonard

theorem det_Delta_ne_zero (K m S : ℕ) (hK : 1 ≤ K) (hmK : m ≤ K) :
    ((Wb K (0 : ℚ) (bX m (S : ℤ)))ᵀ * Wb K (0 : ℚ) (bY m (S : ℤ))).det ≠ 0 := by
  obtain ⟨ℓ, hℓ, hprime⟩ := Nat.exists_infinite_primes (S + K + 2 * m)
  haveI : Fact ℓ.Prime := ⟨hprime⟩
  exact (Delta_LU (ℓ := ℓ) K m S hmK hK hℓ).1

theorem kgenR_zero_of_generic (K m S : ℕ) (hK : 1 ≤ K) (hmK : m ≤ K) (hS : 1 ≤ S)
    (Fn : ℚ → ℚ) (hF : ContinuousAt Fn 0)
    (heq : ∀ θ : ℚ, 0 < θ → θ < 1 → kgen K m S θ = Fn θ) : kgen K m S (0 : ℚ) = Fn 0 := by
  unfold kgen kgenR at *
  exact kgenCore_zero_of_generic (K := K) (m := m) _ (S : ℤ) (bX m S) (bY m S)
    (by exact_mod_cast hS) (fun j hj => (Finset.mem_Icc.1 hj).1)
    (fun i => by simp only [bX]; omega) (fun i => by simp only [bY]; omega)
    (det_Delta_ne_zero K m S hK hmK) Fn hF heq

theorem kgenL_zero_of_generic (K m S : ℕ) (hK : 1 ≤ K) (hmK : m ≤ K) (hS : 1 ≤ S)
    (Fn : ℚ → ℚ) (hF : ContinuousAt Fn 0)
    (heq : ∀ θ : ℚ, 0 < θ → θ < 1 →
      kgenL K m θ (Finset.Icc 1 ((S : ℤ) - 1)) S = Fn θ) :
    kgenL K m (0 : ℚ) (Finset.Icc 1 ((S : ℤ) - 1)) S = Fn 0 := by
  unfold kgenL at *
  refine kgenCore_zero_of_generic (K := K) (m := m) _ (S : ℤ) (bY m S) (bX m S)
    (by exact_mod_cast hS) (fun j hj => (Finset.mem_Icc.1 hj).1)
    (fun i => by simp only [bY]; omega) (fun i => by simp only [bX]; omega) ?_ Fn hF heq
  rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  exact det_Delta_ne_zero K m S hK hmK

/-- the explicit shape of the closed form is continuous at `0` when only factors `θ + c`, `c ≥ 1`
occur in the denominator -/
theorem cA_closedForm (c : ℚ) (N : ℕ) (e : ℕ → ℕ) :
    ContinuousAt (fun θ : ℚ => c * (∏ t ∈ Finset.Icc 1 N, (θ + (t : ℚ)) ^ (e t))⁻¹) 0 := by
  refine continuousAt_const.mul ?_
  have h : ContinuousAt (fun θ : ℚ => ∏ t ∈ Finset.Icc 1 N, (θ + (t : ℚ)) ^ (e t)) 0 :=
    (continuous_finset_prod _ fun t _ => by fun_prop).continuousAt
  refine ContinuousAt.inv₀ h ?_
  simp only [zero_add]
  refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
  have := (Finset.mem_Icc.1 ht).1
  positivity

end CatalanCore.Star
