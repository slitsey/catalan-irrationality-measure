module

public import CatalanCore.Star.Leonard.GClosed
public import CatalanCore.Star.Leonard.DeltaFinal

/-!
# The scalar `G` of the K-step in closed form

`G = Num / Δ` with `Num` from `G_mul_Delta_closed` (Lemma N) and `Δ` from `Delta_closed`
(Prop hDelta).  `Hunif` is the uniform-weight Hankel determinant.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- **`G` in closed form** (`n = S + 1`, `K = m + n`, `N = S + m`, `x₀ = θ - S + 1`). -/
theorem G_closed (m S : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : n = S + 1) (θ : F) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    (CatalanCore.colMat fun j => zvec m n S θ j).det =
      (Vprod (asv m S θ) * Vprod (bsv m S θ) *
        Vprod (fun i : Fin (m + n) => ((i : ℕ) : F)) ^ 2 *
        (∏ b : Fin (m + n), (∏ i ∈ Finset.range (2 * (S + m)),
          ((θ - (S : F) + 1) + ((b : ℕ) : F) + (i : F)))⁻¹) *
        ((((2 * (S + m)).choose (S + m) : ℕ) : F) *
          (∏ i ∈ Finset.range (S + m), ((θ - (S : F) + 1) + ((S + m : ℕ) : F) + (i : F))) ^ 2 /
          (((S + m).factorial : ℕ) : F) ^ 2)) /
      (Vprod (xsθ (θ + (S : F)) m) * Vprod (ysθ (θ + (S : F)) m) *
        (Hunif F (m + n) m / Dpair (θ + (S : F)) (m + n) m)) := by
  have h1 := G_mul_Delta_closed m S θ hm n hn hθ hΔ
  have h2 := Delta_closed (m + n) m S θ hθ.genP (by omega)
  have hne := hΔ.ne_zero
  rw [eq_div_iff (h2 ▸ hne)]
  rw [← h2]
  exact h1

end CatalanCore.Star.Leonard
