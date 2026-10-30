module

public import CatalanCore.Star.Leonard.DeltaBasis
public import CatalanCore.Star.Leonard.ChainProd

/-!
# `Δ = det (W_Xᵀ W_Y)` in terms of the explicit matrix `E` (package H6 interface)

`Wb K θ (bX m S) = Cm K (θ + S + 2 + 2i)` and `Wb K θ (bY m S) = Cm K (θ + S + 1 + 2i)`, so
`Δ(K,m,S,θ) = Δ(K,m,0,θ+S)` and `delta_E` applies at `θ + S`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma Wb_bX_eq_Cm (K m S : ℕ) (θ : F) :
    Wb K θ (bX m (S : ℤ)) = Cm K (xsθ (θ + (S : F)) m) := by
  ext a i
  simp only [Wb, wcol, bX, Cm, xsθ, Matrix.of_apply]
  congr 1
  push_cast; ring

lemma Wb_bY_eq_Cm (K m S : ℕ) (θ : F) :
    Wb K θ (bY m (S : ℤ)) = Cm K (ysθ (θ + (S : F)) m) := by
  ext a i
  simp only [Wb, wcol, bY, Cm, ysθ, Matrix.of_apply]
  congr 1
  push_cast; ring

lemma Gen_add_nat {θ : F} (h : GenP θ) (S : ℕ) : GenP (θ + (S : F)) := fun z hz => by
  have := h ((S : ℤ) + z) (by omega)
  intro h0; apply this; push_cast; linear_combination h0

/-- **Prop hDelta, reduced to `det E`.** -/
theorem Delta_eq_E (K m S : ℕ) (θ : F) (hθ : GenP θ) :
    ((Wb K θ (bX m (S : ℤ)))ᵀ * Wb K θ (bY m (S : ℤ))).det =
      Vprod (xsθ (θ + (S : F)) m) * Vprod (ysθ (θ + (S : F)) m) *
        (Matrix.of fun (p q : Fin m) => ∑ a : Fin K,
          (pochr (((a : ℕ) : F) + (θ + (S : F)) + ((p : ℕ) : F) + 1)
            (2 * m - (p : ℕ) - (q : ℕ)))⁻¹).det := by
  rw [Wb_bX_eq_Cm, Wb_bY_eq_Cm]
  exact delta_E (θ + (S : F)) (Gen_add_nat hθ S) K m

end CatalanCore.Star.Leonard
