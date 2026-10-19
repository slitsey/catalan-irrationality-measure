module

public import CatalanCore.Star.Leonard.ChainInst

/-!
# The diagonal step with its cyclicity hypotheses discharged (package H4)

`ds_cyc`: the cross-ratio identity of `ds_concrete` for `v₀ = Π c₀`, `v_S = Π c_S`, with all three
cyclicity hypotheses proved from the explicit chain products of `ChainInst`.
`T'`-chain forms: the instance `(θ-1, S+1)` shares the borders and `Π`, and
`c'_{S+1} = c_S`, `c'_1 = c_0`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma wcol_shift_nat (K : ℕ) (θ : F) (y : ℕ) :
    wcol K (θ - 1) ((y + 1 : ℕ) : ℤ) = wcol K θ (y : ℤ) := by
  have := wcol_shift K θ (y : ℤ)
  simpa using this

/-- `u(T~', Π c_0)` is `u(T~', Π' c'_1)`: the upward chain of the instance `(θ-1, S+1)`. -/
theorem u_up_shift_ne [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ' : Gen (θ - 1))
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
      (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) ≠ 0 := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_up_1_ne m n (S + 1) hm (θ - 1) hθ' hΔ' (by omega)
  rw [Wb_shift_Y, projB_shift] at h
  have e : wcol (m + n) (θ - 1) 1 = wcol (m + n) θ 0 := by
    have := wcol_shift (m + n) θ 0; simpa using this
  rw [e] at h
  exact h

/-- `u(T~', Π c_S)`: the downward chain from the top of the instance `(θ-1, S+1)`. -/
theorem u_down_shift_ne [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ' : Gen (θ - 1))
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
      (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) ≠ 0 := by
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  have h := u_down_S_ne m n (S + 1) hm (θ - 1) hθ' hΔ' (by omega)
  rw [Wb_shift_Y, projB_shift, wcol_shift_nat] at h
  exact h

/-- **The diagonal step (H4)** with cyclicity discharged. -/
theorem ds_cyc [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) (hθ' : Gen (θ - 1))
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (hS : n ≤ S) (hn : 1 ≤ n) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) =
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) *
      CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1))
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) :=
  ds_concrete m n S hm θ hθ hθ' hΔ _ _ (u_down_0_ne m n S hm θ hθ hΔ hS hn)
    (u_up_shift_ne m n S hm θ hθ' hΔ hS) rfl

end CatalanCore.Star.Leonard
