module

public import CatalanCore.Star.Leonard.CrossRatio
public import CatalanCore.Linalg.KrylovV2

/-!
# The diagonal step (package H4): instances `(θ, S)` and `(θ - 1, S + 1)` share the borders
`W_X, W_Y`; `Ã' = Ã + (Π c₀)(Πᵀ c₀)ᵀ`, so `bkdet_ds` applies.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma wcol_shift (K : ℕ) (θ : F) (y : ℤ) : wcol K (θ - 1) (y + 1) = wcol K θ y := by
  funext a; simp only [wcol]; congr 1; push_cast; ring

lemma Wb_shift_X (m n S : ℕ) (θ : F) :
    Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)) = Wb (m + n) θ (bX m (S : ℤ)) := by
  ext a i; simp only [Wb, Matrix.of_apply, wcol, bX]; congr 1; push_cast; ring

lemma Wb_shift_Y (m n S : ℕ) (θ : F) :
    Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ)) = Wb (m + n) θ (bY m (S : ℤ)) := by
  ext a i; simp only [Wb, Matrix.of_apply, wcol, bY]; congr 1; push_cast; ring

lemma projB_shift (m n S : ℕ) (θ : F) :
    projB (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)) (bY m ((S + 1 : ℕ) : ℤ)) =
      projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) := by
  unfold projB; rw [Wb_shift_X, Wb_shift_Y]

lemma Nsum_shift (m n : ℕ) (θ : F) (S : ℕ) :
    Nsum (fun y : ℕ => wcol (m + n) (θ - 1) (y : ℤ)) (S + 1) =
      Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) S +
        Matrix.vecMulVec (wcol (m + n) θ 0) (wcol (m + n) θ 0) := by
  induction S with
  | zero =>
    rw [Nsum_succ]
    have h0 : Nsum (fun y : ℕ => wcol (m + n) (θ - 1) (y : ℤ)) 0 = 0 := by
      simp [Nsum]
    have h1 : Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) 0 = 0 := by simp [Nsum]
    have h2 : wcol (m + n) (θ - 1) (((0 + 1 : ℕ)) : ℤ) = wcol (m + n) θ 0 := by
      have := wcol_shift (m + n) θ 0; simpa using this
    rw [h0, h1, h2]
  | succ S ih =>
    rw [Nsum_succ, ih, Nsum_succ (fun y : ℕ => wcol (m + n) θ (y : ℤ)) S]
    have h2 : wcol (m + n) (θ - 1) (((S + 1 + 1 : ℕ)) : ℤ) = wcol (m + n) θ ((S + 1 : ℕ) : ℤ) := by
      have := wcol_shift (m + n) θ ((S + 1 : ℕ) : ℤ); push_cast at this ⊢; exact this
    rw [h2]; abel

/-- `Ã` of the shifted instance is `Ã` plus a rank-one term along `Π c₀`. -/
lemma Atil_shift (m n S : ℕ) (θ : F) :
    Atil m n (S + 1) (θ - 1) = Atil m n S θ +
      Matrix.vecMulVec
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0)
        ((projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)))ᵀ *ᵥ wcol (m + n) θ 0) := by
  unfold Atil
  rw [projB_shift, Nsum_shift, Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.mulVec_transpose]

/-- **The diagonal step (H4), concrete.**  For `Ã = Π N_S Π`, `Ã' = Π N'_{S+1} Π` of the instances
`(θ, S)` and `(θ - 1, S + 1)` (same borders), with cyclic start vector `v₀`:
`u(Ã, v_S) u(T~, v₀) u(T~', v_S) = u(Ã', v_S) u(T~, v_S) u(T~', v₀)`. -/
theorem ds_concrete [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)
    (hθ' : Gen (θ - 1))
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (v0 vS : Fin (m + n) → F)
    (hcyc : bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ) v0 ≠ 0)
    (hcyc' : bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1)) v0 ≠ 0)
    (hv0 : v0 = projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) :
    bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ) vS *
        bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ) v0 *
        bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1)) vS =
      bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n (S + 1) (θ - 1)) vS *
        bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ) vS *
        bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m (S + 1) (θ - 1)) v0 := by
  obtain ⟨hA, hc⟩ := Atil_hyps m n S hm θ hθ hΔ
  have hΔ' : IsUnit ((Wb (m + n) (θ - 1) (bX m ((S + 1 : ℕ) : ℤ)))ᵀ *
      Wb (m + n) (θ - 1) (bY m ((S + 1 : ℕ) : ℤ))).det := by
    rw [Wb_shift_X, Wb_shift_Y]; exact hΔ
  obtain ⟨hA', hc'⟩ := Atil_hyps m n (S + 1) hm (θ - 1) hθ' hΔ'
  have hT := Ttil_preserves_WY m n S hm θ hθ
  have hT' := Ttil_preserves_WY m n (S + 1) hm (θ - 1) hθ'
  rw [Wb_shift_Y] at hA' hc' hT'
  exact bkdet_ds hA hT hc hA' hT' hc' v0 vS _ (by rw [hv0]; exact Atil_shift m n S θ) hcyc hcyc'

end CatalanCore.Star.Leonard
