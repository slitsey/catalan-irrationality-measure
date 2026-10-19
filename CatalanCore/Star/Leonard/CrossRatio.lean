module

public import CatalanCore.Star.Leonard.CommN
public import CatalanCore.Star.Leonard.CommPi

/-!
# Cross-ratio for the concrete pair `(Ã, T~)` (package H4: L1 applied)

`Ã = Π N_S Π` (equal to `Π N_S` on `ker W_Xᵀ`).  With `T~ Π = Π T~` (`Ttil_comm_projB`), `T~` preserving
`range W_Y` (`Ttil_preserves_WY`) and `[N_S, T~] x ∈ range W_Y` on `ker W_Xᵀ` (`comm_N_mem`), the bordered
commutation hypotheses of `bkdet_cross_ratio` hold, so the ratio `u(Ã, v)/u(T~, v)` is independent of `v`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- `Ã = Π N_S Π`. -/
noncomputable def Atil (m n S : ℕ) (θ : F) : Matrix (Fin (m + n)) (Fin (m + n)) F :=
  projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *
    Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) S *
    projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ))

theorem cross_ratio_Atil [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)
    (v0 : Fin (m + n) → F)
    (hcyc : bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ) v0 ≠ 0)
    (v v' : Fin (m + n) → F) :
    bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ) v *
        bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ) v' =
      bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Atil m n S θ) v' *
        bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ) v := by
  set WX := Wb (m + n) θ (bX m (S : ℤ)) with hWX
  set WY := Wb (m + n) θ (bY m (S : ℤ)) with hWY
  set T := Ttil (m + n) m S θ with hT
  set P := projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) with hP
  set N := Nsum (fun y : ℕ => wcol (m + n) θ (y : ℤ)) S with hN
  set G := WXᵀ * WY with hG
  have hMG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hΔ
  have hGM : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΔ
  have hPW : P * WY = 0 := by
    rw [hP]; unfold projB
    rw [← hWX, ← hWY, ← hG, Matrix.sub_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hG, hMG, Matrix.mul_one, sub_self]
  have hXP : WXᵀ * P = 0 := by
    rw [hP]; unfold projB
    rw [← hWX, ← hWY, ← hG, Matrix.mul_sub, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hG, hGM, Matrix.one_mul, sub_self]
  have hcomm : T * P = P * T := Ttil_comm_projB m n S hm θ hθ hΔ
  have hPw : ∀ w ∈ CatalanCore.Wsp WY, P *ᵥ w = 0 := by
    rintro w ⟨b, rfl⟩
    change P *ᵥ (WY *ᵥ b) = 0
    rw [Matrix.mulVec_mulVec, hPW, Matrix.zero_mulVec]
  have hker : ∀ x, WXᵀ *ᵥ (P *ᵥ x) = 0 := by
    intro x; rw [Matrix.mulVec_mulVec, hXP, Matrix.zero_mulVec]
  refine bkdet_cross_ratio (T := T) (N := Atil m n S θ) ?_ (Ttil_preserves_WY m n S hm θ hθ) ?_
    hcyc v v'
  · intro x hx
    have : Atil m n S θ *ᵥ x = 0 := by
      unfold Atil
      rw [← hP, ← hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPw x hx]
      simp
    rw [this]; exact Submodule.zero_mem _
  · intro x
    have h1 : (Atil m n S θ * T - T * Atil m n S θ) *ᵥ x =
        P *ᵥ (N *ᵥ (T *ᵥ (P *ᵥ x)) - T *ᵥ (N *ᵥ (P *ᵥ x))) := by
      unfold Atil
      rw [← hP, ← hN]
      rw [Matrix.sub_mulVec]
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      have e1 : P * N * P * T = P * (N * (T * P)) := by
        calc P * N * P * T = P * N * (P * T) := by simp only [Matrix.mul_assoc]
          _ = P * N * (T * P) := by rw [hcomm]
          _ = P * (N * (T * P)) := by simp only [Matrix.mul_assoc]
      have e2 : T * (P * N * P) = P * (T * (N * P)) := by
        calc T * (P * N * P) = (T * P) * N * P := by simp only [Matrix.mul_assoc]
          _ = (P * T) * N * P := by rw [hcomm]
          _ = P * (T * (N * P)) := by simp only [Matrix.mul_assoc]
      rw [e1, e2]
    rw [h1, hPw _ (comm_N_mem m n S hm θ hθ (P *ᵥ x) (hker x))]
    exact Submodule.zero_mem _

end CatalanCore.Star.Leonard
