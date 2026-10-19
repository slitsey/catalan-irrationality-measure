module

public import CatalanCore.Star.Leonard.Invariance

/-!
# `T~` commutes with the projector `Π` (package H2: first half of `[T~, A] = 0`)

`T~ WY = WY B`, `WXᵀ T~ = C WXᵀ` (from (CC), (RC) at the border points, `Ttil_colY`/`TtilT_colY`),
hence `B M = M C` for `M = (WXᵀ WY)⁻¹` and `T~ Π = Π T~` for `Π = 1 - WY M WXᵀ`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- `T~ WY = WY B`. -/
lemma exists_B [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) :
    ∃ B : Matrix (Fin m) (Fin m) F, Ttil (m + n) m S θ * Wb (m + n) θ (bY m (S : ℤ)) =
      Wb (m + n) θ (bY m (S : ℤ)) * B := by
  set W := Wb (m + n) θ (bY m (S : ℤ)) with hW
  have h := fun i : Fin m => Ttil_preserves_WY m n S hm θ hθ (fun a => W a i)
    (col_mem_Wsp W i)
  choose b hb using h
  refine ⟨Matrix.of fun r i => b i r, ?_⟩
  ext a i
  have := congrFun (hb i) a
  simp only [Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [← this]
  rfl


/-- `T~ᵀ` preserves `range WX`. -/
theorem TtilT_preserves_WX [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) :
    ∀ i : Fin m, ∃ b : Fin m → F, Wb (m + n) θ (bX m (S : ℤ)) *ᵥ b =
      (Ttil (m + n) m S θ)ᵀ *ᵥ (fun a => Wb (m + n) θ (bX m (S : ℤ)) a i) := by
  set W := Wb (m + n) θ (bX m (S : ℤ)) with hW
  have hwc : ∀ (i : ℕ) (hi : i < m), wcol (m + n) θ ((S + 2 * i + 2 : ℕ) : ℤ) = fun a => W a ⟨i, hi⟩ := by
    intro i hi; funext a; simp [hW, Wb, bX, wcol]; ring_nf
  intro i
  obtain ⟨d, κ, h⟩ := TtilT_colY (m + n) m S hm θ hθ i i.2
  have hc : (fun a => W a i) = wcol (m + n) θ ((S + 2 * (i : ℕ) + 2 : ℕ) : ℤ) := by
    rw [hwc i i.2]
  rw [hc, h]
  have hmem : d • wcol (m + n) θ ((S + 2 * (i : ℕ) + 2 : ℕ) : ℤ)
      + ∑ i' ∈ Finset.range m, κ i' • wcol (m + n) θ ((S + 2 * i' + 2 : ℕ) : ℤ) ∈
      LinearMap.range (Matrix.mulVecLin W) := by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.sum_mem _ fun i' hi' => ?_)
    · rw [← hc]; exact col_mem_Wsp W i
    · refine Submodule.smul_mem _ _ ?_
      have := Finset.mem_range.1 hi'
      rw [hwc i' this]; exact col_mem_Wsp W ⟨i', this⟩
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb⟩

/-- `WXᵀ T~ = C WXᵀ`. -/
lemma exists_C [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ) :
    ∃ C : Matrix (Fin m) (Fin m) F, (Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Ttil (m + n) m S θ =
      C * (Wb (m + n) θ (bX m (S : ℤ)))ᵀ := by
  set W := Wb (m + n) θ (bX m (S : ℤ)) with hW
  choose c hc using TtilT_preserves_WX m n S hm θ hθ
  refine ⟨Matrix.of fun i r => c i r, ?_⟩
  ext i a
  have := congrFun (hc i) a
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
  have e : ∑ b, W b i * Ttil (m + n) m S θ b a = ∑ x, Ttil (m + n) m S θ x a * W x i :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e, ← this]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _


/-- **`T~ Π = Π T~`.** -/
theorem Ttil_comm_projB [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    Ttil (m + n) m S θ * projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) =
      projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) * Ttil (m + n) m S θ := by
  obtain ⟨B, hB⟩ := exists_B m n S hm θ hθ
  obtain ⟨C, hC⟩ := exists_C m n S hm θ hθ
  set WX := Wb (m + n) θ (bX m (S : ℤ)) with hWX
  set WY := Wb (m + n) θ (bY m (S : ℤ)) with hWY
  set T := Ttil (m + n) m S θ with hT
  set G := WXᵀ * WY with hG
  have hGB : G * B = C * G := by
    have : WXᵀ * (T * WY) = (WXᵀ * T) * WY := by rw [Matrix.mul_assoc]
    rw [hB, hC] at this
    simpa [hG, Matrix.mul_assoc] using this
  have hMG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hΔ
  have hGM : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΔ
  have hBM : B * G⁻¹ = G⁻¹ * C := by
    calc B * G⁻¹ = G⁻¹ * (G * B) * G⁻¹ := by
          rw [← Matrix.mul_assoc, hMG, Matrix.one_mul]
      _ = G⁻¹ * (C * G) * G⁻¹ := by rw [hGB]
      _ = G⁻¹ * C := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hGM, Matrix.mul_one]
  unfold projB
  rw [← hWX, ← hWY, ← hG]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  calc T * (WY * G⁻¹ * WXᵀ) = (T * WY) * G⁻¹ * WXᵀ := by simp only [Matrix.mul_assoc]
    _ = WY * (B * G⁻¹) * WXᵀ := by rw [hB]; simp only [Matrix.mul_assoc]
    _ = WY * (G⁻¹ * C) * WXᵀ := by rw [hBM]
    _ = WY * G⁻¹ * (C * WXᵀ) := by simp only [Matrix.mul_assoc]
    _ = WY * G⁻¹ * (WXᵀ * T) := by rw [hC]
    _ = (WY * G⁻¹ * WXᵀ) * T := by simp only [Matrix.mul_assoc]

end CatalanCore.Star.Leonard
