module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3J

@[expose] public section

/-!
# Lemma E, class 3: the three linear systems `M0 V1 = B1`, `N1 V1 + D1 V2 = B2`, `G1 V1 + G2 V2 = 0`
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {o p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

variable (S : ESetup3 o p r m k1)

include S

lemma h1_sys (c : Pt3 p r m) (y : Fin m) :
    ∑ c', Mat3 p r m (sd3 S) (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inl c')) * V1 S c' y =
      Mat3 p r m (sd3 S) (Sum.inl (Sum.inl c)) (Sum.inr y) := by
  have hN := S.hN; have hpr := S.hpr; have hk2r := S.hk2r; have hk1 := S.hk1o
  obtain ⟨he1, he2⟩ := e0_bounds S y
  have hy := y.2
  rw [Finset.sum_eq_single (e0 S y)]
  · simp only [V1, if_true]
    rw [Mat3_pp, Mat3_py, rfC_eq, rfC_eq, rfC_eq, ← map_mul]
    congr 1
    rw [TE3_PY S c.1.2 c.2 (show r ≤ r + 2 * (y : ℕ) + 1 by omega)]
    by_cases hc : c = e0 S y
    · rw [hc, TE3_PP S (e0 S y).1.2 (e0 S y).2 (e0 S y).1.2 (e0 S y).2, if_pos rfl,
        dZ_B1 S he1 he2, if_pos (by rw [e0_val]; omega),
        singG_mid S he1 he2 (by omega)]
      ring
    · have hc' : (c.1 : ℕ) ≠ r + 2 * (y : ℕ) + 1 - p := by
        intro h; apply hc; apply Subtype.ext; apply Fin.ext; rw [e0_val]; exact h
      rw [TE3_PP S c.1.2 c.2 (e0 S y).1.2 (e0 S y).2, if_neg (by rw [e0_val]; exact fun h => hc' h.symm),
        if_neg, if_neg (by omega)]
      · simp
      · rw [e0_val]
        intro h
        unfold tauN at h
        split_ifs at h <;> omega
  · intro c' _ hne
    simp [V1, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma h2_sys (w : Wt3 p r m) (y : Fin m) :
    ∑ c', Mat3 p r m (sd3 S) (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inl c')) * V1 S c' y +
    ∑ w', Mat3 p r m (sd3 S) (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inr w')) * V2 w' y =
      Mat3 p r m (sd3 S) (Sum.inl (Sum.inr w)) (Sum.inr y) := by
  have hN := S.hN; have hpr := S.hpr; have hk2r := S.hk2r; have hk1 := S.hk1o
  obtain ⟨hw1, hw2, hw3⟩ := wC_bounds S w
  have hy := y.2
  have hfirst : ∑ c', Mat3 p r m (sd3 S) (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inl c')) *
      V1 S c' y = 0 := by
    rw [Finset.sum_eq_single (e0 S y)]
    · simp only [V1, if_true]
      rw [Mat3_wp, TE3_WP0 S w y, rfC_zero, zero_mul]
    · intro c' _ hne
      simp [V1, hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsecond : ∑ w', Mat3 p r m (sd3 S) (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inr w')) *
      V2 w' y = V2 w y := by
    rw [Finset.sum_eq_single w]
    · rw [Mat3_ww, TE3_WW S w.1.2 w.2 w.1.2 w.2, if_pos rfl, rfC_one, one_mul]
    · intro w' _ hne
      have hne' : (w'.1 : ℕ) ≠ w.1 := fun h => hne (Subtype.ext (Fin.ext h))
      rw [Mat3_ww, TE3_WW S w.1.2 w.2 w'.1.2 w'.2, if_neg hne', rfC_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hfirst, hsecond, zero_add, Mat3_wy]
  unfold V2
  congr 1
  have hwc' := w.2
  unfold isCz at hwc'
  rw [TE3_WY S w.1.2 w.2 (show r ≤ r + 2 * (y : ℕ) + 1 by omega) (by omega),
    singG_mid S hw1 hw2 (by omega)]

lemma h3_sys (x y : Fin m) :
    ∑ c', Mat3 p r m (sd3 S) (Sum.inr x) (Sum.inl (Sum.inl c')) * V1 S c' y +
    ∑ w', Mat3 p r m (sd3 S) (Sum.inr x) (Sum.inl (Sum.inr w')) * V2 w' y = 0 := by
  have hN := S.hN; have hpr := S.hpr; have hk2r := S.hk2r; have hk1 := S.hk1o
  have hy := y.2
  have hx := x.2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨he1, he2⟩ := e0_bounds S y
  obtain ⟨hw1, hw2, hw3⟩ := wC_bounds S (ww S x)
  have hxcast : (((r + 2 * (x : ℕ) - p : ℕ)) : ZMod p) = ((r + 2 * (x : ℕ) : ℕ) : ZMod p) :=
    cast_sub_p S (by omega)
  have hycast : (((r + 2 * (y : ℕ) + 1 - p : ℕ)) : ZMod p) = ((r + 2 * (y : ℕ) + 1 : ℕ) : ZMod p) :=
    cast_sub_p S (by omega)
  have hfirst : ∑ c', Mat3 p r m (sd3 S) (Sum.inr x) (Sum.inl (Sum.inl c')) * V1 S c' y =
      rfC p ((16 * (((r + 2 * (x : ℕ) : ℕ) : ZMod p) - ((r + 2 * (y : ℕ) + 1 : ℕ) : ZMod p)))⁻¹ *
        s3 p) * rfC p ((16 : ZMod p)⁻¹ * s3 p) := by
    rw [Finset.sum_eq_single (e0 S y)]
    · simp only [V1, if_true]
      rw [Mat3_xp]
      rw [TE3_XP S (show r ≤ r + 2 * (x : ℕ) by omega) (e0 S y).1.2 (e0 S y).2
        (by rw [e0_val]; omega), singG_mid S he1 he2 (by omega), e0_val, hycast]
    · intro c' _ hne
      simp [V1, hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsecond : ∑ w', Mat3 p r m (sd3 S) (Sum.inr x) (Sum.inl (Sum.inr w')) * V2 w' y =
      rfC p ((16 : ZMod p)⁻¹ * s3 p) * rfC p ((16 * (((r + 2 * (y : ℕ) + 1 : ℕ) : ZMod p) -
        ((r + 2 * (x : ℕ) : ℕ) : ZMod p)))⁻¹ * s3 p) := by
    rw [Finset.sum_eq_single (ww S x)]
    · rw [Mat3_xw, TE3_XW S (show r ≤ r + 2 * (x : ℕ) by omega) (ww S x).1.2 (ww S x).2,
        if_pos (by rw [ww_val]; omega), singG_mid S hw1 hw2 (by omega)]
      unfold V2
      rw [ww_val, hxcast]
    · intro w' _ hne
      have hne' : (w'.1 : ℕ) ≠ r + 2 * (x : ℕ) - p := by
        intro h; apply hne; apply Subtype.ext; apply Fin.ext; rw [ww_val]; exact h
      rw [Mat3_xw, TE3_XW S (show r ≤ r + 2 * (x : ℕ) by omega) w'.1.2 w'.2, if_neg, rfC_zero,
        zero_mul]
      omega
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hfirst, hsecond]
  simp only [rfC_eq]
  rw [← map_mul, ← map_mul, ← map_add]
  rw [← map_zero (rfCH p)]
  congr 1
  have hneg : ((r + 2 * (y : ℕ) + 1 : ℕ) : ZMod p) - ((r + 2 * (x : ℕ) : ℕ) : ZMod p) =
      -(((r + 2 * (x : ℕ) : ℕ) : ZMod p) - ((r + 2 * (y : ℕ) + 1 : ℕ) : ZMod p)) := by ring
  rw [hneg, mul_neg, inv_neg]
  ring

end

end CatalanCore.Arith.Hybrid
