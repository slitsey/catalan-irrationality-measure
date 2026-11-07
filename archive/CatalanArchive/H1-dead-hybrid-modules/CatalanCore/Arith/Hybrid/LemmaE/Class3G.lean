module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3F
public import CatalanCore.Arith.Hybrid.DefBSchur

@[expose] public section

/-!
# Lemma E, class 3: invertibility of `M0` (needs `p ∤ 6255`) and of `D1`
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {o p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

variable (S : ESetup3 o p r m k1)

include S

lemma dZ_B1 {a : ℕ} (h1 : k1 ≤ a) (h2 : a < p) : dZ S a = 1 := by
  have hk1 := S.hk1o
  have h16 := h16_ne (p := p) S.p5
  unfold dZ
  rw [singG2_B1 S h1 h2]
  simp
  field_simp

lemma dZ_lo {a : ℕ} (h1 : a < k1) : dZ S a = 0 := by
  have hk1 := S.hk1o
  unfold dZ
  rw [singG2_eval S]
  have e1 : ¬ k1 ≤ a := by omega
  have e2 : ¬ p ≤ a := by omega
  have e3 : ¬ p + k1 ≤ a := by omega
  rw [if_neg e1, if_neg e2, if_neg e3]
  simp

lemma eZ_lo1 {a : ℕ} (h0 : a < k1) : eZ S a =
    (16 : ZMod p)⁻¹ * (-(4 * (((1 : ℕ) : ZMod p))⁻¹) + 1) := by
  have hk1 := S.hk1o
  have hpr := S.hpr
  have hk2r := S.hk2r
  have hrp : a < r - p := by omega
  unfold eZ
  rw [if_pos hrp, singG_eval S]
  have e1 : a < k1 ∧ k1 ≤ a + p := by omega
  have e2 : a < p ∧ p ≤ a + p := by omega
  have e3 : ¬ (a < p + k1 ∧ p + k1 ≤ a + p) := by omega
  rw [if_pos e1, if_pos e2, if_neg e3]
  ring

lemma eZ_lo2 {a : ℕ} (h0 : k1 ≤ a) (h1 : a < r - p) : eZ S a =
    (16 : ZMod p)⁻¹ * s3 p := by
  have hk1 := S.hk1o
  have hpr := S.hpr
  have hk2r := S.hk2r
  have hN := S.hN
  unfold eZ
  rw [if_pos h1, singG_mid S h0 (by omega) (by omega)]

lemma dZ_B3 {b : ℕ} (h : p + k1 ≤ b) : dZ S b =
    -(1 / 16 : ZMod p) * (-(16 * ((((1 : ℕ) : ZMod p))⁻¹) ^ 2) + 1 +
      -(16 * ((((5 : ℕ) : ZMod p))⁻¹) ^ 2)) := by
  have hk1 := S.hk1o
  unfold dZ
  rw [singG2_eval S]
  have e1 : k1 ≤ b := by omega
  have e2 : p ≤ b := by omega
  rw [if_pos e1, if_pos e2, if_pos h]

lemma num_id (h5 : (5 : ZMod p) ≠ 0) (h16 : (16 : ZMod p) ≠ 0) :
    (1 * (-(1 / 16 : ZMod p) * (-(16 * ((1 : ZMod p)⁻¹) ^ 2) + 1 + -(16 * ((5 : ZMod p)⁻¹) ^ 2))) -
      ((16 : ZMod p)⁻¹ * (1 + -(4 * (5 : ZMod p)⁻¹))) ^ 2) * 6400 = 6255 := by
  field_simp
  ring

lemma delta_core {a : ℕ} (h : a < r - p) (h3 : (3 : ZMod p) ≠ 0)
    (h5 : (5 : ZMod p) ≠ 0) (h6255 : (6255 : ZMod p) ≠ 0) :
    dZ S a * dZ S (a + p) - eZ S a ^ 2 ≠ 0 := by
  have hk1 := S.hk1o
  have hp5 := S.p5
  have h16 := h16_ne (p := p) S.p5
  have hpr := S.hpr
  have hk2r := S.hk2r
  have hN := S.hN
  rcases lt_or_ge a k1 with h1 | h1
  · rw [dZ_lo S h1, eZ_lo1 S h1]
    have : (16 : ZMod p)⁻¹ * (-(4 * (((1 : ℕ) : ZMod p))⁻¹) + 1) ≠ 0 := by
      refine mul_ne_zero (inv_ne_zero h16) ?_
      intro hh
      apply h3
      simp at hh
      linear_combination -hh
    simpa using this
  · have ha : a < p := by omega
    rw [dZ_B1 S h1 ha, dZ_B3 S (b := a + p) (by omega), eZ_lo2 S h1 h]
    intro hh
    have key := num_id S h5 h16
    simp only [s3] at hh
    simp only [Nat.cast_one, Nat.cast_ofNat] at hh
    rw [hh, zero_mul] at key
    exact h6255 key.symm

end

end CatalanCore.Arith.Hybrid
