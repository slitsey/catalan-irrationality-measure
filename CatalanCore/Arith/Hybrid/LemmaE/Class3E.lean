module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3D

@[expose] public section

/-!
# Lemma E, class 3: evaluation of the table on `Pt × Pt`, `Wt × Wt` and the borders
-/

open Finset

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

/-- `ρ_p + ρ_{k₂}` = `1 - 4/5`. -/
def s3 (p : ℕ) : ZMod p := 1 + (-(4 * (((5 : ℕ) : ZMod p))⁻¹))

variable (S : ESetup3 p r m k1)

lemma h16_ne (hp5 : 5 ≤ p) : (16 : ZMod p) ≠ 0 := by
  have : (16 : ZMod p) = 4 * 4 := by norm_num
  rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)

lemma singG_mid {a b : ℕ} (h1 : k1 ≤ a) (h2 : a < p) (h3 : p + k1 ≤ b) :
    singG (sd3 S) a b = s3 p := by
  have hk1 := S.hk1
  rw [singG_eval S]
  have e1 : ¬ (a < k1 ∧ k1 ≤ b) := by omega
  have e2 : a < p ∧ p ≤ b := by omega
  have e3 : a < p + k1 ∧ p + k1 ≤ b := by omega
  rw [if_neg e1, if_pos e2, if_pos e3, s3]
  ring

lemma singG_in {a b : ℕ} (h1 : k1 ≤ a) (h3 : b < p) : singG (sd3 S) a b = 0 := by
  have hk1 := S.hk1
  rw [singG_eval S]
  have e1 : ¬ (a < k1 ∧ k1 ≤ b) := by omega
  have e2 : ¬ (a < p ∧ p ≤ b) := by omega
  have e3 : ¬ (a < p + k1 ∧ p + k1 ≤ b) := by omega
  rw [if_neg e1, if_neg e2, if_neg e3]
  ring

lemma singG2_B1 {a : ℕ} (h1 : k1 ≤ a) (h2 : a < p) :
    singG2 (sd3 S) a = -(16 * ((((1 : ℕ) : ZMod p))⁻¹) ^ 2) := by
  have hk1 := S.hk1
  rw [singG2_eval S]
  have e2 : ¬ p ≤ a := by omega
  have e3 : ¬ p + k1 ≤ a := by omega
  rw [if_pos h1, if_neg e2, if_neg e3]
  ring

end

end CatalanCore.Arith.Hybrid
