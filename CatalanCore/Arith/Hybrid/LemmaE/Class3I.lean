module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3H

@[expose] public section

/-!
# Lemma E, class 3: `Wt × Wt`, `Pt × Wt`, zone and border entries of the table
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

variable (S : ESetup3 p r m k1)

include S

lemma cast_sub_p {a : ℕ} (h : p ≤ a) : ((a - p : ℕ) : ZMod p) = (a : ZMod p) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, sub_zero]

lemma singG_zero_big {a b : ℕ} (h : p + k1 ≤ a) : singG (sd3 S) a b = 0 := by
  have hk1 := S.hk1
  rw [singG_eval S]
  have e1 : ¬ (a < k1 ∧ k1 ≤ b) := by omega
  have e2 : ¬ (a < p ∧ p ≤ b) := by omega
  have e3 : ¬ (a < p + k1 ∧ p + k1 ≤ b) := by omega
  rw [if_neg e1, if_neg e2, if_neg e3]
  ring

lemma TE3_WW {a b : ℕ} (ha : a < r) (haC : isCz p r m a) (hb : b < r) (hbC : isCz p r m b) :
    TEw3 p r m (sd3 S) a b = if b = a then 1 else 0 := by
  have := S.hpr; have := S.hk2r; have := S.hk1; have := S.hN
  have hw : wr p r m a + wc p r m b = 2 := by
    unfold wr wc; rw [if_pos ha, if_pos hb, if_pos haC, if_pos hbC]
  by_cases hab : b = a
  · subst hab
    rw [if_pos rfl, TEw3_eq, hw, TEdG_two]
    have := dZ_B1 S (a := b) (by unfold isCz at haC; omega) (by unfold isCz at haC; omega)
    exact this
  · rw [if_neg hab]
    rcases lt_or_gt_of_ne hab with h | h
    · rw [TEw3_gt _ h, hw, TEoG_two, if_neg]
      unfold isCz at haC hbC; omega
    · rw [TEw3_lt _ h, hw, TEoG_two, if_neg]
      unfold isCz at haC hbC; omega

lemma TE3_PW {a b : ℕ} (ha : a < r) (haP : ¬ isCz p r m a) (hb : b < r) (hbC : isCz p r m b) :
    TEw3 p r m (sd3 S) a b = 0 := by
  have hw : wr p r m a + wc p r m b = 3 := by
    unfold wr wc; rw [if_pos ha, if_pos hb, if_neg haP, if_pos hbC]
  have hab : a ≠ b := fun h => haP (h ▸ hbC)
  rcases lt_or_gt_of_ne hab with h | h
  · rw [TEw3_lt _ h, hw]; exact TEoG_big _ (le_refl 3) _ _
  · rw [TEw3_gt _ h, hw]; exact TEoG_big _ (le_refl 3) _ _

lemma TE3_ZZ {x y : ℕ} (hx : r ≤ x) (hy : r ≤ y) (hne : x ≠ y) (hd : x - y ≠ p) (hd' : y - x ≠ p) :
    TEw3 p r m (sd3 S) x y = 0 := by
  have := S.hpr; have := S.hk2r; have := S.hk1; have := S.hN
  have hw : wr p r m x + wc p r m y = 1 := by
    rw [wr_zone hx, wc_zone hy]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [TEw3_lt _ h, hw, TEoG_one _ hd', singG_zero_big S (by omega)]; simp
  · rw [TEw3_gt _ h, hw, TEoG_one _ hd, singG_zero_big S (by omega)]; simp

/-- `Pt × zone-column`. -/
lemma TE3_PY {c y : ℕ} (hc : c < r) (hcP : ¬ isCz p r m c) (hy : r ≤ y) :
    TEw3 p r m (sd3 S) c y = if y - c = p then (16 : ZMod p)⁻¹ * singG (sd3 S) c y else 0 := by
  have hw : wr p r m c + wc p r m y = 2 := by
    unfold wr; rw [if_pos hc, if_neg hcP, wc_zone hy]
  rw [TEw3_lt _ (by omega), hw, TEoG_two]

/-- `Wt × zone-column`. -/
lemma TE3_WY {w y : ℕ} (hw0 : w < r) (hwC : isCz p r m w) (hy : r ≤ y) (hd : y - w ≠ p) :
    TEw3 p r m (sd3 S) w y = (16 * ((y : ZMod p) - w))⁻¹ * singG (sd3 S) w y := by
  have hw : wr p r m w + wc p r m y = 1 := by
    unfold wr; rw [if_pos hw0, if_pos hwC, wc_zone hy]
  rw [TEw3_lt _ (by omega), hw, TEoG_one _ hd]

/-- zone-row `× Pt`. -/
lemma TE3_XP {z c : ℕ} (hz : r ≤ z) (hc : c < r) (hcP : ¬ isCz p r m c) (hd : z - c ≠ p) :
    TEw3 p r m (sd3 S) z c = (16 * ((z : ZMod p) - c))⁻¹ * singG (sd3 S) c z := by
  have hw : wr p r m z + wc p r m c = 1 := by
    unfold wc; rw [wr_zone hz, if_pos hc, if_neg hcP]
  rw [TEw3_gt _ (by omega), hw, TEoG_one _ hd]

/-- zone-row `× Wt`. -/
lemma TE3_XW {z w : ℕ} (hz : r ≤ z) (hw0 : w < r) (hwC : isCz p r m w) :
    TEw3 p r m (sd3 S) z w =
      if z - w = p then (16 : ZMod p)⁻¹ * singG (sd3 S) w z else 0 := by
  have hw : wr p r m z + wc p r m w = 2 := by
    unfold wc; rw [wr_zone hz, if_pos hw0, if_pos hwC]
  rw [TEw3_gt _ (by omega), hw, TEoG_two]

end

end CatalanCore.Arith.Hybrid
