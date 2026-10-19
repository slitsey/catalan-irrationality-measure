module

public import CatalanFrames.HybCommon.Final
public import CatalanFrames.HybCommon.LogDhybT

@[expose] public section

/-!
# The content bound for every deficit family with the prescribed window values (generic)

`dAll7 o r` is the sum of the seven window deficits; on each window it has the prescribed value
(`dAll7_e1`, ..., `dAll7_lc`) and it vanishes elsewhere, so `dAll7 ≤ δ` for every deficit family `δ` with
those values on the windows (`dAll7_le`).  `content_deficit7_G` combines `logDhybT_le_G` with the seven
deficit sums: for every such `δ`, `log DhybT ≤ (Λ8 + ε) r² - (seven explicit terms)`.
`logDhyb_le_G` is the plain tropical bound `log Dhyb ≤ (Λ8 + ε) r²` (`δ = 0`).
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- **The tropical bound for `Dhyb`**: `log Dhyb ≤ (Λ8 + ε) r²`. -/
theorem logDhyb_le_G {I : HybInst Fr} [∀ r, I.DiagOK r (r / 8)] {o : ℕ} (T : TropFacts I o) {Lc cm : ℕ} (B : BadInfo I Lc cm) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ r : ℕ in atTop,
    Real.log (Dhyb I r (r / 8)) ≤ (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 := by
  filter_upwards [logDhybT_le_G T B hε] with r hr
  have h0 : DefHypT I r (r / 8) (TfunG o I r) (fun _ => 0) :=
    (defHyp_zero (I := I) (r := r) (m := r / 8)).toT.mono_T (fun p _ _ => TfunG_ge_trop p)
  have h := hr _ h0
  rw [log_DhybT I r (r / 8) h0] at h
  rw [log_Dhyb]
  have hs : ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
      (tropExp I r (r / 8) p : ℝ) * Real.log p ≤
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (TfunG o I r p : ℝ) * Real.log p :=
    Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right
      (by exact_mod_cast TfunG_ge_trop p)
      (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
  simp only [Nat.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero] at h
  linarith

section Values

variable {o r p : ℕ}

lemma dAll7_lc (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : LowCleanO o r (r / 8) p) :
    dAll7 o r p = r / 8 := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := disj_lc ho hr h
  rw [dAll7, ← dGK_eq ho p, if_pos h]
  simp [dAll5, dE1, dE3, dB, dC5, dC7, n1, n2, n3, n4, n5]

lemma dAll7_c7 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WC7G o r p) :
    dAll7 o r p = p + (3 * p + o) / 4 - r - r / 8 := by
  have nl : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.2.2.2 h
  obtain ⟨n1, n2, n3, n4⟩ := disj_c7 ho hr h
  rw [dAll7, ← dGK_eq ho p, if_neg nl]
  simp [dAll5, dE1, dE3, dB, dC5, dC7, n1, n2, n3, n4, h]

lemma dAll7_c5 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WC5G o r p) :
    dAll7 o r p = p + (p + o) / 4 - r - r / 8 := by
  have nl : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.2.2.1 h
  have n7 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).2.2.2 h
  obtain ⟨n1, n2, n3⟩ := disj_c5 ho hr h
  rw [dAll7, ← dGK_eq ho p, if_neg nl]
  simp [dAll5, dE1, dE3, dB, dC5, dC7, n1, n2, n3, n7, h]

lemma dAll7_b (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WBG r p) :
    dAll7 o r p = r / 8 - (p - r) := by
  have nl : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.2.1 h
  have n7 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).2.2.1 h
  have n5 : ¬ WC5G o r p := fun c => (disj_c5 ho hr c).2.2 h
  obtain ⟨n1, n2⟩ := disj_b ho hr h
  rw [dAll7, ← dGK_eq ho p, if_neg nl]
  simp [dAll5, dE1, dE3, dB, dC5, dC7, n1, n2, n5, n7, h]

lemma dAll7_e3 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : cleanE3G o r p) :
    dAll7 o r p = r / 8 := by
  have nl : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.1 h
  have n7 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).2.1 h
  have n5 : ¬ WC5G o r p := fun c => (disj_c5 ho hr c).2.1 h
  have nb : ¬ WBG r p := fun c => (disj_b ho hr c).2 h
  have n1 := disj_e3 ho hr h
  rw [dAll7, ← dGK_eq ho p, if_neg nl]
  simp [dAll5, dE1, dE3, dB, dC5, dC7, n1, nb, n5, n7, h]

lemma dAll7_e1 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : cleanE1G o r p) :
    dAll7 o r p = r / 8 := by
  have nl : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).1 h
  have n7 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).1 h
  have n5 : ¬ WC5G o r p := fun c => (disj_c5 ho hr c).1 h
  have nb : ¬ WBG r p := fun c => (disj_b ho hr c).1 h
  have n3 : ¬ cleanE3G o r p := fun c => disj_e3 ho hr c h
  rw [dAll7, ← dGK_eq ho p, if_neg nl]
  simp [dAll5, dE1, dE3, dB, dC5, dC7, n3, nb, n5, n7, h]

/-- Outside the seven windows `dAll7` vanishes. -/
lemma dAll7_zero (ho : o = 1 ∨ o = 3) (hl : ¬ LowCleanO o r (r / 8) p)
    (h7 : ¬ WC7G o r p) (h5 : ¬ WC5G o r p) (hb : ¬ WBG r p) (h3 : ¬ cleanE3G o r p)
    (h1 : ¬ cleanE1G o r p) : dAll7 o r p = 0 := by
  rw [dAll7, ← dGK_eq ho p, if_neg hl]
  simp [dAll5, dE1, dE3, dB, dC5, dC7, h1, h3, hb, h5, h7]

/-- `dAll7` is below every deficit family with the prescribed values on the seven windows. -/
lemma dAll7_le (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) {δ : ℕ → ℕ}
    (h1 : ∀ p, cleanE1G o r p → δ p = r / 8) (h3 : ∀ p, cleanE3G o r p → δ p = r / 8)
    (hB : ∀ p, WBG r p → δ p = r / 8 - (p - r))
    (h5 : ∀ p, WC5G o r p → δ p = p + (p + o) / 4 - r - r / 8)
    (h7 : ∀ p, WC7G o r p → δ p = p + (3 * p + o) / 4 - r - r / 8)
    (hG : ∀ p, LowCleanO o r (r / 8) p → δ p = r / 8) (p : ℕ) : dAll7 o r p ≤ δ p := by
  by_cases l : LowCleanO o r (r / 8) p
  · rw [dAll7_lc ho hr l, hG p l]
  by_cases c7 : WC7G o r p
  · rw [dAll7_c7 ho hr c7, h7 p c7]
  by_cases c5 : WC5G o r p
  · rw [dAll7_c5 ho hr c5, h5 p c5]
  by_cases b : WBG r p
  · rw [dAll7_b ho hr b, hB p b]
  by_cases e3 : cleanE3G o r p
  · rw [dAll7_e3 ho hr e3, h3 p e3]
  by_cases e1 : cleanE1G o r p
  · rw [dAll7_e1 ho hr e1, h1 p e1]
  rw [dAll7_zero ho l c7 c5 b e3 e1]
  exact Nat.zero_le _

end Values

/-- **The content bound with the seven deficits, for every `δ` with the prescribed window values.** -/
theorem content_deficit7_G {I : HybInst Fr} [∀ r, I.DiagOK r (r / 8)] {o : ℕ} (T : TropFacts I o) {Lc cm : ℕ} (B : BadInfo I Lc cm) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT I r (r / 8) (TfunG o I r) δ →
      (∀ p, cleanE1G o r p → δ p = r / 8) → (∀ p, cleanE3G o r p → δ p = r / 8) →
      (∀ p, WBG r p → δ p = r / 8 - (p - r)) →
      (∀ p, WC5G o r p → δ p = p + (p + o) / 4 - r - r / 8) →
      (∀ p, WC7G o r p → δ p = p + (3 * p + o) / 4 - r - r / 8) →
      (∀ p, LowCleanO o r (r / 8) p → δ p = r / 8) →
      Real.log (DhybT I r (r / 8) (TfunG o I r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r) -
        (1 / 128 - ε) * (r : ℝ) ^ 2 - (1 / 320 - ε) * (r : ℝ) ^ 2 - (1 / 448 - ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 72 : ℝ) - ε) * r - 2 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((1 / 44 : ℝ) - ε) * r - 2 * Real.log r) := by
  have ho := T.ho
  have hd := logDhybT_le_G T B hε
  have s1 := sum_E1 I ho hε
  have s3 := sum_E3 I ho hε
  have sB := sum_B I hε
  have s5 := sum_C5 I ho hε
  have s7 := sum_C7 I ho hε
  have sa := sum_GKa I ho hε
  have sb := sum_GKb I ho hε
  filter_upwards [hd, s1, s3, sB, s5, s7, sa, sb, eventually_ge_atTop 16] with r hdr t1 t3 tB t5 t7
    ta tb hr16 δ hδ hδ1 hδ3 hδB hδ5 hδ7 hδG
  have hlog := hdr δ hδ
  have hle : ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
      (dAll7 o r p : ℝ) * Real.log p ≤
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p :=
    Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right
      (by exact_mod_cast dAll7_le ho hr16 hδ1 hδ3 hδB hδ5 hδ7 hδG p)
      (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
  have hsum : ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
      (dAll7 o r p : ℝ) * Real.log p =
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dE1 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dE3 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dB r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dC5 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dC7 o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dGKa o r p : ℝ) * Real.log p +
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dGKb o r p : ℝ) * Real.log p := by
    simp only [dAll7, dAll5, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    ring
  rw [hsum] at hle
  linarith

end CatalanFrames.HybCommon
