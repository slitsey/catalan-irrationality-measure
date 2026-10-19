module

public import CatalanFrames.Lambda.HybTopAll3
public import CatalanFrames.Lambda.HybContent3C
public import CatalanCore.Arith.Hybrid.DefGKBorder

@[expose] public section

/-!
# λ: the bordered deficit family with all seven windows (GK bordered)

`lam_defBoth_all4`: `E (both classes) + B + C5 + C7 + GK` as a single `DefBoth` family for `Tfun3`
(the GK part is `defHypTop_GK`, the bordered T-route of `DefGKBorder`).
`lam_both_eps4`: the `ε`-form of the content bound with all seven deficits, for every
`Λ ≥ Λ₁ = 24729491161/6665218560 - 1/448 - 1/576 - 1/352 = 3.7034204…`; with
`lam_content_deficit3_gen` (the content bound for every `δ` with the window values) and the
real-number tail `lam_num7`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Rect

namespace CatalanFrames.Lambda

theorem lam_defBoth_all4 {r : ℕ} (hr : 16 ≤ r) :
    ∃ δ : ℕ → ℕ, DefBoth r (Tfun3 r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) ∧
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) ∧
      (∀ p, WC7 r p → δ p = p + (3 * p + 1) / 4 - r - r / 8) ∧
      (∀ p, LowClean r (r / 8) p → δ p = r / 8) := by
  classical
  obtain ⟨δ0, h0, h1, h3, hB, hC5, hC7⟩ := lam_defBoth_all3 hr
  have hTr : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ Tfun3 r p :=
    fun p _ _ => le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hTd : ∀ p : ℕ, p.Prime → LowClean r (r / 8) p → 2 * r + r / 8 ≤ Tfun3 r p := fun p _ hW => by
    refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
    simp only [eGK, if_pos hW]
    omega
  have hGK : DefBoth r (Tfun3 r) (fun p => if LowClean r (r / 8) p then r / 8 else 0) :=
    ⟨defHypT_GK lamInst lamData r (r / 8) (by omega) (Tfun3 r) hTr hTd,
     defHypTop_GK lamInst lamData r (r / 8) (by omega) (Tfun3 r) hTr hTd⟩
  have hAll := h0.glue (fun p => LowClean r (r / 8) p) hGK
  refine ⟨_, hAll, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hc
    have nl : ¬ LowClean r (r / 8) p := fun h => (lc_disj hr h).1 hc
    simp only [if_neg nl]; exact h1 p hc
  · intro p hc
    have nl : ¬ LowClean r (r / 8) p := fun h => (lc_disj hr h).2.1 hc
    simp only [if_neg nl]; exact h3 p hc
  · intro p hc
    have nl : ¬ LowClean r (r / 8) p := fun h => (lc_disj hr h).2.2.1 hc
    simp only [if_neg nl]; exact hB p hc
  · intro p hc
    have nl : ¬ LowClean r (r / 8) p := fun h => (lc_disj hr h).2.2.2.1 hc
    simp only [if_neg nl]; exact hC5 p hc
  · intro p hc
    have nl : ¬ LowClean r (r / 8) p := (wc7_disj hr hc).2.2.2.2
    simp only [if_neg nl]; exact hC7 p hc
  · intro p hc
    simp only [if_pos hc]

end CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

/-- The arithmetic of the clean-up of the `m`-dependent and `log r` terms for the seven deficits
(E, B, C5, C7, GK): constant `Λ₁ = 24729491161/6665218560 - 1/448 - 1/576 - 1/352`. -/
theorem lam_num7 {Λ ε r L m lg : ℝ}
    (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 100) (hr : 3 ≤ ε * r) (hL0 : 0 ≤ L) (hL : L ≤ ε / 10 * r)
    (hm : r / 8 - 1 ≤ m)
    (hmain : lg ≤ (24994314577 / 6665218560 + ε / 10) * r ^ 2
      - m * ((1 / 7 - ε / 10) * r - 4 * L) - m * ((7 / 80 - ε / 10) * r - 6 * L)
      - (1 / 128 - ε / 10) * r ^ 2 - (1 / 320 - ε / 10) * r ^ 2 - (1 / 448 - ε / 10) * r ^ 2
      - m * ((1 / 72 - ε / 10) * r - 2 * L) - m * ((1 / 44 - ε / 10) * r - 2 * L)) :
    lg ≤ (Λ + ε) * r ^ 2 := by
  have hr0 : 0 ≤ r := by
    by_contra h
    push Not at h
    nlinarith
  have hX1 : 0 ≤ (1 / 7 - ε / 10) * r - 4 * L := by nlinarith
  have hX2 : 0 ≤ (7 / 80 - ε / 10) * r - 6 * L := by nlinarith
  have hX3 : 0 ≤ (1 / 72 - ε / 10) * r - 2 * L := by nlinarith
  have hX4 : 0 ≤ (1 / 44 - ε / 10) * r - 2 * L := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hm hX1
  have h2 := mul_le_mul_of_nonneg_right hm hX2
  have h3 := mul_le_mul_of_nonneg_right hm hX3
  have h4 := mul_le_mul_of_nonneg_right hm hX4
  have hrL : r * L ≤ ε / 10 * r ^ 2 := by nlinarith
  have hrr : 0 ≤ r ^ 2 := sq_nonneg r
  have hlin : r ≤ ε / 3 * r ^ 2 := by nlinarith
  nlinarith

end CatalanFrames.LambdaHybrid

namespace CatalanFrames.LambdaHybrid

open CatalanFrames.Lambda

/-- The `ε`-form of the content bound with all seven bordered deficits, constant
`Λ₁ = 24729491161/6665218560 - 1/448 - 1/576 - 1/352 = 3.7034204…`. -/
theorem lam_both_eps4 {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  set ε₁ : ℝ := min (ε / 2) (1 / 100) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (by norm_num)
  have hε₁1 : ε₁ ≤ 1 / 100 := min_le_right _ _
  have hε₁2 : ε₁ ≤ ε / 2 := min_le_left _ _
  have hd := lam_content_deficit3_gen (ε := ε₁ / 10) (by positivity)
  have hl := eventually_log_le (e := ε₁ / 10) (by positivity)
  have hbig : ∀ᶠ r : ℕ in atTop, 3 ≤ ε₁ * r := by
    have : Tendsto (fun r : ℕ => ε₁ * (r : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hε₁0
    exact this.eventually_ge_atTop 3
  filter_upwards [hd, hl, hbig, eventually_ge_atTop 16] with r hdr hL hb hr16
  obtain ⟨δ, hδ, hδ1, hδ3, hδB, hδC, hδ7, hδG⟩ := lam_defBoth_all4 hr16
  refine ⟨Tfun3 r, δ, hδ, ?_⟩
  have hlog := hdr δ hδ.1 hδ1 hδ3 hδB hδC hδ7 hδG
  have hm : (r : ℝ) / 8 - 1 ≤ ((r / 8 : ℕ) : ℝ) := by
    have : (r : ℝ) < 8 * ((r / 8 : ℕ) : ℝ) + 8 := by
      exact_mod_cast (by omega : r < 8 * (r / 8) + 8)
    linarith
  have hL0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have key := lam_num7 (Λ := Λ) (ε := ε₁) (r := (r : ℝ)) (L := Real.log r)
    (m := ((r / 8 : ℕ) : ℝ)) (lg := Real.log (DhybT lamInst r (r / 8) (Tfun3 r) δ))
    hΛ hε₁0 hε₁1 hb hL0 hL hm hlog
  have hr2 : 0 ≤ (r : ℝ) ^ 2 := sq_nonneg _
  nlinarith [key]

/-- **`Mem2Content` for λ** at `Λ₁ = 3.7034204…` (deficits E, B, C5, C7, GK, all bordered). -/
theorem lam_mem2Content4 {Λ : ℝ}
    (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    Mem2Content lamFrame Λ :=
  lam_mem2Content_of_both (Λ0 := Λ)
    le_rfl (lam_both_eps4 hΛ)

end CatalanFrames.LambdaHybrid
