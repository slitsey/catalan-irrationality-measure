module

public import CatalanFrames.Lambda.HybInst
public import CatalanFrames.Lambda.DefB
public import CatalanFrames.HybCommon.Deficit7
public import CatalanFrames.HybCommon.TopSum

@[expose] public section

/-!
# λ: the hybrid content theorems, as instances of the generic `HybCommon` layer

Everything here is a one-line instance (offset `o = 1`) of the generic theorems, using
`lam_tropFacts : TropFacts lamInst 1` and `lam_badInfo : BadInfo lamInst` (`HybInst.lean`):

* `lam_content_trop8` is `logDhyb_le_G` (`Λ8 = 24994314577/6665218560 = 3.74996`);
* `lam_content_deficit3_gen` / `lam_content_deficit3` are `content_deficit7_G` with the seven window deficits
  (E both classes, B, C5, C7, GK);
* `lam_defBoth_all4` is `defBoth_all7`, `lam_both_eps4` is `both_eps_G7`, and `lam_mem2Content4` is
  `mem2Content_of_both_G`: the constant is `Λ₁ = 24729491161/6665218560 - 1/448 - 1/576 - 1/352 = 3.7034204…`.

The window predicates (`cleanE1`, `cleanE3`, `WB`, `WC5`, `WC7`), `Tfun3` and `DefBoth` are the generic
`cleanE1G 1`, ..., `TfunG 1 lamInst`, `DefBothG lamInst`; only `cleanE3` keeps the exceptional prime `139`
in its original form (`cleanE3_iff`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanFrames.HybCommon

namespace CatalanFrames.Lambda

/-- Clean primes of E, class `p ≡ 1 (4)`. -/
def cleanE1 (r p : ℕ) : Prop := cleanE1G 1 r p

/-- Clean primes of E, class `p ≡ 3 (4)` (the exceptional prime `139`, `6255 = 3² · 5 · 139`). -/
def cleanE3 (r p : ℕ) : Prop :=
  p.Prime ∧ p % 4 = 3 ∧ 5 * r + 8 ≤ 8 * p ∧ 5 * p + 5 ≤ 4 * r ∧ p ≠ 139

/-- Window of Theorem B. -/
def WB (r p : ℕ) : Prop := WBG r p

/-- The window of C5: `p ≡ 3 (4)`, `m ≤ L_p < 2m` with `L_p = (5p+1)/4 - r`, `p < r`. -/
def WC5 (r p : ℕ) : Prop := WC5G 1 r p

/-- The window of C7: `p ≡ 1 (4)`, `L_p = (7p+1)/4 - r ∈ [m, 2m)`. -/
def WC7 (r p : ℕ) : Prop := WC7G 1 r p

/-- The exponent bound of the glued deficit family. -/
noncomputable def Tfun3 (r p : ℕ) : ℕ := TfunG 1 lamInst r p

/-- Member-1 and member-2 deficit hypotheses together. -/
def DefBoth (r : ℕ) (T δ : ℕ → ℕ) : Prop := DefBothG lamInst r T δ

lemma cleanE3_iff {r p : ℕ} (hr : 16 ≤ r) : cleanE3 r p ↔ cleanE3G 1 r p := by
  constructor
  · rintro ⟨hp, h4, h8, h5, h139⟩
    exact ⟨hp, by omega, h8, h5, not_dvd_6255 hp (by omega) h139⟩
  · rintro ⟨hp, h4, h8, h5, hn⟩
    exact ⟨hp, by omega, h8, h5, fun h => hn (by rw [h]; norm_num)⟩

/-- **The λ hybrid content theorem (tropical), exact D1 truncated at `K = 8`.** -/
theorem lam_content_trop8 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, Real.log (Dhyb lamInst r (r / 8)) ≤
      (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 :=
  logDhyb_le_G lam_tropFacts lam_badInfo hε

/-- **The λ hybrid content theorem, simplified route.**  `Λ_trop' = 1579/420 ≈ 3.75952`. -/
theorem lam_content_trop {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, Real.log (Dhyb lamInst r (r / 8)) ≤ (1579 / 420 + ε) * (r : ℝ) ^ 2 := by
  filter_upwards [lam_content_trop8 hε] with r hr
  nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1579 / 420 - 24994314577 / 6665218560)
    (sq_nonneg (r : ℝ))]

/-- The content bound with the seven deficits, for *every* deficit family `δ` with the prescribed
values on the windows (generic in `δ`, so that the bordered family `DefBoth` can use it). -/
theorem lam_content_deficit3_gen {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT lamInst r (r / 8) (Tfun3 r) δ →
      (∀ p, cleanE1 r p → δ p = r / 8) → (∀ p, cleanE3 r p → δ p = r / 8) →
      (∀ p, WB r p → δ p = r / 8 - (p - r)) →
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) →
      (∀ p, WC7 r p → δ p = p + (3 * p + 1) / 4 - r - r / 8) →
      (∀ p, LowClean r (r / 8) p → δ p = r / 8) →
      Real.log (DhybT lamInst r (r / 8) (Tfun3 r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r) -
        (1 / 128 - ε) * (r : ℝ) ^ 2 - (1 / 320 - ε) * (r : ℝ) ^ 2 - (1 / 448 - ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 72 : ℝ) - ε) * r - 2 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((1 / 44 : ℝ) - ε) * r - 2 * Real.log r) := by
  filter_upwards [content_deficit7_G lam_tropFacts lam_badInfo hε, eventually_ge_atTop 16] with r h
    hr16 δ hδ h1 h3 hB h5 h7 hG
  exact h δ hδ h1 (fun p hp => h3 p ((cleanE3_iff hr16).2 hp)) hB h5 h7
    (fun p hp => hG p ((lowClean_iff r (r / 8) p).2 hp))

theorem lam_defBoth_all4 {r : ℕ} (hr : 16 ≤ r) :
    ∃ δ : ℕ → ℕ, DefBoth r (Tfun3 r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) ∧
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) ∧
      (∀ p, WC7 r p → δ p = p + (3 * p + 1) / 4 - r - r / 8) ∧
      (∀ p, LowClean r (r / 8) p → δ p = r / 8) :=
  ⟨dAll7 1 r, defBoth_all7 lamData (Or.inl rfl) hr,
    fun p h => dAll7_e1 (Or.inl rfl) hr h,
    fun p h => dAll7_e3 (Or.inl rfl) hr ((cleanE3_iff hr).1 h),
    fun p h => dAll7_b (Or.inl rfl) hr h, fun p h => dAll7_c5 (Or.inl rfl) hr h,
    fun p h => dAll7_c7 (Or.inl rfl) hr h,
    fun p h => dAll7_lc (Or.inl rfl) hr ((lowClean_iff r (r / 8) p).1 h)⟩

theorem lam_content_deficit3 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∃ δ : ℕ → ℕ, DefHypT lamInst r (r / 8) (Tfun3 r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) ∧
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) ∧
      (∀ p, WC7 r p → δ p = p + (3 * p + 1) / 4 - r - r / 8) ∧
      (∀ p, LowClean r (r / 8) p → δ p = r / 8) ∧
      Real.log (DhybT lamInst r (r / 8) (Tfun3 r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r) -
        (1 / 128 - ε) * (r : ℝ) ^ 2 - (1 / 320 - ε) * (r : ℝ) ^ 2 - (1 / 448 - ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 72 : ℝ) - ε) * r - 2 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((1 / 44 : ℝ) - ε) * r - 2 * Real.log r) := by
  filter_upwards [lam_content_deficit3_gen hε, eventually_ge_atTop 16] with r hg hr16
  obtain ⟨δ, hδ, hδ1, hδ3, hδB, hδC, hδ7, hδG⟩ := lam_defBoth_all4 hr16
  exact ⟨δ, hδ.1, hδ1, hδ3, hδB, hδC, hδ7, hδG,
    hg δ hδ.1 hδ1 hδ3 hδB hδC hδ7 hδG⟩

/-- The border cost is negligible for λ. -/
theorem lam_topC_sum {ε : ℝ} (hε : 0 < ε) : ∀ᶠ r : ℕ in Filter.atTop,
    ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      (topC lamInst r (r / 8) p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2 :=
  topC_sum_G lamInst lam_badInfo (fun r => r / 8) (fun r => Nat.div_le_self r 8) hε

end CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

open CatalanFrames.Lambda

/-- **Generic bordering step**: a content bound for a family that is simultaneously a
member-1 and member-2 deficit family (`DefBoth`) gives `Mem2Content`, because the border cost
is `O(r log r)` (`lam_topC_sum`).  Any later deficit family (e.g. with GK bordered) plugs in here. -/
theorem lam_mem2Content_of_both {Λ0 Λ : ℝ} (hΛ : Λ0 ≤ Λ)
    (h : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ0 + ε) * (r : ℝ) ^ 2) :
    Mem2Content lamFrame Λ :=
  mem2Content_of_both_G lamInst hΛ (fun ε hε => lam_topC_sum hε) h

/-- The `ε`-form of the content bound with deficits E, B, C5, C7 (no GK), constant
`Λ₂ = 24729491161/6665218560 - 1/448`. -/
theorem lam_both_eps3 {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 :=
  both_eps_G lamInst lamData (Or.inl rfl)
    (fun ε hε => logDhybT_le_G lam_tropFacts lam_badInfo hε) hΛ

/-- The `ε`-form of the member-1/member-2 content bound for the deficit family `B, E, C5`. -/
theorem lam_both_eps {Λ : ℝ} (hΛ : 24729491161 / 6665218560 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 :=
  lam_both_eps3 (by linarith [(by norm_num : (0 : ℝ) < 1 / 448)])

/-- **`Mem2Content` for λ** (bordering of the member-1 deficit families B, E, C5). -/
theorem lam_mem2Content {Λ : ℝ} (hΛ : 24729491161 / 6665218560 ≤ Λ) :
    Mem2Content lamFrame Λ :=
  lam_mem2Content_of_both le_rfl (lam_both_eps hΛ)

/-- **`Mem2Content` for λ** at `Λ₂ = 24729491161/6665218560 - 1/448 = 3.70799745…`
(deficits E, B, C5, C7 bordered; GK not bordered). -/
theorem lam_mem2Content3 {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 ≤ Λ) :
    Mem2Content lamFrame Λ :=
  lam_mem2Content_of_both le_rfl (lam_both_eps3 hΛ)

/-- The `ε`-form of the content bound with all seven bordered deficits, constant
`Λ₁ = 24729491161/6665218560 - 1/448 - 1/576 - 1/352 = 3.7034204…`. -/
theorem lam_both_eps4 {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 :=
  both_eps_G7 lamInst lamData (Or.inl rfl)
    (fun ε hε => logDhybT_le_G lam_tropFacts lam_badInfo hε) hΛ

/-- **`Mem2Content` for λ** at `Λ₁ = 3.7034204…` (deficits E, B, C5, C7, GK, all bordered). -/
theorem lam_mem2Content4 {Λ : ℝ}
    (hΛ : 24729491161 / 6665218560 - 1 / 448 - 1 / 576 - 1 / 352 ≤ Λ) :
    Mem2Content lamFrame Λ :=
  lam_mem2Content_of_both (Λ0 := Λ)
    le_rfl (lam_both_eps4 hΛ)

end CatalanFrames.LambdaHybrid
