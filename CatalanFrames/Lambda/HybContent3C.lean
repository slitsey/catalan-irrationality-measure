module

public import CatalanFrames.Lambda.HybContent3B
public import CatalanFrames.Lambda.HybContent2C
public import CatalanFrames.Lambda.HybDefSum3

@[expose] public section

/-!
# λ: the hybrid content bound with the deficits E, B, C5, C7 and GK

`lam_content_deficit3`: for every `ε > 0`, eventually in `r` there is a deficit family `δ` with
`DefHypT lamInst r ⌊r/8⌋ (Tfun3 r) δ` (`δ = m` on both clean classes and on the GK low band,
`δ = m - (p - r)` on `r < p < r + m`, `δ = L_p - m` on the C5 and C7 windows) and

  `log DhybT ≤ (Λ8 + ε) r² - [E1] - [E3] - (1/128 - ε) r² - (1/320 - ε) r² - (1/448 - ε) r²
      - m((1/72 - ε) r - 2 log r) - m((1/44 - ε) r - 2 log r)`,

`m = ⌊r/8⌋`, `Λ8 = 24994314577/6665218560`.  The total deficit is
`129/4480 + 59/4480 + 29/6336 = 0.046541 r²`, so the content constant drops from `3.7102296` to
`Λ₃ = 3.7034204`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-- The seven windows are pairwise disjoint, so the deficits add up to at most `δ`. -/
lemma defs_le_delta3 {r : ℕ} (hr : 16 ≤ r) {δ : ℕ → ℕ}
    (h1 : ∀ p, cleanE1 r p → δ p = r / 8) (h3 : ∀ p, cleanE3 r p → δ p = r / 8)
    (hB : ∀ p, WB r p → δ p = r / 8 - (p - r))
    (hC : ∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8)
    (h7 : ∀ p, WC7 r p → δ p = p + (3 * p + 1) / 4 - r - r / 8)
    (hG : ∀ p, LowClean r (r / 8) p → δ p = r / 8) (p : ℕ) :
    defE1 r p + defE3 r p + defB r p + defC5 r p + defC7 r p + defGK3 r p + defGK1 r p ≤ δ p := by
  classical
  by_cases hL : LowClean r (r / 8) p
  · obtain ⟨n1, n3, nB, nC, n7⟩ := lc_disj hr hL
    have hδ := hG p hL
    rcases hL with hL | hL
    · have hL3 : LC3 r p := hL
      have : ¬ LC1 r p := fun h => by
        obtain ⟨_, _, _, _, _⟩ := hL3; obtain ⟨_, _, _, _, _⟩ := h; omega
      simp [defE1, defE3, defB, defC5, defC7, defGK3, defGK1, cleanDef, n1, n3, nB, nC, n7, hL3,
        this, hδ]
    · have hL1 : LC1 r p := hL
      have : ¬ LC3 r p := fun h => by
        obtain ⟨_, _, _, _, _⟩ := hL1; obtain ⟨_, _, _, _, _⟩ := h; omega
      simp [defE1, defE3, defB, defC5, defC7, defGK3, defGK1, cleanDef, n1, n3, nB, nC, n7, hL1,
        this, hδ]
  · have g3 : ¬ LC3 r p := fun h => hL (Or.inl h)
    have g1 : ¬ LC1 r p := fun h => hL (Or.inr h)
    by_cases c7 : WC7 r p
    · obtain ⟨n1, n3, nB, nC, _⟩ := wc7_disj hr c7
      simp [defE1, defE3, defB, defC5, defC7, defGK3, defGK1, cleanDef, n1, n3, nB, nC, g3, g1,
        c7, h7 p c7]
    · have := defs_le_delta h1 h3 hB hC p
      simp [defC7, defGK3, defGK1, cleanDef, c7, g3, g1]
      exact this

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
  classical
  have h3 := class3_totalT3 (ε := ε / 4) (by positivity)
  have h1 := class1_totalT3 (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 2) (by positivity)
  have hE1 := lam_E1_deficit_sum hε
  have hE3 := lam_E3_deficit_sum hε
  have hBs := lam_B_deficit_sum hε
  have hCs := lam_C5_deficit_sum hε
  have h7s := lam_C7_deficit_sum hε
  have hG3 := lam_GK3_deficit_sum hε
  have hG1 := lam_GK1_deficit_sum hε
  filter_upwards [h3, h1, hx, hE1, hE3, hBs, hCs, h7s, hG3, hG1, eventually_ge_atTop 16] with r hr3
    hr1 hrx hD1 hD3 hDB hDC hD7 hDG3 hDG1 hr16
  intro δ hδ hδ1 hδ3 hδB hδC hδ7 hδG
  have hmain := lam_log_DhybT_le3 hr16 hδ
  have hex := hrx (r / 8) (Nat.div_le_self r 8)
  have hc := lam_const8
  have e : (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε / 4) +
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε / 4) =
      (r : ℝ) ^ 2 * (24994314577 / 6665218560 + ε / 2) := by
    rw [← mul_add]
    congr 1
    linarith
  have hlogp : ∀ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have key := defSum_ge (Finset.univ : Finset (Fin 7))
    ((Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime) δ
    (fun i => ![defE1 r, defE3 r, defB r, defC5 r, defC7 r, defGK3 r, defGK1 r] i)
    (fun i => ![((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r),
      ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r),
      (1 / 128 - ε) * (r : ℝ) ^ 2, (1 / 320 - ε) * (r : ℝ) ^ 2, (1 / 448 - ε) * (r : ℝ) ^ 2,
      ((r / 8 : ℕ) : ℝ) * (((1 / 72 : ℝ) - ε) * r - 2 * Real.log r),
      ((r / 8 : ℕ) : ℝ) * (((1 / 44 : ℝ) - ε) * r - 2 * Real.log r)] i)
    (fun p _ => by
      simpa [Fin.sum_univ_succ, add_assoc] using
        defs_le_delta3 hr16 hδ1 hδ3 hδB hδC hδ7 hδG p)
    (fun i _ => by
      fin_cases i
      · exact hD1
      · exact hD3
      · exact hDB
      · exact hDC
      · exact hD7
      · exact hDG3
      · exact hDG1)
    hlogp
  simp only [Fin.sum_univ_succ] at key
  simp at key
  nlinarith [hmain, hr3, hr1, hrx, e, hD1, hD3, key]

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
  obtain ⟨δ, hδ, hδ1, hδ3, hδB, hδC, hδ7, hδG⟩ := lam_defHypT_all3 hr16
  exact ⟨δ, hδ, hδ1, hδ3, hδB, hδC, hδ7, hδG, hg δ hδ hδ1 hδ3 hδB hδC hδ7 hδG⟩

end CatalanFrames.Lambda
