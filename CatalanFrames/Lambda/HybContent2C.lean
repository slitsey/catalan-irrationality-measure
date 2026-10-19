module

public import CatalanFrames.Lambda.HybContent2B

@[expose] public section

/-!
# λ: the hybrid content bound with the deficits E, B and C5

`lam_content_deficit2`: for every `ε > 0`, eventually in `r` there is a deficit family `δ` with
`DefHypT lamInst r ⌊r/8⌋ (Tfun2 r) δ` (`δ = m` on both clean classes, `δ = m - (p - r)` on
`r < p < r + m`, `δ = L_p - m` on the C5 window) and

  `log DhybT ≤ (Λ8 + ε) r² - m((1/7 - ε) r - 4 log r) - m((7/80 - ε) r - 6 log r)
      - (1/128 - ε) r² - (1/320 - ε) r²`,

`m = ⌊r/8⌋`, `Λ8 = 24994314577/6665218560`.  The total deficit is
`129/4480 + 1/128 + 1/320 = 89/2240 = 0.03973 r²`.  The four summands are combined with the generic
`defSum_ge`; the C7 and GK deficits add as two more summands (see `DEFSUM/status.md`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-- The four windows are pairwise disjoint, so the deficits add up to at most `δ`. -/
lemma defs_le_delta {r : ℕ} {δ : ℕ → ℕ}
    (h1 : ∀ p, cleanE1 r p → δ p = r / 8) (h3 : ∀ p, cleanE3 r p → δ p = r / 8)
    (hB : ∀ p, WB r p → δ p = r / 8 - (p - r))
    (hC : ∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) (p : ℕ) :
    defE1 r p + defE3 r p + defB r p + defC5 r p ≤ δ p := by
  classical
  by_cases c1 : cleanE1 r p
  · have n3 : ¬ cleanE3 r p := fun h => by have := c1.2.1; have := h.2.1; omega
    have nB : ¬ WB r p := fun h => by have := c1.2.2.2; have := h.2.1; omega
    have nC : ¬ WC5 r p := fun h => by have := c1.2.1; have := h.2.1; omega
    simp [defE1, defE3, defB, defC5, c1, n3, nB, nC, h1 p c1]
  · by_cases c3 : cleanE3 r p
    · have nB : ¬ WB r p := fun h => by
        have := c3.2.2.2.1; have := h.2.1; omega
      have nC : ¬ WC5 r p := fun h => by
        have := c3.2.2.2.1; obtain ⟨_, _, _, _, _⟩ := h; omega
      simp [defE1, defE3, defB, defC5, c1, c3, nB, nC, h3 p c3]
    · by_cases cB : WB r p
      · have nC : ¬ WC5 r p := fun h => by have := cB.2.1; have := h.2.2.2.2; omega
        simp [defE1, defE3, defB, defC5, c1, c3, cB, nC, hB p cB]
      · by_cases cC : WC5 r p
        · simp [defE1, defE3, defB, defC5, c1, c3, cB, cC, hC p cC]
        · simp [defE1, defE3, defB, defC5, c1, c3, cB, cC]

theorem lam_content_deficit2 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∃ δ : ℕ → ℕ, DefHypT lamInst r (r / 8) (Tfun2 r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) ∧
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) ∧
      Real.log (DhybT lamInst r (r / 8) (Tfun2 r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r) -
        (1 / 128 - ε) * (r : ℝ) ^ 2 - (1 / 320 - ε) * (r : ℝ) ^ 2 := by
  classical
  have h3 := class3_totalT2 (ε := ε / 4) (by positivity)
  have h1 := class1_totalT2 (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 2) (by positivity)
  have hE1 := lam_E1_deficit_sum hε
  have hE3 := lam_E3_deficit_sum hε
  have hBs := lam_B_deficit_sum hε
  have hCs := lam_C5_deficit_sum hε
  filter_upwards [h3, h1, hx, hE1, hE3, hBs, hCs, eventually_ge_atTop 16] with r hr3 hr1 hrx hD1 hD3
    hDB hDC hr16
  obtain ⟨δ, hδ, hδ1, hδ3, hδB, hδC⟩ := lam_defHypT_all2 hr16
  refine ⟨δ, hδ, hδ1, hδ3, hδB, hδC, ?_⟩
  have hmain := lam_log_DhybT_le2 hr16 hδ
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
  have key := defSum_ge (Finset.univ : Finset (Fin 4))
    ((Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime) δ
    (fun i => ![defE1 r, defE3 r, defB r, defC5 r] i)
    (fun i => ![((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r),
      ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r),
      (1 / 128 - ε) * (r : ℝ) ^ 2, (1 / 320 - ε) * (r : ℝ) ^ 2] i)
    (fun p _ => by
      simpa [Fin.sum_univ_four] using defs_le_delta hδ1 hδ3 hδB hδC p)
    (fun i _ => by
      fin_cases i
      · exact hD1
      · exact hD3
      · exact hDB
      · exact hDC)
    hlogp
  simp only [Fin.sum_univ_four] at key
  simp at key
  nlinarith [hmain, hr3, hr1, hrx, e, hD1, hD3, key]

end CatalanFrames.Lambda
