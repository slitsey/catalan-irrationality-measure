module

public import CatalanFrames.Lambda.HybTopAll
public import CatalanFrames.Lambda.HybContent3C
public import CatalanCore.Arith.Hybrid.BorderC7

@[expose] public section

/-!
# λ: the bordered deficit family with C7, no GK (LAMFINAL)

`lam_defBoth_all3`: `E (both classes) + B + C5 + C7` as a single `DefBoth` family for
`T = Tfun3` (the `eGK` term only enlarges `T`; no GK deficit is used).
`lam_content_deficit3n`: the content bound with these five deficits, constant
`Λ₂ = 24729491161/6665218560 - 1/448 = 3.7079974…` (= `Λ₃ + 29/6336`, GK missing).
`lam_both_eps3`: the `ε`-form; `lam_mem2Content3`: `Mem2Content` at `Λ₂`.
When a GK bordering result exists only `lam_both_eps3` needs to be replaced (by `Λ₃`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Rect

namespace CatalanFrames.Lambda

theorem lam_defBoth_all3 {r : ℕ} (hr : 16 ≤ r) :
    ∃ δ : ℕ → ℕ, DefBoth r (Tfun3 r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) ∧
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) ∧
      (∀ p, WC7 r p → δ p = p + (3 * p + 1) / 4 - r - r / 8) := by
  classical
  obtain ⟨δ0, h0, h1, h3, hB, hC5⟩ := lam_defBoth_all2 hr
  have hT0 : ∀ p, Tfun2 r p ≤ Tfun3 r p := fun p => le_max_left _ _
  have h0' : DefBoth r (Tfun3 r) δ0 := h0.mono_T fun p _ _ => hT0 p
  have hTr : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ Tfun3 r p :=
    fun p _ _ => le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (hT0 p))
  have hd : ∀ p : ℕ, p.Prime → WC7 r p → ∀ k, CSetup7 p r (r / 8) k →
      ∑ a, wC7 p r k (Frame.hybRow r (r / 8) a) + ∑ b, wC7 p r k (Frame.hybCol r (r / 8) b)
        ≤ Tfun3 r p := fun p hp hW k S => by
    have hk : k = (3 * p + 1) / 4 := by have := S.hk; omega
    rw [wC7_dual_eq S]
    refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
    simp only [eC7, if_pos hW, hk]
    omega
  have hC7 : DefBoth r (Tfun3 r) (fun p => if WC7 r p then p + (3 * p + 1) / 4 - r - r / 8 else 0) :=
    ⟨defHypT_C7 lamInst lamData r (r / 8) (Tfun3 r) (WC7 r)
      (fun p _ hW => ⟨_, csetup7_of_wc7 hr hW⟩) hTr hd,
     defHypTop_C7 lamInst lamData r (r / 8) (Tfun3 r) (WC7 r)
      (fun p _ hW => ⟨_, csetup7_of_wc7 hr hW⟩) hTr hd⟩
  refine ⟨_, h0'.glue (WC7 r) hC7, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hc
    have n7 : ¬ WC7 r p := fun h => (wc7_disj hr h).1 hc
    simp only [if_neg n7]; exact h1 p hc
  · intro p hc
    have n7 : ¬ WC7 r p := fun h => (wc7_disj hr h).2.1 hc
    simp only [if_neg n7]; exact h3 p hc
  · intro p hc
    have n7 : ¬ WC7 r p := fun h => (wc7_disj hr h).2.2.1 hc
    simp only [if_neg n7]; exact hB p hc
  · intro p hc
    have n7 : ¬ WC7 r p := fun h => (wc7_disj hr h).2.2.2.1 hc
    simp only [if_neg n7]; exact hC5 p hc
  · intro p hc
    simp only [if_pos hc]

/-- The five windows E1, E3, B, C5, C7 are pairwise disjoint, so the deficits add up to `δ`. -/
lemma defs_le_delta3n {r : ℕ} (hr : 16 ≤ r) {δ : ℕ → ℕ}
    (h1 : ∀ p, cleanE1 r p → δ p = r / 8) (h3 : ∀ p, cleanE3 r p → δ p = r / 8)
    (hB : ∀ p, WB r p → δ p = r / 8 - (p - r))
    (hC : ∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8)
    (h7 : ∀ p, WC7 r p → δ p = p + (3 * p + 1) / 4 - r - r / 8) (p : ℕ) :
    defE1 r p + defE3 r p + defB r p + defC5 r p + defC7 r p ≤ δ p := by
  classical
  by_cases c7 : WC7 r p
  · obtain ⟨n1, n3, nB, nC, _⟩ := wc7_disj hr c7
    simp [defE1, defE3, defB, defC5, defC7, cleanDef, n1, n3, nB, nC, c7, h7 p c7]
  · have := defs_le_delta h1 h3 hB hC p
    simp [defC7, c7]
    exact this

theorem lam_content_deficit3n {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT lamInst r (r / 8) (Tfun3 r) δ →
      (∀ p, cleanE1 r p → δ p = r / 8) → (∀ p, cleanE3 r p → δ p = r / 8) →
      (∀ p, WB r p → δ p = r / 8 - (p - r)) →
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) →
      (∀ p, WC7 r p → δ p = p + (3 * p + 1) / 4 - r - r / 8) →
      Real.log (DhybT lamInst r (r / 8) (Tfun3 r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r) -
        (1 / 128 - ε) * (r : ℝ) ^ 2 - (1 / 320 - ε) * (r : ℝ) ^ 2 -
        (1 / 448 - ε) * (r : ℝ) ^ 2 := by
  classical
  have h3 := class3_totalT3 (ε := ε / 4) (by positivity)
  have h1 := class1_totalT3 (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 2) (by positivity)
  have hE1 := lam_E1_deficit_sum hε
  have hE3 := lam_E3_deficit_sum hε
  have hBs := lam_B_deficit_sum hε
  have hCs := lam_C5_deficit_sum hε
  have h7s := lam_C7_deficit_sum hε
  filter_upwards [h3, h1, hx, hE1, hE3, hBs, hCs, h7s, eventually_ge_atTop 16] with r hr3
    hr1 hrx hD1 hD3 hDB hDC hD7 hr16
  intro δ hδ hδ1 hδ3 hδB hδC hδ7
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
  have key := defSum_ge (Finset.univ : Finset (Fin 5))
    ((Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime) δ
    (fun i => ![defE1 r, defE3 r, defB r, defC5 r, defC7 r] i)
    (fun i => ![((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r),
      ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r),
      (1 / 128 - ε) * (r : ℝ) ^ 2, (1 / 320 - ε) * (r : ℝ) ^ 2, (1 / 448 - ε) * (r : ℝ) ^ 2] i)
    (fun p _ => by
      simpa [Fin.sum_univ_succ, add_assoc] using
        defs_le_delta3n hr16 hδ1 hδ3 hδB hδC hδ7 p)
    (fun i _ => by
      fin_cases i
      · exact hD1
      · exact hD3
      · exact hDB
      · exact hDC
      · exact hD7)
    hlogp
  simp only [Fin.sum_univ_succ] at key
  simp at key
  nlinarith [hmain, hr3, hr1, hrx, e, hD1, hD3, key]

end CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

open CatalanFrames.Lambda

/-- The `ε`-form of the content bound with deficits E, B, C5, C7 (no GK), constant
`Λ₂ = 24729491161/6665218560 - 1/448`. -/
theorem lam_both_eps3 {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  set ε₁ : ℝ := min (ε / 2) (1 / 100) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (by norm_num)
  have hε₁1 : ε₁ ≤ 1 / 100 := min_le_right _ _
  have hε₁2 : ε₁ ≤ ε / 2 := min_le_left _ _
  have hd := lam_content_deficit3n (ε := ε₁ / 10) (by positivity)
  have hl := eventually_log_le (e := ε₁ / 10) (by positivity)
  have hbig : ∀ᶠ r : ℕ in atTop, 3 ≤ ε₁ * r := by
    have : Tendsto (fun r : ℕ => ε₁ * (r : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hε₁0
    exact this.eventually_ge_atTop 3
  filter_upwards [hd, hl, hbig, eventually_ge_atTop 16] with r hdr hL hb hr16
  obtain ⟨δ, hδ, hδ1, hδ3, hδB, hδC, hδ7⟩ := lam_defBoth_all3 hr16
  refine ⟨Tfun3 r, δ, hδ, ?_⟩
  have hlog := hdr δ hδ.1 hδ1 hδ3 hδB hδC hδ7
  have hm : (r : ℝ) / 8 - 1 ≤ ((r / 8 : ℕ) : ℝ) := by
    have : (r : ℝ) < 8 * ((r / 8 : ℕ) : ℝ) + 8 := by
      exact_mod_cast (by omega : r < 8 * (r / 8) + 8)
    linarith
  have hL0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  -- absorb the C7 term into `lg' = lg + (1/448 - ε₁/10) r²`
  have key := lam_num (Λ := Λ + 1 / 448 + (ε - 11 / 10 * ε₁)) (ε := ε₁) (r := (r : ℝ))
    (L := Real.log r) (m := ((r / 8 : ℕ) : ℝ))
    (lg := Real.log (DhybT lamInst r (r / 8) (Tfun3 r) δ) + (1 / 448 - ε₁ / 10) * (r : ℝ) ^ 2)
    (by linarith) hε₁0 hε₁1 hb hL0 hL hm (by linarith)
  nlinarith [key]

/-- **`Mem2Content` for λ** at `Λ₂ = 24729491161/6665218560 - 1/448 = 3.70799745…`
(deficits E, B, C5, C7 bordered; GK not bordered). -/
theorem lam_mem2Content3 {Λ : ℝ} (hΛ : 24729491161 / 6665218560 - 1 / 448 ≤ Λ) :
    Mem2Content lamFrame Λ :=
  lam_mem2Content_of_both le_rfl (lam_both_eps3 hΛ)

end CatalanFrames.LambdaHybrid
