module

public import CatalanFrames.LambdaMirrorHybrid.MirLegacy
public import CatalanFrames.HybCommon.TropT

@[expose] public section

/-!
# Mirror: the content bound for the deficit family (`DhybT`), before the deficit sums

`mir_logDhybT_le`: for every `ε > 0`, eventually in `r`, for every deficit family `δ` valid against
`TfunG 3 mirNInst r`,
`log DhybT ≤ (Λ8 + ε) r² - ∑_p δ p log p`, `Λ8 = 24994314577/6665218560` (the λ constant).
What remains for `mir_content_deficit3` is the lower bounds for `∑ δ log p` (deficit sums).
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.LambdaMirror CatalanFrames.HybCommon CatalanFrames.Lambda

namespace CatalanFrames.LambdaMirrorHybrid

lemma eNG_le {o : ℕ} (ho : o = 1 ∨ o = 3) {r p : ℕ} (hr : 16 ≤ r) : 4 * eNG o r p ≤ 9 * r := by
  rcases eNG_cases (o := o) (r := r) (p := p) ho hr with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
      ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
      ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
  · rw [h]; omega
  · rw [e]; rcases ho with rfl | rfl <;> omega
  · rw [e]; rcases ho with rfl | rfl <;> omega
  · rw [e]; unfold kBG; rcases ho with rfl | rfl <;> split_ifs <;> omega
  · rw [e]; rcases ho with rfl | rfl <;> omega
  · rw [e]; rcases ho with rfl | rfl <;> omega
  · rw [e]; omega

lemma eNG_small {o : ℕ} (ho : o = 1 ∨ o = 3) {r p : ℕ} (hr : 16 ≤ r) (hp : p ≤ 3) :
    eNG o r p = 0 := by
  rcases eNG_cases (o := o) (r := r) (p := p) ho hr with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
      ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
      ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
  · exact h
  all_goals first
    | (exfalso; rcases ho with rfl | rfl <;> omega)
    | (exfalso; rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> omega)

lemma eNG_tail {o : ℕ} (ho : o = 1 ∨ o = 3) {r p : ℕ} (hr : 16 ≤ r) (hp : 5 * r / 3 < p) :
    eNG o r p = 0 := by
  rcases eNG_cases (o := o) (r := r) (p := p) ho hr with h | ⟨⟨_, c2, c3, c4⟩, e⟩ |
      ⟨⟨_, c2, c3, c4, _⟩, e⟩ | ⟨⟨_, c2, c3⟩, e⟩ | ⟨⟨_, c2, c3, c4, c5⟩, e⟩ |
      ⟨⟨_, c2, c3, c4⟩, e⟩ | ⟨hLC, e⟩
  · exact h
  all_goals first
    | (exfalso; rcases ho with rfl | rfl <;> omega)
    | (exfalso; rcases hLC with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;> omega)

lemma mirWT_prefix (r p : ℕ) (hr : 16 ≤ r) : WTG mirNInst 3 r p ≤ 9 / 4 * r := by
  refine max_le (mirW_prefix r p) ?_
  have := eNG_le (o := 3) (Or.inr rfl) (r := r) (p := p) hr
  have h : (4 : ℝ) * (eNG 3 r p : ℝ) ≤ 9 * r := by exact_mod_cast this
  linarith

lemma TfunG_mir_le (r p : ℕ) (hr : 16 ≤ r) (hp : p.Prime) :
    (TfunG 3 mirNInst r p : ℝ) ≤ (if p = 2 then mirEx2 r else 0) + (if p = 3 then mirEx3 r else 0) +
      ((2 * (r + r / 8) * cntM r (r / 8) p : ℕ) : ℝ) +
      (if p = 2 ∨ p = 3 then 0 else WTG mirNInst 3 r p) := by
  have h := tropExp_mir_le r p (by omega) hp
  have hE2 : 0 ≤ mirEx2 r := by unfold mirEx2; positivity
  have hE3 : 0 ≤ mirEx3 r := by unfold mirEx3; positivity
  have hn : (0 : ℝ) ≤ ((2 * (r + r / 8) * cntM r (r / 8) p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hW : 0 ≤ WTG mirNInst 3 r p := WTG_nonneg _ _ _ _
  have hWG : WG mirNInst r p ≤ WTG mirNInst 3 r p := le_max_left _ _
  have heN : (eNG 3 r p : ℝ) ≤ WTG mirNInst 3 r p := le_max_right _ _
  have hex : 0 ≤ (if p = 2 then mirEx2 r else 0) := by split_ifs <;> [exact hE2; exact le_rfl]
  have hex3 : 0 ≤ (if p = 3 then mirEx3 r else 0) := by split_ifs <;> [exact hE3; exact le_rfl]
  have hT : (TfunG 3 mirNInst r p : ℝ) = max (tropExp mirNInst r (r / 8) p : ℝ) (eNG 3 r p : ℝ) := by
    unfold TfunG; rw [Nat.cast_max]
  rw [hT]
  have hif : (if p = 2 ∨ p = 3 then (0 : ℝ) else WG mirNInst r p) ≤
      (if p = 2 ∨ p = 3 then 0 else WTG mirNInst 3 r p) := by
    by_cases hw : p = 2 ∨ p = 3
    · simp [hw]
    · simp [hw, hWG]
  have hifnn : 0 ≤ (if p = 2 ∨ p = 3 then (0 : ℝ) else WTG mirNInst 3 r p) := by
    split_ifs <;> [exact le_rfl; exact hW]
  refine max_le (h.trans (by linarith)) ?_
  by_cases hw : p = 2 ∨ p = 3
  · have h0 : eNG 3 r p = 0 := eNG_small (Or.inr rfl) hr (by omega)
    rw [h0, Nat.cast_zero]
    linarith
  · rw [if_neg hw] at hifnn ⊢
    linarith

theorem mir_class1_totalT {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (1 : ZMod 4) (WTG mirNInst 3 r) 0 (5 * r) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_1 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l3x l3x_chain hε
  filter_upwards [h, eventually_ge_atTop 400] with r hr hr4
  have := hr (WTG mirNInst 3 r) (fun p _ _ _ => mirWT_prefix r p (by omega)) (by
    intro P hP
    unfold l3x at hP
    rcases List.mem_append.mp hP with h | h
    · simp only [ld1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [cwd1_0 mirN_tropFacts 1 (by decide) r hr4, cwd1_1 mirN_tropFacts 1 (by decide) r hr4,
        cwd1_2 mirN_tropFacts 1 (by decide) r hr4, cwd1_3 mirN_tropFacts 1 (by decide) r hr4,
        cwd1_4 mirN_tropFacts 1 (by decide) r hr4, cwd1_5 mirN_tropFacts 1 (by decide) r hr4,
        cwd1_6 mirN_tropFacts 1 (by decide) r hr4, cwd1_7 mirN_tropFacts 1 (by decide) r hr4,
        cwd1_8 mirN_tropFacts 1 (by decide) r hr4, cwd1_9 mirN_tropFacts 1 (by decide) r hr4,
        cwd1_10 mirN_tropFacts 1 (by decide) r hr4, cwd1_11 mirN_tropFacts 1 (by decide) r hr4,
        cwd1_12 mirN_tropFacts 1 (by decide) r hr4, cwd1_13 mirN_tropFacts 1 (by decide) r hr4,
        cwd1_14 mirN_tropFacts 1 (by decide) r hr4, cwd1_15 mirN_tropFacts 1 (by decide) r hr4]
    · simp only [l3, List.mem_cons, List.mem_nil_iff, or_false] at h
      rw [← e_cJ1]
      rcases h with rfl | rfl | rfl | rfl | rfl
      exacts [cwj1_1 mirN_tropFacts r hr4, cwj1_2 mirN_tropFacts r hr4, cwj1_3 mirN_tropFacts r hr4,
        cwj1_4 mirN_tropFacts r hr4, cwj1_5 mirN_tropFacts r hr4])
  rw [l3x_end, floor_frac] at this
  simpa [tot4] using this

theorem mir_class3_totalT {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (3 : ZMod 4) (WTG mirNInst 3 r) 0 (5 * r / 3) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_3 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l1x l1x_chain hε
  filter_upwards [h, eventually_ge_atTop 400] with r hr hr4
  have := hr (WTG mirNInst 3 r) (fun p _ _ _ => mirWT_prefix r p (by omega)) (by
    intro P hP
    unfold l1x at hP
    rcases List.mem_append.mp hP with h | h
    · simp only [ld1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [cwd1_0 mirN_tropFacts 3 (by decide) r hr4, cwd1_1 mirN_tropFacts 3 (by decide) r hr4,
        cwd1_2 mirN_tropFacts 3 (by decide) r hr4, cwd1_3 mirN_tropFacts 3 (by decide) r hr4,
        cwd1_4 mirN_tropFacts 3 (by decide) r hr4, cwd1_5 mirN_tropFacts 3 (by decide) r hr4,
        cwd1_6 mirN_tropFacts 3 (by decide) r hr4, cwd1_7 mirN_tropFacts 3 (by decide) r hr4,
        cwd1_8 mirN_tropFacts 3 (by decide) r hr4, cwd1_9 mirN_tropFacts 3 (by decide) r hr4,
        cwd1_10 mirN_tropFacts 3 (by decide) r hr4, cwd1_11 mirN_tropFacts 3 (by decide) r hr4,
        cwd1_12 mirN_tropFacts 3 (by decide) r hr4, cwd1_13 mirN_tropFacts 3 (by decide) r hr4,
        cwd1_14 mirN_tropFacts 3 (by decide) r hr4, cwd1_15 mirN_tropFacts 3 (by decide) r hr4]
    · simp only [l1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rw [← e_cJ3]
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [cwj3_1 mirN_tropFacts r hr4, cwj3_2 mirN_tropFacts r hr4, cwj3_3 mirN_tropFacts r hr4,
        cwj3_4 mirN_tropFacts r hr4, cwj3_5 mirN_tropFacts r hr4, cwj3_6 mirN_tropFacts r hr4])
  rw [l1x_end, floor_frac] at this
  simpa [tot4] using this

/-- **The content bound for the glued deficit family, mirror (before the deficit sums).** -/
theorem mir_logDhybT_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT mirNInst r (r / 8) (TfunG 3 mirNInst r) δ →
      Real.log (DhybT mirNInst r (r / 8) (TfunG 3 mirNInst r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ∑ p ∈ (Finset.range (Bnd mirNInst r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
  have h1 := mir_class1_totalT (ε := ε / 4) (by positivity)
  have h3 := mir_class3_totalT (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 6) (by positivity)
  filter_upwards [h1, h3, hx, eventually_ge_atTop 400] with r hr1 hr3 hrx hr0 δ hδ
  have hr16 : 16 ≤ r := by omega
  rw [log_DhybT mirNInst r (r / 8) hδ, mir_Bnd]
  have hmain := mir_sum_le r (by omega) (TfunG 3 mirNInst r) (WTG mirNInst 3 r)
    (WTG_nonneg _ _ _) (fun p hp => TfunG_mir_le r p hr16 hp)
    (fun p hp h5 hm ht => by
      have hk := mirN_tropFacts.kq1 p hp h5 (by omega)
      have := XG_D6 mirN_tropFacts r p hp h5 (by omega) (by omega)
      have hz : XG mirNInst r p = 0 := by omega
      have he := eNG_tail (o := 3) (Or.inr rfl) hr16 (r := r) (p := p) (by omega)
      simp [WTG, WG, hz, he])
    (fun p hp h5 hm ht => by
      have hz : XG mirNInst r p = 0 := mir_tail3 r p hp h5 hm ht
      have he := eNG_tail (o := 3) (Or.inr rfl) hr16 (r := r) (p := p) ht
      simp [WTG, WG, hz, he])
  have hex := hrx (r / 8) (Nat.div_le_self r 8)
  have hc := lam_const8
  have e : (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε / 4) +
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε / 4) =
      (r : ℝ) ^ 2 * (24994314577 / 6665218560 + ε / 2) := by
    rw [← mul_add]
    congr 1
    linarith
  nlinarith [hmain, hr3, hr1, hex, e]

#print axioms mir_logDhybT_le

end CatalanFrames.LambdaMirrorHybrid
