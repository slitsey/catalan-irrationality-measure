module

public import CatalanFrames.LambdaMirrorHybrid.MirFinal2

@[expose] public section

/-!
# Mirror: the tropical hybrid content theorem (exact D1, truncation `K = 8`)

`mir_content_trop8`: for every `ε > 0`, eventually in `r`,
`log (Dhyb mirNInst r ⌊r/8⌋) ≤ (Λ8 + ε) r²` with the SAME constant `Λ8 = 24994314577/6665218560` as λ:
the piece tables `l3x`, `l1x` are shared, only the residue classes are swapped
(`l3x` for `p ≡ 1 (4)`, `l1x` for `p ≡ 3 (4)`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
  CatalanFrames.HybCommon CatalanFrames.Lambda

namespace CatalanFrames.LambdaMirrorHybrid

lemma mirW_prefix (r p : ℕ) : WG mirNInst r p ≤ 9 / 4 * r := by
  have hb := XG_D1 mirN_tropFacts r p
  have := real_of_int_bound (x := XG mirNInst r p) (r := r) (p := p) 4 9 0 0 (by norm_num)
    (by omega)
  norm_num at this
  show (XG mirNInst r p : ℝ) ≤ _
  linarith

lemma e_cJ1 : cJ1 3 = (1 : ZMod 4) := by decide
lemma e_cJ3 : cJ3 3 = (3 : ZMod 4) := by decide

theorem mir_class1_total8 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (1 : ZMod 4) (WG mirNInst r) 0 (5 * r) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_1 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l3x l3x_chain hε
  filter_upwards [h, eventually_ge_atTop 400] with r hr hr4
  have := hr (WG mirNInst r) (fun p _ _ _ => mirW_prefix r p) (by
    intro P hP
    unfold l3x at hP
    rcases List.mem_append.mp hP with h | h
    · simp only [ld1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [d1g_0 mirN_tropFacts 1 (by decide) r, d1g_1 mirN_tropFacts 1 (by decide) r,
        d1g_2 mirN_tropFacts 1 (by decide) r, d1g_3 mirN_tropFacts 1 (by decide) r,
        d1g_4 mirN_tropFacts 1 (by decide) r, d1g_5 mirN_tropFacts 1 (by decide) r,
        d1g_6 mirN_tropFacts 1 (by decide) r, d1g_7 mirN_tropFacts 1 (by decide) r,
        d1g_8 mirN_tropFacts 1 (by decide) r, d1g_9 mirN_tropFacts 1 (by decide) r,
        d1g_10 mirN_tropFacts 1 (by decide) r, d1g_11 mirN_tropFacts 1 (by decide) r,
        d1g_12 mirN_tropFacts 1 (by decide) r, d1g_13 mirN_tropFacts 1 (by decide) r,
        d1g_14 mirN_tropFacts 1 (by decide) r, d1g_15 mirN_tropFacts 1 (by decide) r]
    · simp only [l3, List.mem_cons, List.mem_nil_iff, or_false] at h
      rw [← e_cJ1]
      rcases h with rfl | rfl | rfl | rfl | rfl
      exacts [cj1_1 mirN_tropFacts r hr4, cj1_2 mirN_tropFacts r hr4, cj1_3 mirN_tropFacts r hr4,
        cj1_4 mirN_tropFacts r hr4, cj1_5 mirN_tropFacts r hr4])
  rw [l3x_end, floor_frac] at this
  simpa [tot4] using this

theorem mir_class3_total8 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (3 : ZMod 4) (WG mirNInst r) 0 (5 * r / 3) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_3 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l1x l1x_chain hε
  filter_upwards [h, eventually_ge_atTop 400] with r hr hr4
  have := hr (WG mirNInst r) (fun p _ _ _ => mirW_prefix r p) (by
    intro P hP
    unfold l1x at hP
    rcases List.mem_append.mp hP with h | h
    · simp only [ld1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [d1g_0 mirN_tropFacts 3 (by decide) r, d1g_1 mirN_tropFacts 3 (by decide) r,
        d1g_2 mirN_tropFacts 3 (by decide) r, d1g_3 mirN_tropFacts 3 (by decide) r,
        d1g_4 mirN_tropFacts 3 (by decide) r, d1g_5 mirN_tropFacts 3 (by decide) r,
        d1g_6 mirN_tropFacts 3 (by decide) r, d1g_7 mirN_tropFacts 3 (by decide) r,
        d1g_8 mirN_tropFacts 3 (by decide) r, d1g_9 mirN_tropFacts 3 (by decide) r,
        d1g_10 mirN_tropFacts 3 (by decide) r, d1g_11 mirN_tropFacts 3 (by decide) r,
        d1g_12 mirN_tropFacts 3 (by decide) r, d1g_13 mirN_tropFacts 3 (by decide) r,
        d1g_14 mirN_tropFacts 3 (by decide) r, d1g_15 mirN_tropFacts 3 (by decide) r]
    · simp only [l1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rw [← e_cJ3]
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [cj3_1 mirN_tropFacts r hr4, cj3_2 mirN_tropFacts r hr4, cj3_3 mirN_tropFacts r hr4,
        cj3_4 mirN_tropFacts r hr4, cj3_5 mirN_tropFacts r hr4, cj3_6 mirN_tropFacts r hr4])
  rw [l1x_end, floor_frac] at this
  simpa [tot4] using this

/-- **The mirror hybrid content theorem (tropical), exact D1 truncated at `K = 8`.** -/
theorem mir_content_trop8 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, Real.log (Dhyb mirNInst r (r / 8)) ≤
      (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 := by
  have h1 := mir_class1_total8 (ε := ε / 4) (by positivity)
  have h3 := mir_class3_total8 (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 6) (by positivity)
  filter_upwards [h1, h3, hx, eventually_ge_atTop 4] with r hr1 hr3 hrx hr0
  have hmain := mir_log_Dhyb_le r hr0
  have hex := hrx (r / 8) (Nat.div_le_self r 8)
  have hc := lam_const8
  have e : (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε / 4) +
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε / 4) =
      (r : ℝ) ^ 2 * (24994314577 / 6665218560 + ε / 2) := by
    rw [← mul_add]
    congr 1
    linarith
  nlinarith [hmain, hr3, hr1, hex, e]

#print axioms mir_content_trop8

end CatalanFrames.LambdaMirrorHybrid
