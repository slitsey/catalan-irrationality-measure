module

public import CatalanFrames.Lambda.HybContentT4
public import CatalanFrames.Lambda.HybDefAll

@[expose] public section

/-!
# λ: the hybrid content theorem with the additive deficits E and B (`DhybT`)

`lam_content_deficit`: for every `ε > 0`, eventually in `r` there is a deficit family `δ` with
`DefHypT lamInst r ⌊r/8⌋ (Tfun r) δ` (`δ = m` at the clean primes of both classes, `δ = m - (p - r)`
on `r < p < r + m`) and

  `log DhybT ≤ (Λ8 + ε) r² - m ((1/7 - ε) r - 4 log r) - m ((7/80 - ε) r - 6 log r)`,

`m = ⌊r/8⌋`, `Λ8 = 24994314577/6665218560` the tropical constant.  The two subtracted terms are the
class-1 (`5r/7 < p < r`) and class-3 (`5r/8 < p < 4r/5`, `p ≠ 139`) clean-prime deficits of
Lemma E, about `129 r²/4480 = 0.0288 r²` in total (the B deficit is dropped, `δ_B ≥ 0`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma prefixT {r : ℕ} (hr : 16 ≤ r) (p : ℕ) (hp : p.Prime)
    (hpl : p ≤ ⌊(1 / 68 : ℝ) * r⌋₊) : lamWT r p ≤ 9 / 4 * r := by
  refine max_le (lam_prefix r p) ?_
  have h68 : 68 * p ≤ r := by
    have h1 : (p : ℝ) ≤ (1 / 68 : ℝ) * r := (Nat.cast_le.2 hpl).trans (Nat.floor_le (by positivity))
    have : (68 * p : ℝ) ≤ r := by linarith
    exact_mod_cast this
  have h0 : eN r p = 0 := by
    rcases eN_arith r p hr hp with h | h | h | h <;> first | exact h | omega
  rw [h0]; simp

theorem class3_totalT {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (3 : ZMod 4) (lamWT r) 0 (5 * r) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_3 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l3x l3x_chain hε
  filter_upwards [h, eventually_ge_atTop 16] with r hr hr16
  have := hr (lamWT r) (fun p hpl hp _ => prefixT hr16 p hp hpl) (by
    intro P hP
    unfold l3x at hP
    rcases List.mem_append.mp hP with h | h
    · exact ld1_covers_T 3 (by decide) hr16 P h
    · simp only [l3, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      exacts [c3T_1 hr16, c3T_2 hr16, c3T_3 hr16, c3T_4 hr16, c3T_5 hr16])
  rw [l3x_end, floor_frac] at this
  simpa [tot4] using this

theorem class1_totalT {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (1 : ZMod 4) (lamWT r) 0 (5 * r / 3) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_1 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l1x l1x_chain hε
  filter_upwards [h, eventually_ge_atTop 16] with r hr hr16
  have := hr (lamWT r) (fun p hpl hp _ => prefixT hr16 p hp hpl) (by
    intro P hP
    unfold l1x at hP
    rcases List.mem_append.mp hP with h | h
    · exact ld1_covers_T 1 (by decide) hr16 P h
    · simp only [l1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [c1T_1 hr16, c1T_2 hr16, c1T_3 hr16, c1T_4 hr16, c1T_5 hr16, c1T_6 hr16])
  rw [l1x_end, floor_frac] at this
  simpa [tot4] using this

theorem lam_content_deficit {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∃ δ : ℕ → ℕ, DefHypT lamInst r (r / 8) (Tfun r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) ∧
      Real.log (DhybT lamInst r (r / 8) (Tfun r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r) := by
  have h3 := class3_totalT (ε := ε / 4) (by positivity)
  have h1 := class1_totalT (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 2) (by positivity)
  have hE1 := lam_E1_deficit_sum hε
  have hE3 := lam_E3_deficit_sum hε
  filter_upwards [h3, h1, hx, hE1, hE3, eventually_ge_atTop 16] with r hr3 hr1 hrx hD1 hD3 hr16
  obtain ⟨δ, hδ, hδ1, hδ3, hδB⟩ := lam_defHypT_all hr16
  refine ⟨δ, hδ, hδ1, hδ3, hδB, ?_⟩
  have hmain := lam_log_DhybT_le hr16 hδ
  have hex := hrx (r / 8) (Nat.div_le_self r 8)
  have hc := lam_const8
  have e : (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε / 4) +
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε / 4) =
      (r : ℝ) ^ 2 * (24994314577 / 6665218560 + ε / 2) := by
    rw [← mul_add]
    congr 1
    linarith
  -- the deficit sum dominates the two lower bounds
  have hlogp : ∀ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have hdom : ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      (defE1 r p : ℝ) * Real.log p + ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      (defE3 r p : ℝ) * Real.log p ≤
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hlogp p hp)
    by_cases c1 : cleanE1 r p
    · have n3 : ¬ cleanE3 r p := fun h => by have := c1.2.1; have := h.2.1; omega
      have e1 : defE1 r p = r / 8 := by simp [defE1, c1]
      have e3 : defE3 r p = 0 := by simp [defE3, n3]
      rw [e1, e3, hδ1 p c1]; simp
    · by_cases c3 : cleanE3 r p
      · have e1 : defE1 r p = 0 := by simp [defE1, c1]
        have e3 : defE3 r p = r / 8 := by simp [defE3, c3]
        rw [e1, e3, hδ3 p c3]; simp
      · have e1 : defE1 r p = 0 := by simp [defE1, c1]
        have e3 : defE3 r p = 0 := by simp [defE3, c3]
        rw [e1, e3]; simp
  nlinarith [hmain, hr3, hr1, hex, e, hD1, hD3, hdom]

end CatalanFrames.Lambda
