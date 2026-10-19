module

public import CatalanFrames.HybCommon.TropT
public import CatalanCore.Arith.Hybrid.Extra

@[expose] public section

/-!
# `log DhybT` for the glued deficit family, generic in the instance (class dictionary)

`sum_le_G`: the per-prime bookkeeping (bad prime `2`, an optional second bad prime `3` marked by `X`,
higher levels, level-1 class sums) for any weights, independent of the frame.
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

/-- The extra weight of the prime `2`. -/
noncomputable def ex2G (r : ℕ) : ℝ :=
  (4 + 2 * (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℝ)) *
    ((r + r / 8 : ℕ) : ℝ)

/-- The extra weight of the (optional) bad prime `3`. -/
noncomputable def ex3G (r : ℕ) : ℝ :=
  2 * ((r + r / 8 : ℕ) : ℝ) *
    (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℝ)

lemma g_sum_eq_G (w : ℕ → ℝ) (B : ℕ) :
    ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime,
        (if p = 2 then (0 : ℝ) else w p * Real.log p) =
      clsSum 4 (1 : ZMod 4) w 0 B + clsSum 4 (3 : ZMod 4) w 0 B := by
  have hset : (Finset.range (B + 1)).filter Nat.Prime = (Finset.Ioc 0 B).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩
  rw [hset, clsSum_eq, clsSum_eq, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · by_cases h2 : p = 2
    · subst h2
      simp [cast4_two.1, cast4_two.2]
    · rcases prime_class4 hp h2 with ⟨h3, h1⟩ | ⟨h1, h3⟩
      · rw [if_pos hp, if_neg h2, if_neg (fun h => h1 h.2), if_pos ⟨hp, h3⟩, zero_add]
      · rw [if_pos hp, if_neg h2, if_pos ⟨hp, h1⟩, if_neg (fun h => h3 h.2), add_zero]
  · simp [hp]

lemma log3_le_G : Real.log 3 ≤ 2 * Real.log 2 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [← this]
  exact Real.log_le_log (by norm_num) (by norm_num)

/-- **Level-1 plus negligible terms (mirror).** -/
theorem sum_le_G (r : ℕ) (hr : 4 ≤ r) (T : ℕ → ℕ) (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (cnt : ℕ → ℕ) (hcnt_le : ∀ p, p.Prime → cnt p ≤ Nat.log 2 (4 * (r + 2 * (r / 8))))
    (hcnt0 : ∀ p, p.Prime → 4 * (r + 2 * (r / 8)) < p ^ 2 → cnt p = 0)
    (X : ℕ → Prop) (hX : ∀ p, X p → p = 3)
    (hT : ∀ p, p.Prime → (T p : ℝ) ≤ (if p = 2 then ex2G r else 0) +
      (if X p then ex3G r else 0) + ((2 * (r + r / 8) * cnt p : ℕ) : ℝ) +
      (if p = 2 ∨ X p then 0 else w p))
    (R1 R3 : ℕ) (hR3 : 3 ≤ R3)
    (ht1 : ∀ p, p.Prime → 5 ≤ p → p % 4 = 1 → R1 < p → w p = 0)
    (ht3 : ∀ p, p.Prime → 5 ≤ p → p % 4 = 3 → R3 < p → w p = 0) :
    ∑ p ∈ (Finset.range (4 * (r + 2 * (r / 8)) + 6)).filter Nat.Prime, (T p : ℝ) * Real.log p ≤
      3 * extraBound r (r / 8) + clsSum 4 (1 : ZMod 4) w 0 R1 +
      clsSum 4 (3 : ZMod 4) w 0 R3 := by
  set m := r / 8 with hm
  set P := (Finset.range (4 * (r + 2 * m) + 6)).filter Nat.Prime with hP
  set P5 := (Finset.range (4 * (r + 2 * m) + 5)).filter Nat.Prime with hP5
  have hlogpos : ∀ p ∈ P, 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have hpt : ∀ p ∈ P, (T p : ℝ) * Real.log p ≤
      (((if p = 2 then ex2G r else 0) + ((2 * (r + r / 8) * cnt p : ℕ) : ℝ)) * Real.log p) +
        ((if X p then ex3G r * Real.log 3 else 0) +
          (if p = 2 ∨ X p then 0 else w p * Real.log p)) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have h := hT p hpp
    have e3 : (if X p then ex3G r else 0) * Real.log p =
        if X p then ex3G r * Real.log 3 else 0 := by
      by_cases hx : X p
      · have := hX p hx; subst this; simp [hx]
      · simp [hx]
    have := mul_le_mul_of_nonneg_right h hlog
    by_cases hw : p = 2 ∨ X p
    · simp only [hw, if_true, add_zero] at this
      calc _ ≤ _ := this
        _ = _ := by
          rw [add_mul, add_mul, e3]; simp only [hw, if_true]; simp only [hm]; push_cast; ring
    · simp only [hw, if_false] at this ⊢
      calc _ ≤ _ := this
        _ = _ := by
          rw [add_mul, add_mul, add_mul, e3]
          have h3' : ¬ X p := fun h => hw (Or.inr h)
          simp only [h3', if_false]; simp only [hm]; push_cast; ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the extra terms of the primes below `4N + 5`
  have hlam : 0 ≤ ex2G r := by unfold ex2G; positivity
  have hex5 : ∑ p ∈ P5, (((if p = 2 then ex2G r else 0) +
      ((2 * (r + r / 8) * cnt p : ℕ) : ℝ)) * Real.log p) ≤ extraBound r m := by
    have := ex_sum_bound r m (4 * (r + 2 * m) + 5) (ex2G r) hlam
      (fun p => 2 * (r + r / 8) * cnt p) (Nat.log 2 (4 * (r + 2 * m))) le_rfl
      (fun p hp => Nat.mul_le_mul_left _ (hcnt_le p hp))
      (fun p hp h => by simp [hcnt0 p hp h])
    refine this.trans (le_of_eq ?_)
    unfold extraBound ex2G
    push_cast
    ring
  have hnn : ∀ p, 0 ≤ ((if p = 2 then ex2G r else 0) +
      ((2 * (r + r / 8) * cnt p : ℕ) : ℝ)) * Real.log p := by
    intro p
    have h0 : 0 ≤ (if p = 2 then ex2G r else 0) := by split_ifs <;> [exact hlam; exact le_rfl]
    have hl : 0 ≤ Real.log p := by
      by_cases hp1 : 1 ≤ p
      · exact Real.log_nonneg (by exact_mod_cast hp1)
      · have : p = 0 := by omega
        subst this; simp
    positivity
  have hex : ∑ p ∈ P, (((if p = 2 then ex2G r else 0) + ((2 * (r + r / 8) * cnt p : ℕ) : ℝ)) *
      Real.log p) ≤ extraBound r m := by
    by_cases hq : (4 * (r + 2 * m) + 5).Prime
    · have hnot : (4 * (r + 2 * m) + 5) ∉ P5 := by simp [hP5]
      have hPe : P = insert (4 * (r + 2 * m) + 5) P5 := by
        ext p
        simp only [hP, hP5, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h : p = 4 * (r + 2 * m) + 5
          · exact Or.inl h
          · exact Or.inr ⟨by omega, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · subst h; exact ⟨by omega, hq⟩
          · exact ⟨by omega, h2⟩
      rw [hPe, Finset.sum_insert hnot]
      have hz : cnt (4 * (r + 2 * m) + 5) = 0 := hcnt0 _ hq (by nlinarith)
      have h2 : (4 * (r + 2 * m) + 5 : ℕ) ≠ 2 := by omega
      simp only [hz, h2, if_false, Nat.mul_zero, Nat.cast_zero, add_zero, zero_mul, zero_add]
      exact hex5
    · have hPe : P = P5 := by
        ext p
        simp only [hP, hP5, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          have : p ≠ 4 * (r + 2 * m) + 5 := fun h => hq (h ▸ h2)
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      rw [hPe]
      exact hex5
  -- the prime 3
  have hE3 : ∑ p ∈ P, (if X p then ex3G r * Real.log 3 else 0) ≤ 2 * extraBound r m := by
    have hE3nn : 0 ≤ ex3G r * Real.log 3 := by
      unfold ex3G
      have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      positivity
    have h1 : ∑ p ∈ P, (if X p then ex3G r * Real.log 3 else 0) ≤ ex3G r * Real.log 3 := by
      rw [← Finset.sum_filter]
      have : (P.filter (fun p => X p)) ⊆ {3} := by
        intro x hx; simp only [Finset.mem_filter] at hx; simp [hX x hx.2]
      calc _ ≤ ∑ p ∈ ({3} : Finset ℕ), ex3G r * Real.log 3 :=
            Finset.sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => hE3nn)
        _ = _ := by simp
    refine h1.trans ?_
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hex2 : ex3G r ≤ ex2G r := by
      unfold ex3G ex2G
      have : (0 : ℝ) ≤ ((r + r / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hext : ex2G r * Real.log 2 ≤ extraBound r m := by
      unfold extraBound ex2G
      have h2 : 0 ≤ ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) *
          (2 * (r + m : ℝ) * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) * Real.log (4 * (r + 2 * m) + 5)) := by
        have : 0 ≤ Real.log (4 * ((r : ℝ) + 2 * m) + 5) := Real.log_nonneg (by
          have : (0 : ℝ) ≤ 4 * ((r : ℝ) + 2 * m) := by positivity
          linarith)
        positivity
      push_cast
      nlinarith
    have hl3 := log3_le_G
    calc ex3G r * Real.log 3 ≤ ex2G r * (2 * Real.log 2) := by
          apply mul_le_mul hex2 hl3 (Real.log_nonneg (by norm_num)) hlam
      _ = 2 * (ex2G r * Real.log 2) := by ring
      _ ≤ 2 * extraBound r m := by linarith
  -- the level-1 sums
  have hg : ∑ p ∈ P, (if p = 2 ∨ X p then 0 else w p * Real.log p) ≤
      clsSum 4 (1 : ZMod 4) w 0 R1 +
        clsSum 4 (3 : ZMod 4) w 0 R3 := by
    have hle : ∑ p ∈ P, (if p = 2 ∨ X p then 0 else w p * Real.log p) ≤
        ∑ p ∈ P, (if p = 2 then (0 : ℝ) else w p * Real.log p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpp := (Finset.mem_filter.mp hp).2
      have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
      have hW := hw0 p
      by_cases h2 : p = 2
      · simp [h2]
      · by_cases h3 : X p
        · rw [if_pos (Or.inr h3), if_neg h2]; exact mul_nonneg hW hlog
        · simp [h2, h3]
    refine hle.trans ?_
    have hPe : P = (Finset.range (4 * (r + 2 * m) + 5 + 1)).filter Nat.Prime := rfl
    rw [hPe, g_sum_eq_G w (4 * (r + 2 * m) + 5)]
    have t1 := clsSum_le_of_tail (M := 4) (1 : ZMod 4) w hw0
      (B := 4 * (r + 2 * m) + 5) (B' := R1) (by
        intro p hp1 hpp hpc
        have h1 := cls4_mod1 hpc
        exact ht1 p hpp (by have := hpp.two_le; have := hpp.eq_two_or_odd; omega) h1 hp1)
    have t3 := clsSum_le_of_tail (M := 4) (3 : ZMod 4) w hw0
      (B := 4 * (r + 2 * m) + 5) (B' := R3) (by
        intro p hp1 hpp hpc
        have h3 := cls4_mod3 hpc
        exact ht3 p hpp (by omega) h3 hp1)
    linarith
  linarith


end CatalanFrames.HybCommon
