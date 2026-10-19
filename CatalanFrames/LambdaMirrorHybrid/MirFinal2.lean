module

public import CatalanFrames.LambdaMirrorHybrid.MirFinal

@[expose] public section

/-!
# Mirror: the tropical content bound (class sums)

`mir_log_Dhyb_le`: `log Dhyb mirNInst r ⌊r/8⌋ ≤ 3 · extraBound + clsSum₁ + clsSum₃` (the bad prime `3`
costs at most twice the prime-`2` term).  The class `j = 1` is `p ≡ 1 (4)` (summed to `5r`), the class
`j = 3` is `p ≡ 3 (4)` (summed to `5r/3`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
  CatalanFrames.HybCommon CatalanFrames.Lambda

namespace CatalanFrames.LambdaMirrorHybrid

lemma mirW_nonneg (r p : ℕ) : 0 ≤ WG mirNInst r p := Nat.cast_nonneg _

lemma mir_tail1 (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : p % 4 = 1) (ht : 5 * r < p) :
    XG mirNInst r p = 0 := by
  have hk := mirN_tropFacts.kq1 p hp h5 (by omega)
  have := XG_D6 mirN_tropFacts r p hp h5 (by omega) (by omega)
  omega

lemma mir_tail3 (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : p % 4 = 3) (ht : 5 * r / 3 < p) :
    XG mirNInst r p = 0 := by
  have hk := mirN_tropFacts.kq3 p hp h5 (by omega)
  have := XG_D6 mirN_tropFacts r p hp h5 (by omega) (by omega)
  omega

lemma mir_g_sum_eq (r B : ℕ) :
    ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime,
        (if p = 2 then (0 : ℝ) else WG mirNInst r p * Real.log p) =
      clsSum 4 (1 : ZMod 4) (WG mirNInst r) 0 B + clsSum 4 (3 : ZMod 4) (WG mirNInst r) 0 B := by
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

lemma log3_le : Real.log 3 ≤ 2 * Real.log 2 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [← this]
  exact Real.log_le_log (by norm_num) (by norm_num)

/-- **Level-1 plus negligible terms (mirror).** -/
theorem mir_log_Dhyb_le (r : ℕ) (hr : 4 ≤ r) :
    Real.log (Dhyb mirNInst r (r / 8)) ≤ 3 * extraBound r (r / 8) +
      clsSum 4 (1 : ZMod 4) (WG mirNInst r) 0 (5 * r) +
      clsSum 4 (3 : ZMod 4) (WG mirNInst r) 0 (5 * r / 3) := by
  set m := r / 8 with hm
  rw [log_Dhyb, mir_Bnd]
  set P := (Finset.range (4 * (r + 2 * m) + 6)).filter Nat.Prime with hP
  set P5 := (Finset.range (4 * (r + 2 * m) + 5)).filter Nat.Prime with hP5
  have hlogpos : ∀ p ∈ P, 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have hpt : ∀ p ∈ P, (tropExp mirNInst r m p : ℝ) * Real.log p ≤
      (((if p = 2 then mirEx2 r else 0) + ((2 * (r + r / 8) * cntM r m p : ℕ) : ℝ)) * Real.log p) +
        ((if p = 3 then mirEx3 r * Real.log 3 else 0) +
          (if p = 2 ∨ p = 3 then 0 else WG mirNInst r p * Real.log p)) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have h := tropExp_mir_le r p (by omega) hpp
    have e3 : (if p = 3 then mirEx3 r else 0) * Real.log p =
        if p = 3 then mirEx3 r * Real.log 3 else 0 := by
      split_ifs with h3
      · subst h3; rfl
      · simp
    have := mul_le_mul_of_nonneg_right h hlog
    by_cases hw : p = 2 ∨ p = 3
    · simp only [if_pos hw, add_zero] at this
      calc _ ≤ _ := this
        _ = _ := by rw [add_mul, add_mul, e3]; simp only [if_pos hw]; ring
    · simp only [if_neg hw] at this ⊢
      calc _ ≤ _ := this
        _ = _ := by
          rw [add_mul, add_mul, add_mul, e3]
          have h3' : p ≠ 3 := fun h => hw (Or.inr h)
          simp only [if_neg h3']; ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the extra terms of the primes below `4N + 5`
  have hlam : 0 ≤ mirEx2 r := by unfold mirEx2; positivity
  have hex5 : ∑ p ∈ P5, (((if p = 2 then mirEx2 r else 0) +
      ((2 * (r + r / 8) * cntM r m p : ℕ) : ℝ)) * Real.log p) ≤ extraBound r m := by
    have := ex_sum_bound r m (4 * (r + 2 * m) + 5) (mirEx2 r) hlam
      (fun p => 2 * (r + r / 8) * cntM r m p) (Nat.log 2 (4 * (r + 2 * m))) le_rfl
      (fun p hp => Nat.mul_le_mul_left _ (cntM_le r m p hp))
      (fun p hp h => by simp [cntM_zero r m p hp h])
    refine this.trans (le_of_eq ?_)
    unfold extraBound mirEx2
    push_cast
    ring
  have hnn : ∀ p, 0 ≤ ((if p = 2 then mirEx2 r else 0) +
      ((2 * (r + r / 8) * cntM r m p : ℕ) : ℝ)) * Real.log p := by
    intro p
    have h0 : 0 ≤ (if p = 2 then mirEx2 r else 0) := by split_ifs <;> [exact hlam; exact le_rfl]
    have hl : 0 ≤ Real.log p := by
      by_cases hp1 : 1 ≤ p
      · exact Real.log_nonneg (by exact_mod_cast hp1)
      · have : p = 0 := by omega
        subst this; simp
    positivity
  have hex : ∑ p ∈ P, (((if p = 2 then mirEx2 r else 0) + ((2 * (r + r / 8) * cntM r m p : ℕ) : ℝ)) *
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
      have hz : cntM r m (4 * (r + 2 * m) + 5) = 0 := cntM_zero r m _ hq (by nlinarith)
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
  have hE3 : ∑ p ∈ P, (if p = 3 then mirEx3 r * Real.log 3 else 0) ≤ 2 * extraBound r m := by
    have hE3nn : 0 ≤ mirEx3 r * Real.log 3 := by
      unfold mirEx3
      have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      positivity
    have h1 : ∑ p ∈ P, (if p = 3 then mirEx3 r * Real.log 3 else 0) ≤ mirEx3 r * Real.log 3 := by
      rw [← Finset.sum_filter]
      have : (P.filter (fun p => p = 3)) ⊆ {3} := by
        intro x hx; simp at hx ⊢; exact hx.2
      calc _ ≤ ∑ p ∈ ({3} : Finset ℕ), mirEx3 r * Real.log 3 :=
            Finset.sum_le_sum_of_subset_of_nonneg this (fun _ _ _ => hE3nn)
        _ = _ := by simp
    refine h1.trans ?_
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hex2 : mirEx3 r ≤ mirEx2 r := by
      unfold mirEx3 mirEx2
      have : (0 : ℝ) ≤ ((r + r / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hext : mirEx2 r * Real.log 2 ≤ extraBound r m := by
      unfold extraBound mirEx2
      have h2 : 0 ≤ ((Nat.sqrt (4 * (r + 2 * m)) : ℝ) + 1) *
          (2 * (r + m : ℝ) * (Nat.log 2 (4 * (r + 2 * m)) : ℝ) * Real.log (4 * (r + 2 * m) + 5)) := by
        have : 0 ≤ Real.log (4 * ((r : ℝ) + 2 * m) + 5) := Real.log_nonneg (by
          have : (0 : ℝ) ≤ 4 * ((r : ℝ) + 2 * m) := by positivity
          linarith)
        positivity
      push_cast
      nlinarith
    have hl3 := log3_le
    calc mirEx3 r * Real.log 3 ≤ mirEx2 r * (2 * Real.log 2) := by
          apply mul_le_mul hex2 hl3 (Real.log_nonneg (by norm_num)) hlam
      _ = 2 * (mirEx2 r * Real.log 2) := by ring
      _ ≤ 2 * extraBound r m := by linarith
  -- the level-1 sums
  have hg : ∑ p ∈ P, (if p = 2 ∨ p = 3 then 0 else WG mirNInst r p * Real.log p) ≤
      clsSum 4 (1 : ZMod 4) (WG mirNInst r) 0 (5 * r) +
        clsSum 4 (3 : ZMod 4) (WG mirNInst r) 0 (5 * r / 3) := by
    have hle : ∑ p ∈ P, (if p = 2 ∨ p = 3 then 0 else WG mirNInst r p * Real.log p) ≤
        ∑ p ∈ P, (if p = 2 then (0 : ℝ) else WG mirNInst r p * Real.log p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpp := (Finset.mem_filter.mp hp).2
      have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
      have hW := mirW_nonneg r p
      by_cases h2 : p = 2
      · simp [h2]
      · by_cases h3 : p = 3
        · rw [if_pos (Or.inr h3), if_neg h2]; exact mul_nonneg hW hlog
        · simp [h2, h3]
    refine hle.trans ?_
    have hPe : P = (Finset.range (4 * (r + 2 * m) + 5 + 1)).filter Nat.Prime := rfl
    rw [hPe, mir_g_sum_eq r (4 * (r + 2 * m) + 5)]
    have t1 := clsSum_le_of_tail (M := 4) (1 : ZMod 4) (WG mirNInst r) (mirW_nonneg r)
      (B := 4 * (r + 2 * m) + 5) (B' := 5 * r) (by
        intro p hp1 hpp hpc
        have h1 := cls4_mod1 hpc
        have : XG mirNInst r p = 0 := mir_tail1 r p hpp (by omega) h1 hp1
        simp [WG, this])
    have t3 := clsSum_le_of_tail (M := 4) (3 : ZMod 4) (WG mirNInst r) (mirW_nonneg r)
      (B := 4 * (r + 2 * m) + 5) (B' := 5 * r / 3) (by
        intro p hp1 hpp hpc
        have h3 := cls4_mod3 hpc
        have : XG mirNInst r p = 0 := mir_tail3 r p hpp (by omega) h3 hp1
        simp [WG, this])
    linarith
  linarith

end CatalanFrames.LambdaMirrorHybrid
