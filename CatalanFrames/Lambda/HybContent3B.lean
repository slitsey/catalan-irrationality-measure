module

public import CatalanFrames.Lambda.HybContent3
public import CatalanFrames.Lambda.HybContent2B

@[expose] public section

/-!
# λ: `lam_content_deficit3`

`lam_log_DhybT_le3`: `log DhybT ≤ extraBound + clsSum₃(lamWT3) + clsSum₁(lamWT3) - ∑ δ log p`
(the proof of `lam_log_DhybT_le` with `Tfun3`).  `lam_content_deficit3` then sums the seven deficit
families E (class 1), E (class 3), B, C5, C7, GK (class 3), GK (class 1) with `defSum_ge`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma g_sum_eqT3 (r : ℕ) (B : ℕ) :
    ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime,
        (if p = 2 then (0 : ℝ) else lamWT3 r p * Real.log p) =
      clsSum 4 (3 : ZMod 4) (lamWT3 r) 0 B + clsSum 4 (1 : ZMod 4) (lamWT3 r) 0 B := by
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
      · rw [if_pos hp, if_neg h2, if_pos ⟨hp, h3⟩, if_neg (fun h => h1 h.2), add_zero]
      · rw [if_pos hp, if_neg h2, if_neg (fun h => h3 h.2), if_pos ⟨hp, h1⟩, zero_add]
  · simp [hp]

lemma lamWT3_tail3 {r p : ℕ} (hr : 16 ≤ r) (hp : p.Prime) (h3 : p % 4 = 3) (ht : 5 * r < p) :
    lamWT3 r p = 0 := by
  have h0 := lamWT2_tail3 hr hp h3 ht
  obtain ⟨h7, hk⟩ := e7_zero (p := p) hr (Or.inr (by omega))
  unfold lamWT3
  rw [h0, h7, hk]; simp

lemma lamWT3_tail1 {r p : ℕ} (hr : 16 ≤ r) (hp : p.Prime) (h1 : p % 4 = 1) (ht : 5 * r / 3 < p) :
    lamWT3 r p = 0 := by
  have h0 := lamWT2_tail1 hr hp h1 ht
  obtain ⟨h7, hk⟩ := e7_zero (p := p) hr (Or.inr (by omega))
  unfold lamWT3
  rw [h0, h7, hk]; simp

theorem lam_log_DhybT_le3 {r : ℕ} (hr : 16 ≤ r) {δ : ℕ → ℕ}
    (h : DefHypT lamInst r (r / 8) (Tfun3 r) δ) :
    Real.log (DhybT lamInst r (r / 8) (Tfun3 r) δ) ≤ extraBound r (r / 8) +
      clsSum 4 (3 : ZMod 4) (lamWT3 r) 0 (5 * r) + clsSum 4 (1 : ZMod 4) (lamWT3 r) 0 (5 * r / 3) -
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (δ p : ℝ) * Real.log p := by
  rw [log_DhybT lamInst r (r / 8) h]
  have hr1 : 1 ≤ r := by omega
  suffices hS : ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      (Tfun3 r p : ℝ) * Real.log p ≤ extraBound r (r / 8) +
      clsSum 4 (3 : ZMod 4) (lamWT3 r) 0 (5 * r) + clsSum 4 (1 : ZMod 4) (lamWT3 r) 0 (5 * r / 3) by
    linarith
  rw [lam_Bnd]
  set P := (Finset.range (4 * (r + 2 * (r / 8)) + 5)).filter Nat.Prime with hP
  have hpt : ∀ p ∈ P, (Tfun3 r p : ℝ) * Real.log p ≤
      ((if p = 2 then lamEx2 r else 0) + ((2 * (r + r / 8) * cntG r (r / 8) p : ℕ) : ℝ)) * Real.log p +
        (if p = 2 then 0 else lamWT3 r p * Real.log p) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have h1 := tropExp_lam_le r p hr1 hpp
    have hlw : lamW r p ≤ lamWT r p := le_max_left _ _
    have hlw2 : lamW r p ≤ lamWT3 r p := hlw.trans ((le_max_left _ _).trans (le_max_left _ _))
    have hlex : 0 ≤ lamEx2 r := by unfold lamEx2; positivity
    have hcnt : (0 : ℝ) ≤ ((2 * (r + r / 8) * cntG r (r / 8) p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hwt := lamWT3_nonneg r p
    have hT : (Tfun3 r p : ℝ) ≤ (if p = 2 then lamEx2 r else 0) +
        ((2 * (r + r / 8) * cntG r (r / 8) p : ℕ) : ℝ) + (if p = 2 then 0 else lamWT3 r p) := by
      unfold Tfun3 Tfun2 Tfun
      push_cast
      push_cast at h1 hcnt
      have hmono : lamWT r p ≤ lamWT3 r p := (le_max_left _ _).trans (le_max_left _ _)
      have hz := e7_zero (p := 2) hr (Or.inl (by omega))
      refine max_le (max_le (max_le ?_ ?_) ?_) (max_le ?_ ?_)
      · by_cases h2 : p = 2
        · simp only [if_pos h2] at h1 ⊢; linarith
        · simp only [if_neg h2] at h1 ⊢; linarith
      · by_cases h2 : p = 2
        · subst h2; rw [eN_zero_two hr]; simp only [if_pos rfl]; push_cast; linarith
        · have : (eN r p : ℝ) ≤ lamWT r p := le_max_right _ _
          simp only [if_neg h2]; linarith
      · by_cases h2 : p = 2
        · subst h2; rw [eC5_two r]; simp only [if_pos rfl]; push_cast; linarith
        · have : (eC5 r p : ℝ) ≤ lamWT2 r p := le_max_right _ _
          have h' : lamWT2 r p ≤ lamWT3 r p := le_max_left _ _
          simp only [if_neg h2]; linarith
      · by_cases h2 : p = 2
        · subst h2; rw [hz.1]; simp only [if_pos rfl]; push_cast; linarith
        · have : (eC7 r p : ℝ) ≤ lamWT3 r p := (le_max_left _ _).trans (le_max_right _ _)
          simp only [if_neg h2]; linarith
      · by_cases h2 : p = 2
        · subst h2; rw [hz.2]; simp only [if_pos rfl]; push_cast; linarith
        · have : (eGK r p : ℝ) ≤ lamWT3 r p := (le_max_right _ _).trans (le_max_right _ _)
          simp only [if_neg h2]; linarith
    by_cases h2 : p = 2
    · simp only [if_pos h2] at hT ⊢
      nlinarith
    · simp only [if_neg h2] at hT ⊢
      nlinarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  have hex : ∑ p ∈ P, ((if p = 2 then lamEx2 r else 0) +
      ((2 * (r + r / 8) * cntG r (r / 8) p : ℕ) : ℝ)) * Real.log p ≤ extraBound r (r / 8) := by
    have hlam : 0 ≤ lamEx2 r := by unfold lamEx2; positivity
    have := ex_sum_bound r (r / 8) (4 * (r + 2 * (r / 8)) + 5) (lamEx2 r) hlam
      (fun p => 2 * (r + r / 8) * cntG r (r / 8) p) (Nat.log 2 (4 * (r + 2 * (r / 8)))) le_rfl
      (fun p hp => by
        have := cntG_le r (r / 8) p hp
        exact Nat.mul_le_mul_left _ this)
      (fun p hp h => by simp [cntG_zero r (r / 8) p hp h])
    refine this.trans (le_of_eq ?_)
    unfold extraBound lamEx2
    push_cast
    ring
  have hg : ∑ p ∈ P, (if p = 2 then (0 : ℝ) else lamWT3 r p * Real.log p) ≤
      clsSum 4 (3 : ZMod 4) (lamWT3 r) 0 (5 * r) + clsSum 4 (1 : ZMod 4) (lamWT3 r) 0 (5 * r / 3) := by
    have hP' : P = (Finset.range ((4 * (r + 2 * (r / 8)) + 4) + 1)).filter Nat.Prime := by rfl
    rw [hP', g_sum_eqT3 r (4 * (r + 2 * (r / 8)) + 4)]
    have t3 := clsSum_le_of_tail (M := 4) (3 : ZMod 4) (lamWT3 r) (lamWT3_nonneg r)
      (B := 4 * (r + 2 * (r / 8)) + 4) (B' := 5 * r) (by
        intro p hp1 hpp hpc
        exact lamWT3_tail3 hr hpp (cls4_mod3 hpc) hp1)
    have t1 := clsSum_le_of_tail (M := 4) (1 : ZMod 4) (lamWT3 r) (lamWT3_nonneg r)
      (B := 4 * (r + 2 * (r / 8)) + 4) (B' := 5 * r / 3) (by
        intro p hp1 hpp hpc
        exact lamWT3_tail1 hr hpp (cls4_mod1 hpc) hp1)
    linarith
  linarith

end CatalanFrames.Lambda
