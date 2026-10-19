module

public import CatalanFrames.Lambda.HybContent

@[expose] public section

/-!
# λ: `log Dhyb ≤ (Λ_trop' + ε) r²`

Assembly: `log Dhyb = ∑_p tropExp log p`, split into the prime `2` and higher levels (negligible,
`Extra.lean`) and the level-1 sums over the classes `3` and `1` mod 4 (`class3_total`,
`class1_total`).  The constant of this file is the simplified `Λ_trop' = 1579/420`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-- `Bnd` for λ. -/
lemma lam_Bnd (r m : ℕ) : Bnd lamInst r m = 4 * (r + 2 * m) + 5 := by
  show lamCD.L * (r + 2 * m) + 3 + lamCD.bad.sup id = _
  have : lamCD.bad.sup id = 2 := by
    show ({2} : Finset ℕ).sup id = 2
    simp
  rw [this]
  show 4 * (r + 2 * m) + 3 + 2 = _
  ring

lemma lam_cOf2 : cOf lamInst 2 = 4 := by
  show (16 : ℕ).factorization 2 = 4
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
  simp

lemma lam_cOf_odd {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : cOf lamInst p = 0 :=
  cOf_eq_zero lamInst hp (by simpa [lamInst, HybInst.ofSing, lamCD] using h2)

/-- Level-count for odd primes. -/
noncomputable def cntG (r m p : ℕ) : ℕ :=
  ((Finset.Icc 2 (Elev lamInst r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card

noncomputable def cntB (r m : ℕ) : ℕ :=
  ((Finset.Icc 1 (Elev lamInst r m)).filter
    (fun e => 2 ^ e ≤ 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m))).card

lemma cntG_le (r m p : ℕ) (hp : p.Prime) : cntG r m p ≤ Nat.log 2 (4 * (r + 2 * m)) := by
  unfold cntG
  calc _ ≤ (Finset.Icc 2 (Nat.log 2 (4 * (r + 2 * m)))).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
        have h2 := Finset.mem_Icc.mp he1
        refine Finset.mem_Icc.mpr ⟨h2.1, ?_⟩
        apply Nat.le_log_of_pow_le (by norm_num)
        exact (Nat.pow_le_pow_left hp.two_le e).trans he2
    _ ≤ _ := by simp

lemma cntG_zero (r m p : ℕ) (hp : p.Prime) (h : 4 * (r + 2 * m) < p ^ 2) : cntG r m p = 0 := by
  unfold cntG
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hle
  have h2 := (Finset.mem_Icc.mp he).1
  have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos h2
  omega

lemma cntB_le (r m : ℕ) :
    cntB r m ≤ Nat.log 2 (4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m)) := by
  unfold cntB
  calc _ ≤ (Finset.Icc 1 (Nat.log 2 (4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m)))).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
        have h2 := Finset.mem_Icc.mp he1
        refine Finset.mem_Icc.mpr ⟨h2.1, ?_⟩
        exact Nat.le_log_of_pow_le (by norm_num) he2
    _ ≤ _ := by simp

/-- The extra weight of the prime `2`. -/
noncomputable def lamEx2 (r : ℕ) : ℝ :=
  (4 + 2 * (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℝ)) *
    ((r + r / 8 : ℕ) : ℝ)

/-- The per-prime bound: prime `2` and higher levels go to the extra terms. -/
lemma tropExp_lam_le (r p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) :
    (tropExp lamInst r (r / 8) p : ℝ) ≤
      (if p = 2 then lamEx2 r else 0) +
      ((2 * (r + r / 8) * cntG r (r / 8) p : ℕ) : ℝ) + (if p = 2 then 0 else lamW r p) := by
  by_cases h2 : p = 2
  · subst h2
    have hb := tropExp_le_bad lamInst r (r / 8) 2
    rw [lam_cOf2] at hb
    have hcB : ((Finset.Icc 1 (Elev lamInst r (r / 8))).filter
        (fun e => 2 ^ e ≤ lamInst.Ebd (r + 2 * (r / 8)) + (r + 2 * (r / 8)))).card ≤
        Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) := cntB_le r _
    have h1 : tropExp lamInst r (r / 8) 2 ≤
        4 * (r + r / 8) + 2 * (r + r / 8) *
          Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) := by
      refine hb.trans ?_
      have := Nat.mul_le_mul_left (2 * (r + r / 8)) hcB
      omega
    have h1' : (tropExp lamInst r (r / 8) 2 : ℝ) ≤
        4 * (r + r / 8 : ℕ) + 2 * (r + r / 8 : ℕ) *
          (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℕ) := by
      exact_mod_cast h1
    simp only [if_true, lamEx2]
    have h0 : (0 : ℝ) ≤ ((2 * (r + r / 8) * cntG r (r / 8) 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at h1' h0 ⊢
    nlinarith
  · have hb := tropExp_le lamInst r (r / 8) p hr hp
      (by simpa [lamInst, HybInst.ofSing, lamCD] using h2)
    rw [lam_cOf_odd hp h2, zero_mul, zero_add] at hb
    simp only [if_neg h2]
    have hb' : (tropExp lamInst r (r / 8) p : ℝ) ≤
        ((tropVal (HW lamInst.lev p r (r / 8)) + 2 * (r + r / 8) * cntG r (r / 8) p : ℕ) : ℝ) := by
      exact_mod_cast hb
    push_cast at hb' ⊢
    have e : (tropVal (HW lamInst.lev p r (r / 8)) : ℝ) = lamW r p := rfl
    linarith


lemma cast4_two : (2 : ZMod 4) ≠ 3 ∧ (2 : ZMod 4) ≠ 1 := by decide

lemma prime_class4 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ((p : ZMod 4) = 3 ∧ (p : ZMod 4) ≠ 1) ∨ ((p : ZMod 4) = 1 ∧ (p : ZMod 4) ≠ 3) := by
  have hodd := hp.eq_two_or_odd.resolve_left h2
  have : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases this with h | h
  · right
    have e : (p : ZMod 4) = ((p % 4 : ℕ) : ZMod 4) := (ZMod.natCast_mod p 4).symm
    rw [e, h]; decide
  · left
    have e : (p : ZMod 4) = ((p % 4 : ℕ) : ZMod 4) := (ZMod.natCast_mod p 4).symm
    rw [e, h]; decide

/-- The level-1 part of the sum is the sum of the two class sums. -/
lemma g_sum_eq (r : ℕ) (B : ℕ) :
    ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime,
        (if p = 2 then (0 : ℝ) else lamW r p * Real.log p) =
      clsSum 4 (3 : ZMod 4) (lamW r) 0 B + clsSum 4 (1 : ZMod 4) (lamW r) 0 B := by
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

/-- **Level-1 plus negligible terms.** -/
theorem lam_log_Dhyb_le (r : ℕ) (hr : 1 ≤ r) :
    Real.log (Dhyb lamInst r (r / 8)) ≤ extraBound r (r / 8) +
      clsSum 4 (3 : ZMod 4) (lamW r) 0 (5 * r) + clsSum 4 (1 : ZMod 4) (lamW r) 0 (5 * r / 3) := by
  set m := r / 8 with hm
  rw [log_Dhyb, lam_Bnd]
  set P := (Finset.range (4 * (r + 2 * m) + 5)).filter Nat.Prime with hP
  have hpt : ∀ p ∈ P, (tropExp lamInst r m p : ℝ) * Real.log p ≤
      ((if p = 2 then lamEx2 r else 0) + ((2 * (r + r / 8) * cntG r m p : ℕ) : ℝ)) * Real.log p +
        (if p = 2 then 0 else lamW r p * Real.log p) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have h := tropExp_lam_le r p hr hpp
    by_cases h2 : p = 2
    · simp only [if_pos h2] at h ⊢
      nlinarith
    · simp only [if_neg h2] at h ⊢
      nlinarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  have hex : ∑ p ∈ P, ((if p = 2 then lamEx2 r else 0) +
      ((2 * (r + r / 8) * cntG r m p : ℕ) : ℝ)) * Real.log p ≤ extraBound r m := by
    have hlam : 0 ≤ lamEx2 r := by unfold lamEx2; positivity
    have := ex_sum_bound r m (4 * (r + 2 * m) + 5) (lamEx2 r) hlam
      (fun p => 2 * (r + r / 8) * cntG r m p) (Nat.log 2 (4 * (r + 2 * m))) le_rfl
      (fun p hp => by
        have := cntG_le r m p hp
        exact Nat.mul_le_mul_left _ this)
      (fun p hp h => by simp [cntG_zero r m p hp h])
    refine this.trans (le_of_eq ?_)
    unfold extraBound lamEx2
    push_cast
    ring
  have hg : ∑ p ∈ P, (if p = 2 then (0 : ℝ) else lamW r p * Real.log p) ≤
      clsSum 4 (3 : ZMod 4) (lamW r) 0 (5 * r) + clsSum 4 (1 : ZMod 4) (lamW r) 0 (5 * r / 3) := by
    have hP' : P = (Finset.range ((4 * (r + 2 * m) + 4) + 1)).filter Nat.Prime := by rfl
    rw [hP', g_sum_eq r (4 * (r + 2 * m) + 4)]
    have t3 := clsSum_le_of_tail (M := 4) (3 : ZMod 4) (lamW r) (lamW_nonneg r)
      (B := 4 * (r + 2 * m) + 4) (B' := 5 * r) (by
        intro p hp1 hpp hpc
        have h3 := cls4_mod3 hpc
        have : lamX r p = 0 := lam_tail3 r p hpp h3 hp1
        simp [lamW, this])
    have t1 := clsSum_le_of_tail (M := 4) (1 : ZMod 4) (lamW r) (lamW_nonneg r)
      (B := 4 * (r + 2 * m) + 4) (B' := 5 * r / 3) (by
        intro p hp1 hpp hpc
        have h1 := cls4_mod1 hpc
        have : lamX r p = 0 := lam_tail1 r p hpp h1 hp1
        simp [lamW, this])
    linarith
  linarith

/-- **The λ hybrid content theorem, simplified route.**  `Λ_trop' = 1579/420 ≈ 3.75952`. -/
theorem lam_content_trop {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, Real.log (Dhyb lamInst r (r / 8)) ≤ (1579 / 420 + ε) * (r : ℝ) ^ 2 := by
  have h3 := class3_total (ε := ε / 4) (by positivity)
  have h1 := class1_total (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 2) (by positivity)
  filter_upwards [h3, h1, hx, eventually_ge_atTop 1] with r hr3 hr1 hrx hr0
  have hmain := lam_log_Dhyb_le r hr0
  have hex := hrx (r / 8) (Nat.div_le_self r 8)
  have hc := lam_const
  have e : (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 4) + listInt l3) / 2 + ε / 4) +
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 4) + listInt l1) / 2 + ε / 4) =
      (r : ℝ) ^ 2 * (1579 / 420 + ε / 2) := by
    rw [← mul_add]
    congr 1
    linarith
  nlinarith [hmain, hr3, hr1, hex, e]

end CatalanFrames.Lambda
