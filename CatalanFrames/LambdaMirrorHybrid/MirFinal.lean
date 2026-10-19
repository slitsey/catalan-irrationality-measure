module

public import CatalanFrames.LambdaMirrorHybrid.MirTrop
public import CatalanCore.Arith.Hybrid.Extra

@[expose] public section

/-!
# Mirror: `log Dhyb ≤ extra + level-1 class sums` (bad primes `{2, 3}`)

Same assembly as `CatalanFrames/Lambda/HybFinal.lean`, with the second bad prime `3`: its contribution is
bounded by the crude all-levels bound and is at most twice the prime-`2` term (`log 3 < 2 log 2`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
  CatalanFrames.HybCommon

namespace CatalanFrames.LambdaMirrorHybrid

lemma mir_Bnd (r m : ℕ) : Bnd mirNInst r m = 4 * (r + 2 * m) + 6 := by
  show mirCD.L * (r + 2 * m) + 3 + mirCD.bad.sup id = _
  have : mirCD.bad.sup id = 3 := by
    show ({2, 3} : Finset ℕ).sup id = 3
    decide
  rw [this]
  show 4 * (r + 2 * m) + 3 + 3 = _
  ring

lemma mir_cOf2 : cOf mirNInst 2 = 4 := by
  show (16 : ℕ).factorization 2 = 4
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
  simp

lemma mir_cOf3 : cOf mirNInst 3 = 0 := by
  show (16 : ℕ).factorization 3 = 0
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
  simp

lemma mir_cOf_good {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : cOf mirNInst p = 0 :=
  cOf_eq_zero mirNInst hp (by simpa [mirNInst, mirInst, HybInst.neg, HybInst.ofSing,
    ContentData.neg, mirCD] using And.intro h2 h3)

/-- Level-count for non-bad primes. -/
noncomputable def cntM (r m p : ℕ) : ℕ :=
  ((Finset.Icc 2 (Elev mirNInst r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card

/-- Level-count for the bad prime `3`. -/
noncomputable def cnt3 (r m : ℕ) : ℕ :=
  ((Finset.Icc 1 (Elev mirNInst r m)).filter
    (fun e => 3 ^ e ≤ 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m))).card

/-- Level-count for the bad prime `2`. -/
noncomputable def cnt2 (r m : ℕ) : ℕ :=
  ((Finset.Icc 1 (Elev mirNInst r m)).filter
    (fun e => 2 ^ e ≤ 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m))).card

lemma cntM_le (r m p : ℕ) (hp : p.Prime) : cntM r m p ≤ Nat.log 2 (4 * (r + 2 * m)) := by
  unfold cntM
  calc _ ≤ (Finset.Icc 2 (Nat.log 2 (4 * (r + 2 * m)))).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
        have h2 := Finset.mem_Icc.mp he1
        refine Finset.mem_Icc.mpr ⟨h2.1, ?_⟩
        apply Nat.le_log_of_pow_le (by norm_num)
        exact (Nat.pow_le_pow_left hp.two_le e).trans he2
    _ ≤ _ := by simp

lemma cntM_zero (r m p : ℕ) (hp : p.Prime) (h : 4 * (r + 2 * m) < p ^ 2) : cntM r m p = 0 := by
  unfold cntM
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hle
  have h2 := (Finset.mem_Icc.mp he).1
  have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos h2
  omega

lemma cnt_bad_le (b r m : ℕ) (hb : 2 ≤ b) :
    ((Finset.Icc 1 (Elev mirNInst r m)).filter
      (fun e => b ^ e ≤ 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m))).card ≤
      Nat.log 2 (4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m)) := by
  calc _ ≤ (Finset.Icc 1 (Nat.log 2 (4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m)))).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
        have h2 := Finset.mem_Icc.mp he1
        refine Finset.mem_Icc.mpr ⟨h2.1, ?_⟩
        apply Nat.le_log_of_pow_le (by norm_num)
        exact (Nat.pow_le_pow_left hb e).trans he2
    _ ≤ _ := by simp

/-- The extra weight of the prime `2`. -/
noncomputable def mirEx2 (r : ℕ) : ℝ :=
  (4 + 2 * (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℝ)) *
    ((r + r / 8 : ℕ) : ℝ)

/-- The extra weight of the prime `3`. -/
noncomputable def mirEx3 (r : ℕ) : ℝ :=
  2 * ((r + r / 8 : ℕ) : ℝ) *
    (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℝ)

/-- The per-prime bound: the bad primes `2, 3` and higher levels go to the extra terms. -/
lemma tropExp_mir_le (r p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) :
    (tropExp mirNInst r (r / 8) p : ℝ) ≤
      (if p = 2 then mirEx2 r else 0) + (if p = 3 then mirEx3 r else 0) +
      ((2 * (r + r / 8) * cntM r (r / 8) p : ℕ) : ℝ) +
      (if p = 2 ∨ p = 3 then 0 else WG mirNInst r p) := by
  have hn2 : (0 : ℝ) ≤ ((2 * (r + r / 8) * cntM r (r / 8) p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE2 : 0 ≤ mirEx2 r := by unfold mirEx2; positivity
  have hE3 : 0 ≤ mirEx3 r := by unfold mirEx3; positivity
  by_cases h2 : p = 2
  · subst h2
    have hb := tropExp_le_bad mirNInst r (r / 8) 2
    rw [mir_cOf2] at hb
    have hcB := cnt_bad_le 2 r (r / 8) (le_refl 2)
    have h1 : tropExp mirNInst r (r / 8) 2 ≤
        4 * (r + r / 8) + 2 * (r + r / 8) *
          Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) := by
      refine hb.trans ?_
      have := Nat.mul_le_mul_left (2 * (r + r / 8)) hcB
      show 4 * (r + r / 8) + 2 * (r + r / 8) * ((Finset.Icc 1 (Elev mirNInst r (r / 8))).filter
        (fun e => 2 ^ e ≤ 4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8)))).card ≤ _
      omega
    have h1' : (tropExp mirNInst r (r / 8) 2 : ℝ) ≤
        4 * (r + r / 8 : ℕ) + 2 * (r + r / 8 : ℕ) *
          (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℕ) := by
      exact_mod_cast h1
    simp only [if_true, mirEx2]
    simp only [show (2 : ℕ) ≠ 3 by norm_num, if_false, true_or]
    push_cast at h1' hn2 ⊢
    nlinarith
  by_cases h3 : p = 3
  · subst h3
    have hb := tropExp_le_bad mirNInst r (r / 8) 3
    rw [mir_cOf3] at hb
    have hcB := cnt_bad_le 3 r (r / 8) (by norm_num)
    have h1 : tropExp mirNInst r (r / 8) 3 ≤
        2 * (r + r / 8) *
          Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) := by
      refine hb.trans ?_
      have := Nat.mul_le_mul_left (2 * (r + r / 8)) hcB
      show 0 * (r + r / 8) + 2 * (r + r / 8) * ((Finset.Icc 1 (Elev mirNInst r (r / 8))).filter
        (fun e => 3 ^ e ≤ 4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8)))).card ≤ _
      omega
    have h1' : (tropExp mirNInst r (r / 8) 3 : ℝ) ≤
        2 * (r + r / 8 : ℕ) *
          (Nat.log 2 (4 * (r + 2 * (r / 8)) * (r + 2 * (r / 8)) + (r + 2 * (r / 8))) : ℕ) := by
      exact_mod_cast h1
    simp only [show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true, mirEx3, or_true]
    push_cast at h1' hn2 ⊢
    linarith
  · have hb := tropExp_le mirNInst r (r / 8) p hr hp (by
      simpa [mirNInst, mirInst, HybInst.neg, HybInst.ofSing, ContentData.neg, mirCD] using
        And.intro h2 h3)
    rw [mir_cOf_good hp h2 h3, zero_mul, zero_add] at hb
    simp only [if_neg h2, if_neg h3, if_neg (not_or.mpr ⟨h2, h3⟩)]
    have hb' : (tropExp mirNInst r (r / 8) p : ℝ) ≤
        ((tropVal (HW mirNInst.lev p r (r / 8)) +
          2 * (r + r / 8) * cntM r (r / 8) p : ℕ) : ℝ) := by
      exact_mod_cast hb
    push_cast at hb' ⊢
    have e : (tropVal (HW mirNInst.lev p r (r / 8)) : ℝ) = WG mirNInst r p := rfl
    linarith

end CatalanFrames.LambdaMirrorHybrid
