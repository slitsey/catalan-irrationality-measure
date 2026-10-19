module

public import CatalanFrames.HybCommon.Final
public import CatalanCore.Arith.Hybrid.BorderSum
public import CatalanCore.Rect.PairBridgeTop
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# The border cost is negligible, and `Mem2Content` from `DefBothG` families (generic)

`topC_sum_G`: `∑_{p < Bnd} topC · log p = O(r log r) ≤ ε r²` eventually (`m = r/8`), for any hybrid instance
whose levels satisfy `Bnd ≤ 4(r+2m)+6`, `Elev = 4N²+N` and whose normalisation only involves the prime `2`
(`cOf 2 = 4`).  `mem2Content_of_both_G`: the bordering step.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanFrames.Lambda

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- Crude bound for any `(r, m)`. -/
lemma topC_sum_aux_G (I : HybInst Fr)
    (hcO : ∀ p : ℕ, p.Prime → (cOf I p : ℝ) * Real.log p ≤ if p = 2 then 4 * Real.log 2 else 0)
    (r m : ℕ) :
    ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime,
        (topC I r m p : ℝ) * Real.log p ≤
      8 + (Bnd I r m : ℝ) *
        (4 * Real.log (Elev I r m) + Real.log (Bnd I r m)) := by
  set P := (Finset.range (Bnd I r m)).filter Nat.Prime with hP
  set B := Bnd I r m with hB
  set E := Elev I r m with hE
  have hlE : 0 ≤ Real.log E := Real.log_natCast_nonneg E
  have hpt : ∀ p ∈ P, (topC I r m p : ℝ) * Real.log p ≤
      2 * ((if p = 2 then (4 : ℝ) * Real.log 2 else 0)) + (4 * Real.log E + Real.log B) := by
    intro p hp
    have hp' := Finset.mem_filter.1 hp
    have hlt : p < B := Finset.mem_range.1 hp'.1
    have h1 := topC_log_le I r m hp'.2.one_lt
    have h2 : Real.log p ≤ Real.log B :=
      Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hlt.le)
    have h3 : (cOf I p : ℝ) * Real.log p ≤ if p = 2 then (4 : ℝ) * Real.log 2 else 0 := by
      by_cases h : p = 2
      · subst h; simpa using hcO 2 Nat.prime_two
      · simpa [h] using hcO p hp'.2
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_ite_eq'] at hsum
  have hcard : (P.card : ℝ) ≤ B := by
    have : P.card ≤ B := (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_range _).le
    exact_mod_cast this
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlB : 0 ≤ Real.log B := Real.log_natCast_nonneg B
  have hif : (if (2 : ℕ) ∈ P then (4 : ℝ) * Real.log 2 else 0) ≤ 4 := by
    split_ifs
    · linarith
    · norm_num
  rw [nsmul_eq_mul] at hsum
  have : (P.card : ℝ) * (4 * Real.log E + Real.log B) ≤ B * (4 * Real.log E + Real.log B) :=
    mul_le_mul_of_nonneg_right hcard (by linarith)
  linarith

theorem topC_sum_G (I : HybInst Fr)
    (hcO : ∀ p : ℕ, p.Prime → (cOf I p : ℝ) * Real.log p ≤ if p = 2 then 4 * Real.log 2 else 0)
    (hBd : ∀ r m, Bnd I r m ≤ 4 * (r + 2 * m) + 6)
    (hEl : ∀ r m, Elev I r m = 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m))
    (hBpos : ∀ r m, 0 < Bnd I r m) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ r : ℕ in Filter.atTop,
    ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
      (topC I r (r / 8) p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2 := by
  have hl := lam_log_le_eventually (e := ε / 252) (by positivity)
  have hbig : ∀ᶠ r : ℕ in atTop, 16 / ε ≤ (r : ℝ) ^ 2 := by
    have : Tendsto (fun r : ℕ => (r : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop _
  filter_upwards [hl, hbig, eventually_ge_atTop 18] with r hr hr2 hr18
  refine (topC_sum_aux_G I hcO r (r / 8)).trans ?_
  have hBd := hBd r (r / 8)
  set m := r / 8 with hm
  have hm8 : 8 * m ≤ r := by omega
  have hN : r + 2 * m ≤ 2 * r := by omega
  have hrR : (18 : ℝ) ≤ r := by exact_mod_cast hr18
  have hBr : Bnd I r m ≤ 9 * r := by omega
  have hBr2 : Bnd I r m ≤ r ^ 2 := by nlinarith
  have hEr : Elev I r m ≤ r ^ 3 := by
    have : Elev I r m = 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m) := hEl r m
    rw [this]
    have h1 : 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m) ≤ 4 * (2 * r) * (2 * r) + 2 * r :=
      Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left _ hN) hN) hN
    nlinarith
  have hBpos : (0 : ℝ) < Bnd I r m := by exact_mod_cast hBpos r m
  have hEpos : (0 : ℝ) < Elev I r m := by
    have : Elev I r m = 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m) := hEl r m
    rw [this]; positivity
  have hlogE : Real.log (Elev I r m) ≤ 3 * Real.log r := by
    have hc : (Elev I r m : ℝ) ≤ (r : ℝ) ^ 3 := by exact_mod_cast hEr
    have := Real.log_le_log hEpos hc
    rwa [Real.log_pow] at this
  have hlogB : Real.log (Bnd I r m) ≤ 2 * Real.log r := by
    have hc : (Bnd I r m : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast hBr2
    have := Real.log_le_log hBpos hc
    rwa [Real.log_pow] at this
  have hBR : (Bnd I r m : ℝ) ≤ 9 * r := by exact_mod_cast hBr
  have hlr : 0 ≤ Real.log r := Real.log_natCast_nonneg r
  have hr0 : (0 : ℝ) < r := by linarith
  have h16 : 8 ≤ ε / 2 * (r : ℝ) ^ 2 := by
    have := (div_le_iff₀ hε).1 hr2
    nlinarith
  have hmain : (Bnd I r m : ℝ) * (4 * Real.log (Elev I r m) + Real.log (Bnd I r m))
      ≤ (9 * r) * (14 * Real.log r) := by
    have a1 := Real.log_natCast_nonneg (Elev I r m)
    have a2 := Real.log_natCast_nonneg (Bnd I r m)
    exact mul_le_mul hBR (by linarith) (by linarith) (by positivity)
  have : (9 * (r : ℝ)) * (14 * Real.log r) ≤ ε / 2 * (r : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 126 * r by positivity)
    nlinarith
  linarith


/-- **Bordering step**: a content bound for a simultaneous member-1/member-2 deficit family gives
`Mem2Content` (the border cost is `O(r log r)`). -/
theorem mem2Content_of_both_G (I : HybInst Fr) {Λ0 Λ : ℝ} (hΛ : Λ0 ≤ Λ)
    (hsum : ∀ ε > 0, ∀ᶠ r : ℕ in atTop,
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
        (topC I r (r / 8) p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2)
    (h : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r / 8) T δ) ≤ (Λ0 + ε) * (r : ℝ) ^ 2) :
    Mem2Content Fr Λ := by
  refine mem2Content_of_top I ?_
  intro ε hε
  filter_upwards [h (ε / 2) (by positivity), hsum (ε / 2) (by positivity)] with r
    ⟨T, δ, hδ, hlog⟩ hS
  refine ⟨T, δ, hδ.2, ?_⟩
  rw [log_DhybTop I r (r / 8) hδ.1]
  nlinarith [hlog, hS, mul_le_mul_of_nonneg_right hΛ (sq_nonneg (r : ℝ))]

end CatalanFrames.HybCommon
