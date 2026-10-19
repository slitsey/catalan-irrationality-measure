module

public import CatalanFrames.Lambda.HybFinal
public import CatalanCore.Arith.Hybrid.BorderSum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# λ: the border cost is negligible (MEM2C)

`lam_topC_sum`: `∑_{p < Bnd} topC · log p = O(r log r) ≤ ε r²` eventually (`m = r/8`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma lam_log_le_eventually {e : ℝ} (he : 0 < e) :
    ∀ᶠ r : ℕ in atTop, Real.log r ≤ e * r := by
  have h := Real.isLittleO_log_id_atTop.bound he
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with r hr
  simp only [id, Real.norm_eq_abs] at hr
  exact (le_abs_self _).trans (hr.trans (by rw [abs_of_nonneg (Nat.cast_nonneg r)]))

/-- Crude bound for any `(r, m)`. -/
lemma lam_topC_sum_aux (r m : ℕ) :
    ∑ p ∈ (Finset.range (Bnd lamInst r m)).filter Nat.Prime,
        (topC lamInst r m p : ℝ) * Real.log p ≤
      8 + (Bnd lamInst r m : ℝ) *
        (4 * Real.log (Elev lamInst r m) + Real.log (Bnd lamInst r m)) := by
  set P := (Finset.range (Bnd lamInst r m)).filter Nat.Prime with hP
  set B := Bnd lamInst r m with hB
  set E := Elev lamInst r m with hE
  have hlE : 0 ≤ Real.log E := Real.log_natCast_nonneg E
  have hpt : ∀ p ∈ P, (topC lamInst r m p : ℝ) * Real.log p ≤
      2 * ((if p = 2 then (4 : ℝ) * Real.log 2 else 0)) + (4 * Real.log E + Real.log B) := by
    intro p hp
    have hp' := Finset.mem_filter.1 hp
    have hlt : p < B := Finset.mem_range.1 hp'.1
    have h1 := topC_log_le lamInst r m hp'.2.one_lt
    have h2 : Real.log p ≤ Real.log B :=
      Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hlt.le)
    have h3 : (cOf lamInst p : ℝ) * Real.log p ≤ if p = 2 then (4 : ℝ) * Real.log 2 else 0 := by
      by_cases h : p = 2
      · subst h; simp [lam_cOf2]
      · simp [h, lam_cOf_odd hp'.2 h]
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

theorem lam_topC_sum {ε : ℝ} (hε : 0 < ε) : ∀ᶠ r : ℕ in Filter.atTop,
    ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      (topC lamInst r (r / 8) p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2 := by
  have hl := lam_log_le_eventually (e := ε / 252) (by positivity)
  have hbig : ∀ᶠ r : ℕ in atTop, 16 / ε ≤ (r : ℝ) ^ 2 := by
    have : Tendsto (fun r : ℕ => (r : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop _
  filter_upwards [hl, hbig, eventually_ge_atTop 18] with r hr hr2 hr18
  refine (lam_topC_sum_aux r (r / 8)).trans ?_
  have hBd : Bnd lamInst r (r / 8) = 4 * (r + 2 * (r / 8)) + 5 := lam_Bnd r (r / 8)
  set m := r / 8 with hm
  have hm8 : 8 * m ≤ r := by omega
  have hN : r + 2 * m ≤ 2 * r := by omega
  have hrR : (18 : ℝ) ≤ r := by exact_mod_cast hr18
  have hBr : Bnd lamInst r m ≤ 9 * r := by omega
  have hBr2 : Bnd lamInst r m ≤ r ^ 2 := by nlinarith
  have hEr : Elev lamInst r m ≤ r ^ 3 := by
    have : Elev lamInst r m = 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m) := rfl
    rw [this]
    have h1 : 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m) ≤ 4 * (2 * r) * (2 * r) + 2 * r :=
      Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left _ hN) hN) hN
    nlinarith
  have hBpos : (0 : ℝ) < Bnd lamInst r m := by rw [hBd]; positivity
  have hEpos : (0 : ℝ) < Elev lamInst r m := by
    have : Elev lamInst r m = 4 * (r + 2 * m) * (r + 2 * m) + (r + 2 * m) := rfl
    rw [this]; positivity
  have hlogE : Real.log (Elev lamInst r m) ≤ 3 * Real.log r := by
    have hc : (Elev lamInst r m : ℝ) ≤ (r : ℝ) ^ 3 := by exact_mod_cast hEr
    have := Real.log_le_log hEpos hc
    rwa [Real.log_pow] at this
  have hlogB : Real.log (Bnd lamInst r m) ≤ 2 * Real.log r := by
    have hc : (Bnd lamInst r m : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast hBr2
    have := Real.log_le_log hBpos hc
    rwa [Real.log_pow] at this
  have hBR : (Bnd lamInst r m : ℝ) ≤ 9 * r := by exact_mod_cast hBr
  have hlr : 0 ≤ Real.log r := Real.log_natCast_nonneg r
  have hr0 : (0 : ℝ) < r := by linarith
  have h16 : 8 ≤ ε / 2 * (r : ℝ) ^ 2 := by
    have := (div_le_iff₀ hε).1 hr2
    nlinarith
  have hmain : (Bnd lamInst r m : ℝ) * (4 * Real.log (Elev lamInst r m) + Real.log (Bnd lamInst r m))
      ≤ (9 * r) * (14 * Real.log r) := by
    have a1 := Real.log_natCast_nonneg (Elev lamInst r m)
    have a2 := Real.log_natCast_nonneg (Bnd lamInst r m)
    exact mul_le_mul hBR (by linarith) (by linarith) (by positivity)
  have : (9 * (r : ℝ)) * (14 * Real.log r) ≤ ε / 2 * (r : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 126 * r by positivity)
    nlinarith
  linarith

end CatalanFrames.Lambda
