module

public import CatalanFrames.HybCommon.Sums

@[expose] public section

/-!
# Staircase deficit sums (B, C5, C7), generic in the offset
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanCore.NT CatalanFrames.Lambda

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

theorem sum_B (I : HybInst Fr) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, (1 / 128 - ε) * (r : ℝ) ^ 2 ≤
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dB r p : ℝ) * Real.log p := by
  have hu : IsUnit (1 : ZMod 1) := isUnit_one
  have h := staircase_ge (M := 1) hu (by positivity : 0 < ε / 4)
  filter_upwards [h, eventually_ge_atTop 16, eventually_ge_atTop ⌈4 / ε⌉₊] with r hr hr16 hrε
  have hBg := Bnd_ge I r (r / 8)
  have hB := hr ((Finset.range (Bnd I r (r / 8))).filter Nat.Prime) (dB r) (r / 8 - 1)
    (fun _ => r) (fun j => r + r / 8 - j) (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
    (fun j hj p h1 h2 hp _ => by
      simp only [Finset.mem_Icc] at hj
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩, ?_⟩
      · omega
      · have : WBG r p := ⟨hp, h1, by omega⟩
        simp only [dB, if_pos this]; omega)
  refine le_trans ?_ hB
  rw [show Nat.totient 1 = 1 from rfl]
  have e : ∀ j ∈ Finset.Icc 1 (r / 8 - 1),
      (((r + r / 8 - j : ℕ) : ℝ) - ((r : ℕ) : ℝ)) / ((1 : ℕ) : ℝ) - ε / 4 * r =
      ((((r / 8 : ℕ) : ℝ) - ε / 4 * r)) - 1 * (j : ℝ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [Finset.sum_congr rfl e, sum_Icc_affine]
  have hm1 : ((r / 8 - 1 : ℕ) : ℝ) = ((r / 8 : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hm1]
  have hm : (r : ℝ) / 8 - 1 ≤ ((r / 8 : ℕ) : ℝ) := by
    have : r ≤ 8 * (r / 8) + 7 := by omega
    have h' : (r : ℝ) ≤ 8 * ((r / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast this
    linarith
  have hm' : ((r / 8 : ℕ) : ℝ) ≤ (r : ℝ) / 8 := by
    have : 8 * (r / 8) ≤ r := by omega
    have h' : 8 * ((r / 8 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    linarith
  have hεr : 4 ≤ ε * r := by
    have h1 : 4 / ε ≤ (r : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hrε)
    rw [div_le_iff₀ hε] at h1
    linarith
  have hr0 : (16 : ℝ) ≤ r := by exact_mod_cast hr16
  set mm : ℝ := ((r / 8 : ℕ) : ℝ) with hmm
  nlinarith [mul_nonneg hε.le (sq_nonneg (r : ℝ))]

theorem sum_C5 (I : HybInst Fr) {o : ℕ} (ho : o = 1 ∨ o = 3) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, (1 / 320 - ε) * (r : ℝ) ^ 2 ≤
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dC5 o r p : ℝ) * Real.log p := by
  have h := staircase_ge (M := 4) (isUnit_o' ho) (by positivity : 0 < ε / 4)
  filter_upwards [h, eventually_ge_atTop 64, eventually_ge_atTop ⌈4 / ε⌉₊] with r hr hr64 hrε
  have hBg := Bnd_ge I r (r / 8)
  have hB := hr ((Finset.range (Bnd I r (r / 8))).filter Nat.Prime) (dC5 o r) (r / 8 - 1)
    (fun j => (4 * (r + r / 8 + j) - o) / 5)
    (fun _ => min (r - 1) ((4 * (r + 2 * (r / 8)) - o - 1) / 5))
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
    (fun j hj p h1 h2 hp hc => by
      have h4 := cls_mod' ho hc
      simp only [Finset.mem_Icc] at hj
      have hW : WC5G o r p := ⟨hp, h4, by omega, by omega, by omega⟩
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩, ?_⟩
      · omega
      · simp only [dC5, if_pos hW]; omega)
  refine le_trans ?_ hB
  have hφ : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [hφ]
  have hmr : (r : ℝ) / 8 - 1 ≤ ((r / 8 : ℕ) : ℝ) := by
    have : r ≤ 8 * (r / 8) + 7 := by omega
    have h' : (r : ℝ) ≤ 8 * ((r / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast this
    linarith
  have hmr' : ((r / 8 : ℕ) : ℝ) ≤ (r : ℝ) / 8 := by
    have : 8 * (r / 8) ≤ r := by omega
    have h' : 8 * ((r / 8 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    linarith
  set mm : ℝ := ((r / 8 : ℕ) : ℝ) with hmm
  have e : ∀ j ∈ Finset.Icc 1 (r / 8 - 1),
      ((min (r - 1) ((4 * (r + 2 * (r / 8)) - o - 1) / 5) : ℕ) -
          (((4 * (r + r / 8 + j) - o) / 5 : ℕ) : ℝ)) / 2 - ε / 4 * r ≥
        ((r - 4 * mm - 14) / 10 - ε / 4 * r) - (2 / 5) * (j : ℝ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have h1 : r ≤ min (r - 1) ((4 * (r + 2 * (r / 8)) - o - 1) / 5) + 3 := by omega
    have h2 : 5 * ((4 * (r + r / 8 + j) - o) / 5) + 1 ≤ 4 * (r + r / 8 + j) := by omega
    have h1' : (r : ℝ) ≤ ((min (r - 1) ((4 * (r + 2 * (r / 8)) - o - 1) / 5) : ℕ) : ℝ) + 3 := by
      exact_mod_cast h1
    have h2' : 5 * (((4 * (r + r / 8 + j) - o) / 5 : ℕ) : ℝ) + 1 ≤ 4 * (r + mm + j) := by
      have h2'' : ((5 * ((4 * (r + r / 8 + j) - o) / 5) + 1 : ℕ) : ℝ) ≤
          ((4 * (r + r / 8 + j) : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at h2''
      rw [hmm]; exact h2''
    linarith
  have hs := Finset.sum_le_sum e
  rw [sum_Icc_affine] at hs
  have hm1 : ((r / 8 - 1 : ℕ) : ℝ) = mm - 1 := by
    rw [Nat.cast_sub (by omega)]; simp [hmm]
  rw [hm1] at hs
  have hεr : 4 ≤ ε * r := by
    have h1 : 4 / ε ≤ (r : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hrε)
    rw [div_le_iff₀ hε] at h1
    linarith
  have hr0 : (64 : ℝ) ≤ r := by exact_mod_cast hr64
  have ha : (r : ℝ) / 8 - 2 ≤ mm - 1 := by linarith
  have hb : (r : ℝ) / 4 - 14 ≤ r - 6 * mm - 14 := by linarith
  have hab : ((r : ℝ) / 8 - 2) * ((r : ℝ) / 4 - 14) ≤ (mm - 1) * (r - 6 * mm - 14) :=
    mul_le_mul ha hb (by linarith) (by linarith)
  have hεm : ε * r * (mm - 1) ≤ ε * r * ((r : ℝ) / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hεr2 : ε * (r : ℝ) ^ 2 ≥ 4 * r := by nlinarith
  nlinarith

theorem sum_C7 (I : HybInst Fr) {o : ℕ} (ho : o = 1 ∨ o = 3) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, (1 / 448 - ε) * (r : ℝ) ^ 2 ≤
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dC7 o r p : ℝ) * Real.log p := by
  have h := staircase_ge (M := 4) (isUnit_o ho) (by positivity : 0 < ε / 4)
  filter_upwards [h, eventually_ge_atTop 64, eventually_ge_atTop ⌈4 / ε⌉₊] with r hr hr64 hrε
  have hBg := Bnd_ge I r (r / 8)
  have hB := hr ((Finset.range (Bnd I r (r / 8))).filter Nat.Prime) (dC7 o r) (r / 8 - 1)
    (fun j => (4 * (r + r / 8 + j) - o) / 7)
    (fun _ => (4 * r + 8 * (r / 8) - o - 1) / 7)
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
    (fun j hj p h1 h2 hp hc => by
      have h4 := cls_mod ho hc
      simp only [Finset.mem_Icc] at hj
      have hW : WC7G o r p := ⟨hp, h4, by omega, by omega⟩
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩, ?_⟩
      · omega
      · simp only [dC7, if_pos hW]; omega)
  refine le_trans ?_ hB
  have hφ : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [hφ]
  have hmr : (r : ℝ) / 8 - 1 ≤ ((r / 8 : ℕ) : ℝ) := by
    have : r ≤ 8 * (r / 8) + 7 := by omega
    have h' : (r : ℝ) ≤ 8 * ((r / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast this
    linarith
  have hmr' : ((r / 8 : ℕ) : ℝ) ≤ (r : ℝ) / 8 := by
    have : 8 * (r / 8) ≤ r := by omega
    have h' : 8 * ((r / 8 : ℕ) : ℝ) ≤ r := by exact_mod_cast this
    linarith
  set mm : ℝ := ((r / 8 : ℕ) : ℝ) with hmm
  have e : ∀ j ∈ Finset.Icc 1 (r / 8 - 1),
      ((((4 * r + 8 * (r / 8) - o - 1) / 7 : ℕ) : ℝ) - (((4 * (r + r / 8 + j) - o) / 7 : ℕ) : ℝ)) / 2
        - ε / 4 * r ≥ ((4 * mm - 9) / 14 - ε / 4 * r) - (2 / 7) * (j : ℝ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have h1 : 4 * r + 8 * (r / 8) ≤ 7 * ((4 * r + 8 * (r / 8) - o - 1) / 7) + 10 := by omega
    have h2 : 7 * ((4 * (r + r / 8 + j) - o) / 7) + 1 ≤ 4 * (r + r / 8 + j) := by omega
    have h1' : 4 * (r : ℝ) + 8 * mm ≤ 7 * (((4 * r + 8 * (r / 8) - o - 1) / 7 : ℕ) : ℝ) + 10 := by
      have h1'' : ((4 * r + 8 * (r / 8) : ℕ) : ℝ) ≤
          ((7 * ((4 * r + 8 * (r / 8) - o - 1) / 7) + 10 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1''
      rw [hmm]; exact h1''
    have h2' : 7 * (((4 * (r + r / 8 + j) - o) / 7 : ℕ) : ℝ) + 1 ≤ 4 * (r + mm + j) := by
      have h2'' : ((7 * ((4 * (r + r / 8 + j) - o) / 7) + 1 : ℕ) : ℝ) ≤
          ((4 * (r + r / 8 + j) : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at h2''
      rw [hmm]; exact h2''
    linarith
  have hs := Finset.sum_le_sum e
  rw [sum_Icc_affine] at hs
  have hm1 : ((r / 8 - 1 : ℕ) : ℝ) = mm - 1 := by
    rw [Nat.cast_sub (by omega)]; simp [hmm]
  rw [hm1] at hs
  have hεr : 4 ≤ ε * r := by
    have h1 : 4 / ε ≤ (r : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hrε)
    rw [div_le_iff₀ hε] at h1
    linarith
  have hr0 : (64 : ℝ) ≤ r := by exact_mod_cast hr64
  have ha : (r : ℝ) / 8 - 2 ≤ mm - 1 := by linarith
  have hb : (r : ℝ) / 4 - 11 ≤ 2 * mm - 9 := by linarith
  have hab : ((r : ℝ) / 8 - 2) * ((r : ℝ) / 4 - 11) ≤ (mm - 1) * (2 * mm - 9) :=
    mul_le_mul ha hb (by linarith) (by linarith)
  have hεm : ε * r * (mm - 1) ≤ ε * r * ((r : ℝ) / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hεr2 : ε * (r : ℝ) ^ 2 ≥ 4 * r := by nlinarith
  nlinarith

end CatalanFrames.HybCommon
