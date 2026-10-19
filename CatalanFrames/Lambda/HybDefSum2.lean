module

public import CatalanFrames.Lambda.HybDefAll
public import CatalanFrames.Lambda.HybFinal
public import CatalanCore.Arith.Hybrid.DefSumLin
public import CatalanCore.Arith.Hybrid.DefC5Fam

@[expose] public section

/-!
# λ: the deficit sums of B and C5 (staircase / layer-cake)

* `lam_B_deficit_sum`: `∑ defB r p log p ≥ (1/128 - ε) r²`   (`defB = m - (p - r)` on `r < p < r + m`);
* `lam_C5_deficit_sum`: `∑ defC5 r p log p ≥ (1/320 - ε) r²`  (`defC5 = (5p+1)/4 - r - m` on the C5
  window `p ≡ 3 (4)`, `m ≤ L_p < 2m`, `p < r`).
Both are staircases `δ ≥ j` on `A j < p ≤ B j` with `A j, B j` affine in `j`, so only the uniform
PNT bound `clsSum_ge_unif` and an arithmetic-progression sum are used.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma sum_Icc_affine (J : ℕ) (a b : ℝ) :
    ∑ j ∈ Finset.Icc 1 J, (a - b * j) = J * a - b * (J * (J + 1) / 2) := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

open Classical in
/-- The B deficit. -/
noncomputable def defB (r p : ℕ) : ℕ := if WB r p then r / 8 - (p - r) else 0

/-- The window of C5: `p ≡ 3 (4)`, `m ≤ L_p < 2m` with `L_p = (5p+1)/4 - r`, `p < r`. -/
def WC5 (r p : ℕ) : Prop :=
  p.Prime ∧ p % 4 = 3 ∧ 4 * (r + r / 8) ≤ 5 * p + 1 ∧ 5 * p + 1 < 4 * (r + 2 * (r / 8)) ∧ p < r

open Classical in
/-- The C5 deficit `L_p - m`. -/
noncomputable def defC5 (r p : ℕ) : ℕ := if WC5 r p then p + (p + 1) / 4 - r - r / 8 else 0

theorem lam_B_deficit_sum {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, (1 / 128 - ε) * (r : ℝ) ^ 2 ≤
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (defB r p : ℝ) * Real.log p := by
  classical
  have hu : IsUnit (1 : ZMod 1) := isUnit_one
  have h := staircase_ge (M := 1) hu (by positivity : 0 < ε / 4)
  filter_upwards [h, eventually_ge_atTop 16, eventually_ge_atTop ⌈4 / ε⌉₊] with r hr hr16 hrε
  have hB := hr ((Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime) (defB r) (r / 8 - 1)
    (fun _ => r) (fun j => r + r / 8 - j) (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
    (fun j hj p h1 h2 hp _ => by
      simp only [Finset.mem_Icc] at hj
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩, ?_⟩
      · rw [lam_Bnd]; omega
      · have : WB r p := ⟨hp, h1, by omega⟩
        simp only [defB, if_pos this]; omega)
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

theorem lam_C5_deficit_sum {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, (1 / 320 - ε) * (r : ℝ) ^ 2 ≤
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (defC5 r p : ℝ) * Real.log p := by
  classical
  have hu : IsUnit (3 : ZMod 4) := by decide
  have h := staircase_ge (M := 4) hu (by positivity : 0 < ε / 4)
  filter_upwards [h, eventually_ge_atTop 64, eventually_ge_atTop ⌈4 / ε⌉₊] with r hr hr64 hrε
  have hB := hr ((Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime) (defC5 r) (r / 8 - 1)
    (fun j => (4 * (r + r / 8 + j) - 2) / 5) (fun j => min (r - 1) ((4 * (r + 2 * (r / 8)) - 2) / 5))
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
    (fun j hj p h1 h2 hp hc => by
      have h4 := cls4_mod3 hc
      simp only [Finset.mem_Icc] at hj
      have hW : WC5 r p := ⟨hp, h4, by omega, by omega, by omega⟩
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩, ?_⟩
      · rw [lam_Bnd]; omega
      · simp only [defC5, if_pos hW]; omega)
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
      (((r - 1) ⊓ ((4 * (r + 2 * (r / 8)) - 2) / 5) : ℕ) - (((4 * (r + r / 8 + j) - 2) / 5 : ℕ) : ℝ)) / 2
        - ε / 4 * r ≥ ((r - 4 * mm - 8) / 10 - ε / 4 * r) - (2 / 5) * (j : ℝ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have h1 : r ≤ ((r - 1) ⊓ ((4 * (r + 2 * (r / 8)) - 2) / 5)) + 2 := by omega
    have h2 : 5 * ((4 * (r + r / 8 + j) - 2) / 5) + 2 ≤ 4 * (r + r / 8 + j) := by omega
    have h1' : (r : ℝ) ≤ (((r - 1) ⊓ ((4 * (r + 2 * (r / 8)) - 2) / 5) : ℕ) : ℝ) + 2 := by
      exact_mod_cast h1
    have h2' : 5 * (((4 * (r + r / 8 + j) - 2) / 5 : ℕ) : ℝ) + 2 ≤ 4 * (r + mm + j) := by
      have h2'' : ((5 * ((4 * (r + r / 8 + j) - 2) / 5) + 2 : ℕ) : ℝ) ≤ ((4 * (r + r / 8 + j) : ℕ) : ℝ) := by
        exact_mod_cast h2
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
  have hb : (r : ℝ) / 4 - 8 ≤ r - 6 * mm - 8 := by linarith
  have hab : ((r : ℝ) / 8 - 2) * ((r : ℝ) / 4 - 8) ≤ (mm - 1) * (r - 6 * mm - 8) :=
    mul_le_mul ha hb (by linarith) (by linarith)
  have hεm : ε * r * (mm - 1) ≤ ε * r * ((r : ℝ) / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hεr2 : ε * (r : ℝ) ^ 2 ≥ 4 * r := by nlinarith
  nlinarith
end CatalanFrames.Lambda
