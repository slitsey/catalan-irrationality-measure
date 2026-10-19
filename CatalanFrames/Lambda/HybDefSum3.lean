module

public import CatalanFrames.Lambda.HybDefC7Lam
public import CatalanFrames.Lambda.HybDefSum2

@[expose] public section

/-!
# λ: the deficit sums of C7 and GK

* `lam_C7_deficit_sum`: `∑ defC7 r p log p ≥ (1/448 - ε) r²`   (staircase, as for C5);
* `lam_GK3_deficit_sum`, `lam_GK1_deficit_sum`: `∑ defGK p log p ≥ m ((1/72 resp. 1/44 - ε) r - 2 log r)`
  (`cleanSum_ge`; the O(1) exceptional primes `139`, `1009` and the band-boundary primes are in `Exc`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

open Classical in
/-- The C7 deficit `L_p - m`. -/
noncomputable def defC7 (r p : ℕ) : ℕ := if WC7 r p then p + (3 * p + 1) / 4 - r - r / 8 else 0

/-- The GK deficit, class 3. -/
noncomputable def defGK3 (r p : ℕ) : ℕ := cleanDef (r / 8) (LC3 r) p

/-- The GK deficit, class 1. -/
noncomputable def defGK1 (r p : ℕ) : ℕ := cleanDef (r / 8) (LC1 r) p

theorem lam_C7_deficit_sum {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, (1 / 448 - ε) * (r : ℝ) ^ 2 ≤
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (defC7 r p : ℝ) * Real.log p := by
  classical
  have hu : IsUnit (1 : ZMod 4) := by decide
  have h := staircase_ge (M := 4) hu (by positivity : 0 < ε / 4)
  filter_upwards [h, eventually_ge_atTop 64, eventually_ge_atTop ⌈4 / ε⌉₊] with r hr hr64 hrε
  have hB := hr ((Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime) (defC7 r) (r / 8 - 1)
    (fun j => (4 * (r + r / 8 + j) - 2) / 7) (fun _ => (4 * r + 8 * (r / 8) - 2) / 7)
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
    (fun j hj p h1 h2 hp hc => by
      have h4 := cls4_mod1 hc
      simp only [Finset.mem_Icc] at hj
      have hW : WC7 r p := ⟨hp, h4, by omega, by omega⟩
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩, ?_⟩
      · rw [lam_Bnd]; omega
      · simp only [defC7, if_pos hW]; omega)
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
      ((((4 * r + 8 * (r / 8) - 2) / 7 : ℕ) : ℝ) - (((4 * (r + r / 8 + j) - 2) / 7 : ℕ) : ℝ)) / 2
        - ε / 4 * r ≥ ((2 * mm - 3) / 7 - ε / 4 * r) - (2 / 7) * (j : ℝ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have h1 : 4 * r + 8 * (r / 8) ≤ 7 * ((4 * r + 8 * (r / 8) - 2) / 7) + 8 := by omega
    have h2 : 7 * ((4 * (r + r / 8 + j) - 2) / 7) + 2 ≤ 4 * (r + r / 8 + j) := by omega
    have h1' : 4 * (r : ℝ) + 8 * mm ≤ 7 * (((4 * r + 8 * (r / 8) - 2) / 7 : ℕ) : ℝ) + 8 := by
      have h1'' : ((4 * r + 8 * (r / 8) : ℕ) : ℝ) ≤
          ((7 * ((4 * r + 8 * (r / 8) - 2) / 7) + 8 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1''
      rw [hmm]; exact h1''
    have h2' : 7 * (((4 * (r + r / 8 + j) - 2) / 7 : ℕ) : ℝ) + 2 ≤ 4 * (r + mm + j) := by
      have h2'' : ((7 * ((4 * (r + r / 8 + j) - 2) / 7) + 2 : ℕ) : ℝ) ≤
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
  have hb : (r : ℝ) / 8 - 4 ≤ mm - 3 := by linarith
  have hab : ((r : ℝ) / 8 - 2) * ((r : ℝ) / 8 - 4) ≤ (mm - 1) * (mm - 3) :=
    mul_le_mul ha hb (by linarith) (by linarith)
  have hεm : ε * r * (mm - 1) ≤ ε * r * ((r : ℝ) / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hεr2 : ε * (r : ℝ) ^ 2 ≥ 4 * r := by nlinarith
  nlinarith

theorem lam_GK3_deficit_sum {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ((r / 8 : ℕ) : ℝ) * (((1 / 72 : ℝ) - ε) * r - 2 * Real.log r) ≤
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (defGK3 r p : ℝ) * Real.log p := by
  classical
  have hs : (0 : ℝ) < ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) := by norm_num
  have hst : ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) ≤ ((4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ) := by norm_num
  have ht : ((4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ) ≤ 1 := by norm_num
  have hu : IsUnit (3 : ZMod 4) := by decide
  have h := cleanSum_ge (M := 4) hu hs hst ht hε
  filter_upwards [h, eventually_ge_atTop 64] with r hr hr64
  set Exc : Finset ℕ := {4 * r / 9, 139} with hExc
  have hcard : Exc.card ≤ 2 := Finset.card_le_two
  have hcl : ∀ p, ⌊((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) * r⌋₊ < p →
      p ≤ ⌊((4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ) * r⌋₊ → p.Prime → (p : ZMod 4) = 3 → p ∉ Exc →
      LC3 r p := by
    intro p h1 h2 hp hc hnot
    rw [floor_frac] at h1 h2
    have h4 := cls4_mod3 hc
    have hnot' : p ≠ 4 * r / 9 ∧ p ≠ 139 := by
      simp only [hExc, Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      exact hnot
    refine ⟨by omega, h4, hnot'.2, by omega, by omega⟩
  have := hr lamInst (r / 8) (LC3 r) Exc hcl
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hc2 : (Exc.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  have hm0 : (0 : ℝ) ≤ ((r / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
  refine le_trans ?_ this
  have hφ : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [hφ]
  apply mul_le_mul_of_nonneg_left _ hm0
  have e2 : (((4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ) - ((5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) / 2 = 1 / 72 := by
    norm_num
  rw [e2]
  nlinarith [hlog, hc2]

theorem lam_GK1_deficit_sum {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ((r / 8 : ℕ) : ℝ) * (((1 / 44 : ℝ) - ε) * r - 2 * Real.log r) ≤
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (defGK1 r p : ℝ) * Real.log p := by
  classical
  have hs : (0 : ℝ) < ((5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ) := by norm_num
  have hst : ((5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := by norm_num
  have ht : ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) ≤ 1 := by norm_num
  have hu : IsUnit (1 : ZMod 4) := by decide
  have h := cleanSum_ge (M := 4) hu hs hst ht hε
  filter_upwards [h, eventually_ge_atTop 64] with r hr hr64
  set Exc : Finset ℕ := {r / 2, 1009} with hExc
  have hcard : Exc.card ≤ 2 := Finset.card_le_two
  have hcl : ∀ p, ⌊((5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ) * r⌋₊ < p →
      p ≤ ⌊((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) * r⌋₊ → p.Prime → (p : ZMod 4) = 1 → p ∉ Exc →
      LC1 r p := by
    intro p h1 h2 hp hc hnot
    rw [floor_frac] at h1 h2
    have h4 := cls4_mod1 hc
    have hnot' : p ≠ r / 2 ∧ p ≠ 1009 := by
      simp only [hExc, Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      exact hnot
    refine ⟨by omega, h4, hnot'.2, by omega, by omega⟩
  have := hr lamInst (r / 8) (LC1 r) Exc hcl
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hc2 : (Exc.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  have hm0 : (0 : ℝ) ≤ ((r / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
  refine le_trans ?_ this
  have hφ : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [hφ]
  apply mul_le_mul_of_nonneg_left _ hm0
  have e2 : (((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) - ((5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) / 2 = 1 / 44 := by
    norm_num
  rw [e2]
  nlinarith [hlog, hc2]

end CatalanFrames.Lambda
