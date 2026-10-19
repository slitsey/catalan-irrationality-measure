module

public import CatalanFrames.HybCommon.DefBoth
public import CatalanCore.Arith.Hybrid.LemmaE.Summation
public import CatalanCore.Arith.Hybrid.DefSumLin
public import CatalanCore.Arith.Hybrid.DefSum
public import CatalanFrames.Lambda.HybDefE3
public import CatalanFrames.Lambda.HybDefSum2

@[expose] public section

/-!
# Lower bounds for the deficit sums, generic in the offset (class dictionary)

For `I : HybInst Fr`, `o ∈ {1, 3}`: `∑_{p < Bnd} dX p log p` for the five windows E1, E3, B, C5, C7,
with the same constants for both offsets (`1/7`, `7/80`, `1/128`, `1/320`, `1/448`); the residue classes
are `o` (j = 3: E1, C7) and `4 - o` (j = 1: E3, C5).
-/

open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanCore.NT

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

lemma Bnd_ge (I : HybInst Fr) (r m : ℕ) : r + 2 * m + 3 ≤ Bnd I r m := by
  have := I.cd.hL
  unfold Bnd
  nlinarith

lemma isUnit_o {o : ℕ} (ho : o = 1 ∨ o = 3) : IsUnit ((o : ℕ) : ZMod 4) := by
  rcases ho with rfl | rfl <;> decide

lemma isUnit_o' {o : ℕ} (ho : o = 1 ∨ o = 3) : IsUnit ((4 - o : ℕ) : ZMod 4) := by
  rcases ho with rfl | rfl <;> decide

lemma cls_mod {p o : ℕ} (ho : o = 1 ∨ o = 3) (h : (p : ZMod 4) = ((o : ℕ) : ZMod 4)) :
    p % 4 = o := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rcases ho with rfl | rfl <;> simpa using h

lemma cls_mod' {p o : ℕ} (ho : o = 1 ∨ o = 3) (h : (p : ZMod 4) = ((4 - o : ℕ) : ZMod 4)) :
    p % 4 = 4 - o := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rcases ho with rfl | rfl <;> simpa using h

lemma dE1_eq (o r p : ℕ) : dE1 o r p = cleanDef (r / 8) (cleanE1G o r) p := by
  unfold dE1 cleanDef; rfl

lemma dE3_eq (o r p : ℕ) : dE3 o r p = cleanDef (r / 8) (cleanE3G o r) p := by
  unfold dE3 cleanDef; rfl

theorem sum_E1 (I : HybInst Fr) {o : ℕ} (ho : o = 1 ∨ o = 3) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r) ≤
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dE1 o r p : ℝ) * Real.log p := by
  have hs : (0 : ℝ) < ((5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) := by norm_num
  have hst : ((5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by norm_num
  have ht : ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) ≤ 1 := by norm_num
  have h := cleanSum_ge (M := 4) (isUnit_o ho) hs hst ht hε
  filter_upwards [h, eventually_ge_atTop 16] with r hr hr16
  set Exc : Finset ℕ := Finset.Icc (5 * r / 7) (5 * r / 7 + 2) ∪ {r} with hExc
  have hcard : Exc.card ≤ 4 := by
    refine (Finset.card_union_le _ _).trans ?_
    simp only [Nat.card_Icc, Finset.card_singleton]
    omega
  have hcl : ∀ p, ⌊((5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) * r⌋₊ < p →
      p ≤ ⌊((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * r⌋₊ → p.Prime → (p : ZMod 4) = ((o : ℕ) : ZMod 4) →
      p ∉ Exc → cleanE1G o r p := by
    intro p h1 h2 hp hc hnot
    rw [floor_frac] at h1 h2
    have h4 := cls_mod ho hc
    have hnot' : ¬ (5 * r / 7 ≤ p ∧ p ≤ 5 * r / 7 + 2) ∧ p ≠ r := by
      simp only [hExc, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton, not_or] at hnot
      exact hnot
    refine ⟨hp, h4, by omega, by omega⟩
  have := hr I (r / 8) (cleanE1G o r) Exc hcl
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hc4 : (Exc.card : ℝ) ≤ 4 := by exact_mod_cast hcard
  have hm0 : (0 : ℝ) ≤ ((r / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
      (dE1 o r p : ℝ) * Real.log p =
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
        (cleanDef (r / 8) (cleanE1G o r) p : ℝ) * Real.log p := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dE1_eq]
  rw [e]
  refine le_trans ?_ this
  have hφ : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [hφ]
  apply mul_le_mul_of_nonneg_left _ hm0
  have e2 : (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) / 2 = 1 / 7 := by
    norm_num
  rw [e2]
  nlinarith [hlog, hc4]

theorem sum_E3 (I : HybInst Fr) {o : ℕ} (ho : o = 1 ∨ o = 3) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r) ≤
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime, (dE3 o r p : ℝ) * Real.log p := by
  have hs : (0 : ℝ) < ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) := by norm_num
  have hst : ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) ≤ ((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) := by norm_num
  have ht : ((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) ≤ 1 := by norm_num
  have h := cleanSum_ge (M := 4) (isUnit_o' ho) hs hst ht hε
  filter_upwards [h, eventually_ge_atTop 16] with r hr hr16
  set Exc : Finset ℕ := Finset.Icc (5 * r / 8) (5 * r / 8 + 2) ∪
    Finset.Icc (4 * r / 5 - 1) (4 * r / 5) ∪ {139} with hExc
  have hcard : Exc.card ≤ 6 := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : (Finset.Icc (5 * r / 8) (5 * r / 8 + 2) ∪ Finset.Icc (4 * r / 5 - 1) (4 * r / 5)).card
        ≤ 5 := by
      refine (Finset.card_union_le _ _).trans ?_
      simp only [Nat.card_Icc]
      omega
    simp only [Finset.card_singleton]
    omega
  have hcl : ∀ p, ⌊((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) * r⌋₊ < p →
      p ≤ ⌊((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) * r⌋₊ → p.Prime → (p : ZMod 4) = ((4 - o : ℕ) : ZMod 4) →
      p ∉ Exc → cleanE3G o r p := by
    intro p h1 h2 hp hc hnot
    rw [floor_frac] at h1 h2
    have h4 := cls_mod' ho hc
    have hnot' : ¬ (5 * r / 8 ≤ p ∧ p ≤ 5 * r / 8 + 2) ∧ ¬ (4 * r / 5 - 1 ≤ p ∧ p ≤ 4 * r / 5) ∧
        p ≠ 139 := by
      simp only [hExc, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton, not_or] at hnot
      exact ⟨hnot.1.1, hnot.1.2, hnot.2⟩
    refine ⟨hp, h4, by omega, by omega, ?_⟩
    exact CatalanFrames.Lambda.not_dvd_6255 hp (by omega) hnot'.2.2
  have := hr I (r / 8) (cleanE3G o r) Exc hcl
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hc6 : (Exc.card : ℝ) ≤ 6 := by exact_mod_cast hcard
  have hm0 : (0 : ℝ) ≤ ((r / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
      (dE3 o r p : ℝ) * Real.log p =
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
        (cleanDef (r / 8) (cleanE3G o r) p : ℝ) * Real.log p := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dE3_eq]
  rw [e]
  refine le_trans ?_ this
  have hφ : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [hφ]
  apply mul_le_mul_of_nonneg_left _ hm0
  have e2 : (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) - ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) / 2 = 7 / 80 := by
    norm_num
  rw [e2]
  nlinarith [hlog, hc6]

end CatalanFrames.HybCommon
