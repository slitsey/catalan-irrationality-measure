module

public import CatalanFrames.Lambda.HybDefSum
public import CatalanFrames.Lambda.HybDefE3

@[expose] public section

/-!
# λ: B, E (class 1) and E (class 3) as one `DefHypT` family, with the deficit sums

* `lam_E3_deficit_sum`: `∑_p defE3 r p · log p ≥ m ((7/80 - ε) r - 6 log r)`;
* `lam_defHypT_all`: for `r ≥ 16` a single `T` and `δ` with `DefHypT lamInst r (r/8) T δ`,
  `δ = m` on both clean classes and `δ = m - (p - r)` on `r < p < r + m`;
* `lam_log_DhybT`: `log DhybT = ∑ T log p - ∑ δ log p` (from `log_DhybT`).
The remaining step toward the content constant is the bound `∑ T log p ≤ ∑ tropExp-bound`
(the dual values `2r+m`, `dualE1`, `dualB` against the piece tables), see status.md.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma defE3_eq (r p : ℕ) : defE3 r p = cleanDef (r / 8) (cleanE3 r) p := by
  classical
  unfold defE3 cleanDef
  rfl

theorem lam_E3_deficit_sum {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r) ≤
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (defE3 r p : ℝ) * Real.log p := by
  classical
  have hs : (0 : ℝ) < ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) := by norm_num
  have hst : ((5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) ≤ ((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) := by norm_num
  have ht : ((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) ≤ 1 := by norm_num
  have hu : IsUnit (3 : ZMod 4) := by decide
  have h := cleanSum_ge (M := 4) hu hs hst ht hε
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
      p ≤ ⌊((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) * r⌋₊ → p.Prime → (p : ZMod 4) = 3 → p ∉ Exc →
      cleanE3 r p := by
    intro p h1 h2 hp hc hnot
    rw [floor_frac] at h1 h2
    have h4 : p % 4 = 3 := by
      have := congrArg ZMod.val hc
      rw [ZMod.val_natCast] at this
      rw [this]
      decide
    have hnot' : ¬ (5 * r / 8 ≤ p ∧ p ≤ 5 * r / 8 + 2) ∧ ¬ (4 * r / 5 - 1 ≤ p ∧ p ≤ 4 * r / 5) ∧
        p ≠ 139 := by
      simp only [hExc, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton, not_or] at hnot
      exact ⟨hnot.1.1, hnot.1.2, hnot.2⟩
    refine ⟨hp, h4, by omega, by omega, hnot'.2.2⟩
  have := hr (lamInst) (r / 8) (cleanE3 r) Exc hcl
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have hc6 : (Exc.card : ℝ) ≤ 6 := by exact_mod_cast hcard
  have hm0 : (0 : ℝ) ≤ ((r / 8 : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      (defE3 r p : ℝ) * Real.log p =
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
        (cleanDef (r / 8) (cleanE3 r) p : ℝ) * Real.log p := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [defE3_eq]
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

open Classical in
/-- The dual excess of the three windows. -/
noncomputable def eN (r p : ℕ) : ℕ :=
  max (max (if cleanE1 r p then dualE1 r (r / 8) p else 0)
      (if cleanE3 r p then 2 * r + r / 8 else 0))
    (if WB r p then dualB r (r / 8) p else 0)

/-- The exponent bound. -/
noncomputable def Tfun (r p : ℕ) : ℕ := max (tropExp lamInst r (r / 8) p) (eN r p)

/-- **B, E (class 1) and E (class 3) as a single `DefHypT` family.** -/
theorem lam_defHypT_all {r : ℕ} (hr : 16 ≤ r) :
    ∃ δ : ℕ → ℕ, DefHypT lamInst r (r / 8) (Tfun r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) := by
  classical
  set T : ℕ → ℕ := Tfun r with hT
  have hTdef : ∀ p, T p = max (tropExp lamInst r (r / 8) p) (eN r p) := fun p => rfl
  have hT1 : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ T p :=
    fun p _ _ => le_max_left _ _
  have hE1 := defHypT_E1 r T hT1 (fun p hc => by
    simp only [hT, Tfun, eN]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _)
    rw [if_pos hc])
  have hE3 := defHypT_E3 hr T hT1 (fun p hc => by
    simp only [hT, Tfun, eN]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_right _ _)
    rw [if_pos hc])
  have hB := defHypT_B lamInst lamData r (r / 8) T (WB r) (fun p hp => hp.2.2)
    (fun p hp hW => ⟨_, _, bsetup_of hr hW.1 hW.2.1 hW.2.2⟩) hT1
    (fun p hp hW j k S => by
      rw [bsetup_k hW.1 S]
      simp only [hT, Tfun, eN]
      refine le_trans ?_ (le_max_right _ _)
      refine le_trans ?_ (le_max_right _ _)
      rw [if_pos hW]
      exact le_rfl)
  have d13 : ∀ p, defE1 r p = 0 ∨ defE3 r p = 0 := by
    intro p
    by_cases hc : cleanE1 r p
    · right
      have : ¬ cleanE3 r p := fun h => by have := hc.2.1; have := h.2.1; omega
      simp [defE3, this]
    · left; simp [defE1, hc]
  refine ⟨_, defHypT_add (defHypT_add hE1 hE3 (fun p _ _ => d13 p)) hB ?_, ?_, ?_, ?_⟩
  · intro p hp hb
    by_cases hc : cleanE1 r p ∨ cleanE3 r p
    · right
      have : ¬ WB r p := fun hw => by
        rcases hc with hc | hc
        · have := hc.2.2.2; have := hw.2.1; omega
        · have : p < r := by have := hc.2.2.2.1; omega
          have := hw.2.1; omega
      simp [this]
    · left
      push_neg at hc
      simp [defE1, defE3, hc.1, hc.2]
  · intro p hc
    have : ¬ cleanE3 r p := fun h => by have := hc.2.1; have := h.2.1; omega
    have : ¬ WB r p := fun hw => by have := hc.2.2.2; have := hw.2.1; omega
    simp [defE1, defE3, hc, *]
  · intro p hc
    have h1 : ¬ cleanE1 r p := fun h => by have := hc.2.1; have := h.2.1; omega
    have : ¬ WB r p := fun hw => by
      have : p < r := by have := hc.2.2.2.1; omega
      have := hw.2.1; omega
    simp [defE1, defE3, hc, *]
  · intro p hW
    have h1 : ¬ cleanE1 r p := fun hc => by have := hc.2.2.2; have := hW.2.1; omega
    have h3 : ¬ cleanE3 r p := fun hc => by
      have : p < r := by have := hc.2.2.2.1; omega
      have := hW.2.1; omega
    simp [defE1, defE3, h1, h3, hW]

/-- `log DhybT` for the family of `lam_defHypT_all`. -/
theorem lam_log_DhybT {r : ℕ} {T δ : ℕ → ℕ} (h : DefHypT lamInst r (r / 8) T δ) :
    Real.log (DhybT lamInst r (r / 8) T δ) =
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime, (T p : ℝ) * Real.log p -
      ∑ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime, (δ p : ℝ) * Real.log p :=
  log_DhybT lamInst r (r / 8) h

end CatalanFrames.Lambda
