module

public import CatalanFrames.Lambda.HybDefC5Lam
public import CatalanCore.Arith.Hybrid.DefC7Fam
public import CatalanCore.Arith.Hybrid.DefGKFam

@[expose] public section

/-!
# λ: C7 and GK wired into the combined `DefHypT` family

* `WC7`: window of C7 (`p ≡ 1 (4)`, `L_p = (7p+1)/4 - r ∈ [m, 2m)`); `eC7` its dual excess;
* `LC3, LC1`: the two GK low-band clean classes (`LowClean = LC3 ∨ LC1`); `eGK = 2r + m` there;
* `lam_defHypT_all3`: E1 + E3 + B + C5 + C7 + GK as ONE `DefHypT` family with `Tfun3`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-- The dual value of the D2 potentials of C7. -/
lemma wC7_dual_eq {o p r m k : ℕ} (S : CSetup7 o p r m k) :
    ∑ a : Fin r ⊕ Fin m, wC7 p r k (Frame.hybRow r m a) +
      ∑ b : Fin r ⊕ Fin m, wC7 p r k (Frame.hybCol r m b) = 2 * r + 2 * m - (p + k - r) := by
  have hk := S.hk; have := S.ho0; have := S.ho3; have := S.hp6
  have hLlo := S.hLlo
  have hLhi := S.hLhi
  have hrp := S.hrp
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hc : ∑ c : Fin r, wC7 p r k (c : ℕ) = r - (p + k - r) := by
    have : ∀ c : Fin r, wC7 p r k (c : ℕ) = if r - p ≤ (c : ℕ) ∧ (c : ℕ) < k then 0 else 1 :=
      fun c => by unfold wC7; rw [if_pos c.2]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if r - p ≤ i ∧ i < k then 0 else 1) r]
    have := sum_range_gap r (r - p) k (by omega)
    omega
  have hzr : ∑ i : Fin m, wC7 p r k (Frame.hybRow r m (Sum.inr i)) =
      m + min m ((p + k - r + 1) / 2) := by
    have : ∀ i : Fin m, wC7 p r k (Frame.hybRow r m (Sum.inr i)) =
        if (i : ℕ) < (p + k - r + 1) / 2 then 2 else 1 := fun i => by
      show wC7 p r k (r + 2 * (i : ℕ)) = _
      unfold wC7
      rw [if_neg (by omega)]
      by_cases h : (i : ℕ) < (p + k - r + 1) / 2
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (p + k - r + 1) / 2 then 2 else 1) m,
      sum_range_two]
  have hzc : ∑ i : Fin m, wC7 p r k (Frame.hybCol r m (Sum.inr i)) =
      m + min m ((p + k - r) / 2) := by
    have : ∀ i : Fin m, wC7 p r k (Frame.hybCol r m (Sum.inr i)) =
        if (i : ℕ) < (p + k - r) / 2 then 2 else 1 := fun i => by
      show wC7 p r k (r + 2 * (i : ℕ) + 1) = _
      unfold wC7
      rw [if_neg (by omega)]
      by_cases h : (i : ℕ) < (p + k - r) / 2
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (p + k - r) / 2 then 2 else 1) m,
      sum_range_two]
  have hcc : ∑ c : Fin r, wC7 p r k (Frame.hybCol r m (Sum.inl c)) = r - (p + k - r) := hc
  have hrr : ∑ c : Fin r, wC7 p r k (Frame.hybRow r m (Sum.inl c)) = r - (p + k - r) := hc
  rw [hrr, hcc, hzr, hzc]
  omega


/-- The window of C7. -/
def WC7 (r p : ℕ) : Prop :=
  p.Prime ∧ p % 4 = 1 ∧ 4 * (r + r / 8) ≤ 7 * p + 1 ∧ 7 * p + 1 < 4 * r + 8 * (r / 8)

/-- GK low-band clean primes, class 3. -/
def LC3 (r p : ℕ) : Prop :=
  13 ≤ p ∧ p % 4 = 3 ∧ p ≠ 139 ∧ 9 * p + 1 < 4 * r ∧ r + 2 * (r / 8) ≤ 3 * p

/-- GK low-band clean primes, class 1. -/
def LC1 (r p : ℕ) : Prop :=
  13 ≤ p ∧ p % 4 = 1 ∧ p ≠ 1009 ∧ 2 * p < r ∧ 4 * (r + 2 * (r / 8)) ≤ 11 * p + 1

lemma lowClean_iff (r p : ℕ) : LowClean r (r / 8) p ↔ LC3 r p ∨ LC1 r p := Iff.rfl

/-- The C7 dual excess. -/
noncomputable def eC7 (r p : ℕ) : ℕ := by
  classical exact if WC7 r p then 2 * r + 2 * (r / 8) - (p + (3 * p + 1) / 4 - r) else 0

/-- The GK dual excess. -/
noncomputable def eGK (r p : ℕ) : ℕ := by
  classical exact if LowClean r (r / 8) p then 2 * r + r / 8 else 0

lemma csetup7_of_wc7 {r p : ℕ} (hr : 16 ≤ r) (h : WC7 r p) :
    CSetup7 1 p r (r / 8) ((3 * p + 1) / 4) := by
  obtain ⟨hp, h4, h1, h2⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- `Tfun2` with the C7 and GK duals. -/
noncomputable def Tfun3 (r p : ℕ) : ℕ := max (Tfun2 r p) (max (eC7 r p) (eGK r p))

lemma wc7_disj {r p : ℕ} (hr : 16 ≤ r) (h : WC7 r p) :
    ¬ cleanE1 r p ∧ ¬ cleanE3 r p ∧ ¬ WB r p ∧ ¬ WC5 r p ∧ ¬ LowClean r (r / 8) p := by
  obtain ⟨hp, h4, h1, h2⟩ := h
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
  · have := c.2.2.1; omega
  · have := c.2.1; omega
  · have := c.2.1; omega
  · have := c.2.1; omega
  · rcases c with c | c <;> omega

lemma lc_disj {r p : ℕ} (hr : 16 ≤ r) (h : LowClean r (r / 8) p) :
    ¬ cleanE1 r p ∧ ¬ cleanE3 r p ∧ ¬ WB r p ∧ ¬ WC5 r p ∧ ¬ WC7 r p := by
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
  · have := c.2.2.1; rcases h with c' | c' <;> omega
  · have := c.2.2.1; have := c.2.2.2.1; rcases h with c' | c' <;> omega
  · have := c.2.1; rcases h with c' | c' <;> omega
  · obtain ⟨_, _, _, _, _⟩ := c; rcases h with c' | c' <;> omega
  · obtain ⟨_, _, _, _⟩ := c; rcases h with c' | c' <;> omega

theorem lam_defHypT_all3 {r : ℕ} (hr : 16 ≤ r) :
    ∃ δ : ℕ → ℕ, DefHypT lamInst r (r / 8) (Tfun3 r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) ∧
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) ∧
      (∀ p, WC7 r p → δ p = p + (3 * p + 1) / 4 - r - r / 8) ∧
      (∀ p, LowClean r (r / 8) p → δ p = r / 8) := by
  classical
  obtain ⟨δ0, h0, h1, h3, hB, hC5⟩ := lam_defHypT_all2 hr
  have hT0 : ∀ p, Tfun2 r p ≤ Tfun3 r p := fun p => le_max_left _ _
  have h0' : DefHypT lamInst r (r / 8) (Tfun3 r) δ0 := h0.mono_T fun p _ _ => hT0 p
  have hTr : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ Tfun3 r p :=
    fun p _ _ => le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (hT0 p))
  have hC7 := defHypT_C7 lamInst lamData r (r / 8) (Tfun3 r) (WC7 r)
    (fun p _ hW => ⟨_, csetup7_of_wc7 hr hW⟩) hTr
    (fun p hp hW k S => by
      have hk : k = (3 * p + 1) / 4 := by have := S.hk; omega
      rw [wC7_dual_eq S]
      refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
      simp only [eC7, if_pos hW, hk]
      omega)
  have hGK := defHypT_GK lamInst lamData r (r / 8) (by omega) (Tfun3 r) hTr
    (fun p _ hW => by
      refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
      simp only [eGK, if_pos hW]
      omega)
  have hA := h0'.glue (WC7 r) hC7
  have hAll := hA.glue (fun p => LowClean r (r / 8) p) hGK
  refine ⟨_, hAll, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hc
    have n7 : ¬ WC7 r p := fun h => (wc7_disj hr h).1 hc
    have nl : ¬ LowClean r (r / 8) p := fun h => (lc_disj hr h).1 hc
    simp only [if_neg n7, if_neg nl]; exact h1 p hc
  · intro p hc
    have n7 : ¬ WC7 r p := fun h => (wc7_disj hr h).2.1 hc
    have nl : ¬ LowClean r (r / 8) p := fun h => (lc_disj hr h).2.1 hc
    simp only [if_neg n7, if_neg nl]; exact h3 p hc
  · intro p hc
    have n7 : ¬ WC7 r p := fun h => (wc7_disj hr h).2.2.1 hc
    have nl : ¬ LowClean r (r / 8) p := fun h => (lc_disj hr h).2.2.1 hc
    simp only [if_neg n7, if_neg nl]; exact hB p hc
  · intro p hc
    have n7 : ¬ WC7 r p := fun h => (wc7_disj hr h).2.2.2.1 hc
    have nl : ¬ LowClean r (r / 8) p := fun h => (lc_disj hr h).2.2.2.1 hc
    simp only [if_neg n7, if_neg nl]; exact hC5 p hc
  · intro p hc
    have nl : ¬ LowClean r (r / 8) p := (wc7_disj hr hc).2.2.2.2
    simp only [if_neg nl, if_pos hc]
  · intro p hc
    simp only [if_pos hc]

end CatalanFrames.Lambda
