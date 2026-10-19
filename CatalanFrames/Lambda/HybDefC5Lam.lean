module

public import CatalanFrames.Lambda.HybDefSum2
public import CatalanCore.Arith.Hybrid.DefSum

@[expose] public section

/-!
# λ: C5 wired into the combined `DefHypT` family

* `wC_dual_eq`: the dual value `∑ wC (rows) + ∑ wC (cols)` of the D2 potentials is
  `2r + 2m - L`, `L = p + k - r` (`CSetup`);
* `lam_defHypT_all2`: `B + E (both classes) + C5` as ONE `DefHypT` family with `T = Tfun2 = max Tfun eC5`.
The family is obtained from `lam_defHypT_all` by `DefHypT.mono_T` and `DefHypT.glue`; further
families (C7, GK) are plugged in the same way.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma sum_range_gap (n q k : ℕ) (hqk : q ≤ k) :
    ∑ i ∈ Finset.range n, (if q ≤ i ∧ i < k then 0 else 1) + (min n k - min n q) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    split_ifs <;> omega

lemma sum_range_two (n q : ℕ) :
    ∑ i ∈ Finset.range n, (if i < q then 2 else 1) = n + min n q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

/-- The dual value of the D2 potentials. -/
lemma wC_dual_eq {p r m k : ℕ} (S : CSetup p r m k) :
    ∑ a : Fin r ⊕ Fin m, wC p r k (Frame.hybRow r m a) +
      ∑ b : Fin r ⊕ Fin m, wC p r k (Frame.hybCol r m b) = 2 * r + 2 * m - (p + k - r) := by
  have hk := S.hk
  have hLlo := S.hLlo
  have hLhi := S.hLhi
  have hrp := S.hrp
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hc : ∑ c : Fin r, wC p r k (c : ℕ) = r - (p + k - r) := by
    have : ∀ c : Fin r, wC p r k (c : ℕ) = if r - p ≤ (c : ℕ) ∧ (c : ℕ) < k then 0 else 1 :=
      fun c => by unfold wC; rw [if_pos c.2]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if r - p ≤ i ∧ i < k then 0 else 1) r]
    have := sum_range_gap r (r - p) k (by omega)
    omega
  have hzr : ∑ i : Fin m, wC p r k (Frame.hybRow r m (Sum.inr i)) =
      m + min m ((p + k - r + 1) / 2) := by
    have : ∀ i : Fin m, wC p r k (Frame.hybRow r m (Sum.inr i)) =
        if (i : ℕ) < (p + k - r + 1) / 2 then 2 else 1 := fun i => by
      show wC p r k (r + 2 * (i : ℕ)) = _
      unfold wC
      rw [if_neg (by omega)]
      by_cases h : (i : ℕ) < (p + k - r + 1) / 2
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (p + k - r + 1) / 2 then 2 else 1) m,
      sum_range_two]
  have hzc : ∑ i : Fin m, wC p r k (Frame.hybCol r m (Sum.inr i)) =
      m + min m ((p + k - r) / 2) := by
    have : ∀ i : Fin m, wC p r k (Frame.hybCol r m (Sum.inr i)) =
        if (i : ℕ) < (p + k - r) / 2 then 2 else 1 := fun i => by
      show wC p r k (r + 2 * (i : ℕ) + 1) = _
      unfold wC
      rw [if_neg (by omega)]
      by_cases h : (i : ℕ) < (p + k - r) / 2
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (p + k - r) / 2 then 2 else 1) m,
      sum_range_two]
  have hcc : ∑ c : Fin r, wC p r k (Frame.hybCol r m (Sum.inl c)) = r - (p + k - r) := hc
  have hrr : ∑ c : Fin r, wC p r k (Frame.hybRow r m (Sum.inl c)) = r - (p + k - r) := hc
  rw [hrr, hcc, hzr, hzc]
  omega

/-- The dual value of C5, `2r + 2m - L_p`, on the window. -/
noncomputable def eC5 (r p : ℕ) : ℕ := by
  classical exact if WC5 r p then 2 * r + 2 * (r / 8) - (p + (p + 1) / 4 - r) else 0

lemma csetup_of_wc5 {r p : ℕ} (hr : 16 ≤ r) (h : WC5 r p) : CSetup p r (r / 8) ((p + 1) / 4) := by
  obtain ⟨hp, h4, h1, h2, h3⟩ := h
  exact ⟨by omega, by omega, h3, by omega, by omega, by omega⟩

/-- `Tfun` with the C5 dual. -/
noncomputable def Tfun2 (r p : ℕ) : ℕ := max (Tfun r p) (eC5 r p)

theorem lam_defHypT_all2 {r : ℕ} (hr : 16 ≤ r) :
    ∃ δ : ℕ → ℕ, DefHypT lamInst r (r / 8) (Tfun2 r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) ∧
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) := by
  classical
  obtain ⟨δ0, h0, h1, h3, hB⟩ := lam_defHypT_all hr
  have h0' : DefHypT lamInst r (r / 8) (Tfun2 r) δ0 :=
    h0.mono_T fun p _ _ => le_max_left _ _
  have hC := defHypT_C5 lamInst lamData r (r / 8) (Tfun2 r) (WC5 r)
    (fun p _ hW => ⟨_, csetup_of_wc5 hr hW⟩)
    (fun p _ _ => le_trans (le_max_left _ _) (le_max_left _ _))
    (fun p hp hW k S => by
      have hk : k = (p + 1) / 4 := by have := S.hk; omega
      rw [wC_dual_eq S]
      refine le_trans ?_ (le_max_right _ _)
      simp only [eC5, if_pos hW, hk]
      omega)
  refine ⟨_, h0'.glue (WC5 r) hC, ?_, ?_, ?_, ?_⟩
  · intro p hc
    have : ¬ WC5 r p := fun hw => by have := hc.2.1; have := hw.2.1; omega
    simp only [if_neg this]; exact h1 p hc
  · intro p hc
    have : ¬ WC5 r p := fun hw => by have := hc.2.2.2.1; have := hw.2.2.2.2; have := hw.2.2.1; omega
    simp only [if_neg this]; exact h3 p hc
  · intro p hW
    have : ¬ WC5 r p := fun hw => by have := hW.2.1; have := hw.2.2.2.2; omega
    simp only [if_neg this]; exact hB p hW
  · intro p hW
    simp only [if_pos hW]

end CatalanFrames.Lambda
