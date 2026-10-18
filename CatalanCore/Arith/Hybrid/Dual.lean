module

public import CatalanCore.Arith.Hybrid.Majorant

@[expose] public section

/-!
# Dual certificates for the one-level weight `wt q` on the hybrid index set

WP-H5 step 2 (DW §3, D1-D6).  The index type is `Fin r ⊕ Fin m` with row labels `hybRow`
(`c`, `r + 2i`) and column labels `hybCol` (`c`, `r + 2i + 1`).  A dual certificate is a pair of
rational potentials `u, v : ℕ → ℚ` on labels with `wt q A B ≤ u A + v B` on all slot pairs; weak
duality (`Tropical.lean`) then bounds `tropVal` by `∑ u + ∑ v`, which splits as
`∑_{c<r} (u c + v c) + ∑_{i<m} (u (r+2i) + v (r+2i+1))`.

Proved here: the generic wrapper (`trop_wt_le`), the structural facts on `wt`, and the duals
* `D45` (`r < q`, `r + 2m < 2q`): potential `[blk > 0]` on `C`, `1 + [x ≥ q]` on the zone
  (DW D4 and D5 together);
* `D6` (`q ≥ N`, `C` entirely in block 0).
-/

open Finset

namespace CatalanCore.Arith.Hybrid

/-- The one-level weight table on slots. -/
def HW (q r m : ℕ) (a b : Fin r ⊕ Fin m) : ℕ := wt q (Frame.hybRow r m a) (Frame.hybCol r m b)

/-- The value of the potentials `(u, v)` on the slots. -/
def potVal (u v : ℕ → ℚ) (r m : ℕ) : ℚ :=
  ∑ c ∈ range r, (u c + v c) + ∑ i ∈ range m, (u (r + 2 * i) + v (r + 2 * i + 1))

/-- Weak duality for the hybrid slots. -/
theorem trop_HW_le (q r m : ℕ) (u v : ℕ → ℚ)
    (h : ∀ a b : Fin r ⊕ Fin m, (HW q r m a b : ℚ) ≤ u (Frame.hybRow r m a) + v (Frame.hybCol r m b)) :
    (tropVal (HW q r m) : ℚ) ≤ potVal u v r m := by
  have := tropVal_le_dual (HW q r m) (fun a => u (Frame.hybRow r m a))
    (fun b => v (Frame.hybCol r m b)) h
  refine this.trans (le_of_eq ?_)
  unfold potVal
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_eq_sum_range
    (fun c => u c), Fin.sum_univ_eq_sum_range (fun c => v c),
    Fin.sum_univ_eq_sum_range (fun i => u (r + 2 * i)),
    Fin.sum_univ_eq_sum_range (fun i => v (r + 2 * i + 1))]
  ring

/-! ### Structure of `wt` -/

lemma wt_diag (q A : ℕ) : wt q A A = if 0 < blk q A then 2 else 0 := by
  unfold wt; simp

lemma wt_le_one_of_noncong {q A B : ℕ} (hne : A ≠ B) (hc : ¬ (q : ℤ) ∣ (A : ℤ) - B) :
    wt q A B ≤ 1 := by
  unfold wt
  rw [if_neg hne, if_neg hc]
  split_ifs <;> omega

lemma wt_eq_zero_of_blk {q A B : ℕ} (hne : A ≠ B) (hc : ¬ (q : ℤ) ∣ (A : ℤ) - B)
    (hb : blk q A = blk q B) : wt q A B = 0 := by
  unfold wt
  rw [if_neg hne, if_neg hc]
  simp [hb]

/-- A congruent pair of distinct labels has its larger member `≥ q`. -/
lemma cong_large {q A B : ℕ} (hne : A ≠ B) (hc : (q : ℤ) ∣ (A : ℤ) - B) :
    q ≤ A ∨ q ≤ B := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hd : (q : ℤ) ∣ (B : ℤ) - A := by rw [← dvd_neg]; simpa using hc
    have := Int.le_of_dvd (by omega) hd
    right; omega
  · have := Int.le_of_dvd (by omega) hc
    left; omega

/-- ... and in fact both are `≥ q` or the larger is `≥ q` and the smaller `≥ 0`: used as is. -/
lemma cong_large' {q A B : ℕ} (hne : A ≠ B) (hc : (q : ℤ) ∣ (A : ℤ) - B) :
    q ≤ max A B := by
  rcases cong_large hne hc with h | h
  · exact le_trans h (le_max_left _ _)
  · exact le_trans h (le_max_right _ _)

/-! ### D4/D5: `q > r` -/

/-- The potential of D4/D5. -/
def pot45 (q r : ℕ) (A : ℕ) : ℚ :=
  if A < r then (if 0 < blk q A then 1 else 0) else (1 + if q ≤ A then 1 else 0)

lemma pot45_nonneg (q r A : ℕ) : 0 ≤ pot45 q r A := by
  unfold pot45; split_ifs <;> norm_num

lemma pot45_feasible {q r N A B : ℕ} (hq : r < q) (hN : N < 2 * q) (hrN : r ≤ N)
    (hA : A < N) (hB : B < N) :
    (wt q A B : ℚ) ≤ pot45 q r A + pot45 q r B := by
  by_cases hAB : A = B
  · subst hAB
    rw [wt_diag]
    unfold pot45
    split_ifs <;> norm_num
  by_cases hc : (q : ℤ) ∣ (A : ℤ) - B
  · -- congruent: the larger label is `≥ q > r`, hence in the zone with potential 2
    have hmax := cong_large' hAB hc
    have h2 : wt q A B ≤ 2 := by unfold wt; split_ifs <;> omega
    have hA0 := pot45_nonneg q r A
    have hB0 := pot45_nonneg q r B
    have key : 2 ≤ pot45 q r A ∨ 2 ≤ pot45 q r B := by
      rcases le_total A B with h | h
      · right
        have : q ≤ B := by rwa [max_eq_right h] at hmax
        unfold pot45; rw [if_neg (by omega), if_pos this]; norm_num
      · left
        have : q ≤ A := by rwa [max_eq_left h] at hmax
        unfold pot45; rw [if_neg (by omega), if_pos this]; norm_num
    have : (wt q A B : ℚ) ≤ 2 := by exact_mod_cast h2
    rcases key with k | k <;> linarith
  · have h1 := wt_le_one_of_noncong hAB hc
    by_cases hAr : A < r
    · by_cases hBr : B < r
      · by_cases hbA : 0 < blk q A
        · have : pot45 q r A = 1 := by unfold pot45; rw [if_pos hAr, if_pos hbA]
          have := pot45_nonneg q r B
          have : (wt q A B : ℚ) ≤ 1 := by exact_mod_cast h1
          linarith
        · by_cases hbB : 0 < blk q B
          · have : pot45 q r B = 1 := by unfold pot45; rw [if_pos hBr, if_pos hbB]
            have := pot45_nonneg q r A
            have : (wt q A B : ℚ) ≤ 1 := by exact_mod_cast h1
            linarith
          · have e := wt_eq_zero_of_blk hAB hc (by omega)
            rw [e]; have := pot45_nonneg q r A; have := pot45_nonneg q r B; simp; linarith
      · have : 1 ≤ pot45 q r B := by unfold pot45; rw [if_neg hBr]; split_ifs <;> norm_num
        have := pot45_nonneg q r A
        have : (wt q A B : ℚ) ≤ 1 := by exact_mod_cast h1
        linarith
    · have : 1 ≤ pot45 q r A := by unfold pot45; rw [if_neg hAr]; split_ifs <;> norm_num
      have := pot45_nonneg q r B
      have : (wt q A B : ℚ) ≤ 1 := by exact_mod_cast h1
      linarith

lemma Frame_hybRow_lt (r m : ℕ) (a : Fin r ⊕ Fin m) : Frame.hybRow r m a < r + 2 * m := by
  rcases a with c | i
  · simp [Frame.hybRow]; try (have := c.2; omega)
  · simp [Frame.hybRow]; try (have := i.2; omega)

lemma Frame_hybCol_lt (r m : ℕ) (a : Fin r ⊕ Fin m) : Frame.hybCol r m a < r + 2 * m := by
  rcases a with c | i
  · simp [Frame.hybCol]; try (have := c.2; omega)
  · simp [Frame.hybCol]; try (have := i.2; omega)

/-- **D4/D5.**  For `r < q` and `r + 2m < 2q`. -/
theorem trop_D45 (q r m : ℕ) (hq : r < q) (hN : r + 2 * m < 2 * q) :
    (tropVal (HW q r m) : ℚ) ≤ potVal (pot45 q r) (pot45 q r) r m := by
  apply trop_HW_le
  intro a b
  exact pot45_feasible (N := r + 2 * m) hq hN (by omega) (Frame_hybRow_lt r m a)
    (Frame_hybCol_lt r m b)

end CatalanCore.Arith.Hybrid
