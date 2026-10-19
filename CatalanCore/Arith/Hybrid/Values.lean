module

public import CatalanCore.Arith.Hybrid.Dual3

@[expose] public section

/-!
# Values of the duals

For a prime `q` with first singular index `k` (`hlow : lev q c = 0 ↔ c < k`), the explicit
bounds (all in `ℕ`, truncated subtraction) on `tropVal (HW lev q r m)`:

* `val_D45`  (`r < q`):       `2 (r - k) + 2 m + (2m - (q - r))`   [DW D4/D5];
* `val_D6`   (`r + 2m ≤ q`, `r ≤ k`): `2m - (k - r)`               [DW D6];
* `val_D2`   (`2m < q ≤ r`, `k ≤ r`): `∃ u L, k + q ≤ u + r, u ≤ r, L ≤ min(u, 2m)`,
  value `2 (r - u) + 2m + L`                                       [DW D2];
* `val_D3`   (`2m < q ≤ r`): `2 r + m`                              [DW D3].
-/

open Finset

namespace CatalanCore.Arith.Hybrid

variable {lev : ℕ → ℕ → ℕ}

lemma zone_sum (f : ℕ → ℚ) (r m : ℕ) :
    ∑ i ∈ range m, (f (r + 2 * i) + f (r + 2 * i + 1)) = ∑ j ∈ range (2 * m), f (r + j) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [add_assoc]

lemma potVal_sym (f : ℕ → ℚ) (r m : ℕ) :
    potVal f f r m = 2 * ∑ c ∈ range r, f c + ∑ j ∈ range (2 * m), f (r + j) := by
  unfold potVal
  rw [zone_sum, show ∑ c ∈ range r, (f c + f c) = 2 * ∑ c ∈ range r, f c by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring]

/-- Number of `j < n` with `a ≤ j + b`, at most `n - (a - b)` (truncated). -/
lemma card_filter_le (n a b : ℕ) :
    ((range n).filter (fun j => a ≤ b + j)).card ≤ n - (a - b) := by
  calc _ ≤ (Ico (a - b) n).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp only [Finset.mem_Ico]
        omega
    _ = n - (a - b) := Nat.card_Ico _ _

variable (q r m k : ℕ)

theorem val_D45 (hq : r < q) (hmr : 2 * m ≤ r) (hlow : ∀ c, lev q c = 0 ↔ c < k) :
    tropVal (HW lev q r m) ≤ 2 * (r - k) + 2 * m + (2 * m - (q - r)) := by
  have h := trop_D45 (lev := lev) q r m hq (by omega)
  rw [potVal_sym] at h
  have hC : ∑ c ∈ range r, pot45 lev q r c = (((range r).filter (fun c => 0 < lev q c)).card : ℚ) := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro c hc
    have := Finset.mem_range.mp hc
    unfold pot45
    rw [if_pos this]
  have hZ : ∑ j ∈ range (2 * m), pot45 lev q r (r + j) =
      (2 * m : ℚ) + (((range (2 * m)).filter (fun j => q ≤ r + j)).card : ℚ) := by
    rw [Finset.card_filter]
    push_cast
    rw [show (2 * m : ℚ) = ∑ _j ∈ range (2 * m), (1 : ℚ) by simp]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold pot45
    rw [if_neg (by omega)]
  have hc1 : ((range r).filter (fun c => 0 < lev q c)).card ≤ r - k := by
    calc _ ≤ (Ico k r).card := by
          apply Finset.card_le_card
          intro c hc
          simp only [Finset.mem_filter, Finset.mem_range] at hc
          simp only [Finset.mem_Ico]
          refine ⟨?_, hc.1⟩
          by_contra hh
          have := (hlow c).mpr (by omega)
          omega
      _ = r - k := Nat.card_Ico _ _
  have hz1 := card_filter_le (2 * m) q r
  rw [hC, hZ] at h
  have : (tropVal (HW lev q r m) : ℚ) ≤
      ((2 * (r - k) + 2 * m + (2 * m - (q - r)) : ℕ) : ℚ) := by
    push_cast
    have a1 : ((((range r).filter (fun c => 0 < lev q c)).card : ℕ) : ℚ) ≤ ((r - k : ℕ) : ℚ) := by
      exact_mod_cast hc1
    have a2 : ((((range (2 * m)).filter (fun j => q ≤ r + j)).card : ℕ) : ℚ) ≤
        ((2 * m - (q - r) : ℕ) : ℚ) := by exact_mod_cast hz1
    linarith
  exact_mod_cast this

theorem val_D6 (hq : r + 2 * m ≤ q) (hk : r ≤ k) (hlow : ∀ c, lev q c = 0 ↔ c < k) :
    tropVal (HW lev q r m) ≤ 2 * m - (k - r) := by
  have h := trop_D6 (lev := lev) q r m hq (fun c hc => (hlow c).mpr (by omega))
  rw [potVal_sym] at h
  have hC : ∑ c ∈ range r, pot6 lev q r c = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have := Finset.mem_range.mp hc
    unfold pot6
    rw [if_neg (by omega)]
  have hZ : ∑ j ∈ range (2 * m), pot6 lev q r (r + j) =
      (((range (2 * m)).filter (fun j => k ≤ r + j)).card : ℚ) := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    unfold pot6
    by_cases hj : k ≤ r + j
    · have : 0 < lev q (r + j) := by
        by_contra hh
        have := (hlow (r + j)).mp (by omega)
        omega
      rw [if_pos ⟨by omega, this⟩, if_pos hj]
    · have : lev q (r + j) = 0 := (hlow _).mpr (by omega)
      rw [if_neg (by omega), if_neg hj]
  have hz1 := card_filter_le (2 * m) k r
  rw [hC, hZ] at h
  have : (tropVal (HW lev q r m) : ℚ) ≤ ((2 * m - (k - r) : ℕ) : ℚ) := by
    have a2 : ((((range (2 * m)).filter (fun j => k ≤ r + j)).card : ℕ) : ℚ) ≤
        ((2 * m - (k - r) : ℕ) : ℚ) := by exact_mod_cast hz1
    linarith
  exact_mod_cast this


theorem val_D2 (hq1 : 1 ≤ q) (hh : ∀ c, q ≤ c → 0 < lev q c) (hm : 2 * m < q) (hqr : q ≤ r)
    (hkr : k ≤ r) (hlow : ∀ c, lev q c = 0 ↔ c < k) :
    ∃ u L : ℕ, k + q ≤ u + r ∧ u ≤ r ∧ L ≤ u ∧ L ≤ 2 * m ∧
      tropVal (HW lev q r m) ≤ 2 * (r - u) + 2 * m + L := by
  have h := trop_D2 (lev := lev) q r m hq1 hh hm hqr
  rw [potVal_sym] at h
  set U : Finset ℕ := (range r).filter (fun c => lev q c = 0 ∧ r ≤ c + q) with hU
  set Lset : Finset ℕ := (range (2 * m)).filter (fun j => lev q (r + j - q) = 0) with hL
  refine ⟨U.card, Lset.card, ?_, ?_, ?_, ?_, ?_⟩
  · -- k + q ≤ |U| + r
    by_cases hk : r ≤ k + q
    · have hsub : Ico (r - q) k ⊆ U := by
        intro c hc
        simp only [Finset.mem_Ico] at hc
        simp only [hU, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, (hlow c).mpr hc.2, by omega⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Ico] at this
      omega
    · omega
  · have : U.card ≤ (range r).card := Finset.card_filter_le _ _
    simpa using this
  · -- L ≤ |U|
    apply Finset.card_le_card_of_injOn (fun j => r + j - q)
    · intro j hj
      simp only [hL, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj
      simp only [hU, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      exact ⟨by omega, hj.2, by omega⟩
    · intro j1 _ j2 _ hj
      simp only at hj
      omega
  · have : Lset.card ≤ (range (2 * m)).card := Finset.card_filter_le _ _
    simpa using this
  · have hC : ∑ c ∈ range r, pot2 lev q r c = (r : ℚ) - (U.card : ℚ) := by
      rw [hU, Finset.card_filter]
      push_cast
      rw [show (r : ℚ) = ∑ _c ∈ range r, (1 : ℚ) by simp, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      have := Finset.mem_range.mp hc
      unfold pot2
      rw [if_pos this]
      split_ifs <;> norm_num
    have hZ : ∑ j ∈ range (2 * m), pot2 lev q r (r + j) = (2 * m : ℚ) + (Lset.card : ℚ) := by
      rw [hL, Finset.card_filter]
      push_cast
      rw [show (2 * m : ℚ) = ∑ _j ∈ range (2 * m), (1 : ℚ) by simp, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      unfold pot2
      rw [if_neg (by omega)]
      try (split_ifs <;> norm_num)
    rw [hC, hZ] at h
    have hu : U.card ≤ r := by
      have : U.card ≤ (range r).card := Finset.card_filter_le _ _
      simpa using this
    have : (tropVal (HW lev q r m) : ℚ) ≤ ((2 * (r - U.card) + 2 * m + Lset.card : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub hu]
      linarith
    exact_mod_cast this


/-! ### D3 -/

theorem trop_D3 (hq1 : 1 ≤ q) (hh : ∀ c, q ≤ c → 0 < lev q c) (hm : 2 * m < q) (hqr : q ≤ r) :
    (tropVal (HW lev q r m) : ℚ) ≤ potVal (rowpot3 lev q r m) (colpot3 lev q r m) r m := by
  apply trop_HW_le
  intro a b
  rcases a with c | i <;> rcases b with c' | j
  · simp only [HW, Frame.hybRow, Frame.hybCol, Sum.elim_inl]
    exact feas_CC hq1 hh c.2 c'.2
  · simp only [HW, Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr]
    exact feas_CY hq1 hh hm c.2 j.2
  · simp only [HW, Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr]
    exact feas_XC hq1 hh hm i.2 c'.2
  · simp only [HW, Frame.hybRow, Frame.hybCol, Sum.elim_inr]
    exact feas_XY hm i.2 j.2

lemma not_HR_of_low (hm : 2 * m < q) (hqr : q ≤ r) {j : ℕ} (hj : j < 2 * m)
    (hl : lev q (r + j - q) = 0) : ¬ HR lev q r m (r + j - q) := by
  rintro ⟨i, hi, hb, hd⟩
  have h0 := Int.eq_zero_of_abs_lt_dvd (m := (q : ℤ))
    (x := ((r + j - q : ℕ) : ℤ) - ((r + 2 * i : ℕ) : ℤ) + q)
    (by
      have : (q : ℤ) ∣ q := dvd_refl _
      exact dvd_add hd this) (by rw [abs_lt]; push_cast; constructor <;> omega)
  have : r + j - q = r + 2 * i - q := by omega
  rw [← this] at hb
  omega

lemma not_HC_of_low (hm : 2 * m < q) (hqr : q ≤ r) {j : ℕ} (hj : j < 2 * m)
    (hl : lev q (r + j - q) = 0) : ¬ HC lev q r m (r + j - q) := by
  rintro ⟨i, hi, hb, hd⟩
  have h0 := Int.eq_zero_of_abs_lt_dvd (m := (q : ℤ))
    (x := ((r + j - q : ℕ) : ℤ) - ((r + 2 * i + 1 : ℕ) : ℤ) + q)
    (by
      have : (q : ℤ) ∣ q := dvd_refl _
      exact dvd_add hd this) (by rw [abs_lt]; push_cast; constructor <;> omega)
  have : r + j - q = r + 2 * i + 1 - q := by omega
  rw [← this] at hb
  omega

theorem val_D3 (hq1 : 1 ≤ q) (hh : ∀ c, q ≤ c → 0 < lev q c) (hm : 2 * m < q) (hqr : q ≤ r) :
    tropVal (HW lev q r m) ≤ 2 * r + m := by
  have h := trop_D3 (lev := lev) q r m hq1 hh hm hqr
  unfold potVal at h
  set Lset : Finset ℕ := (range (2 * m)).filter (fun j => lev q (r + j - q) = 0) with hL
  set T : Finset ℕ := Lset.image (fun j => r + j - q) with hT
  have hTcard : T.card = Lset.card := by
    apply Finset.card_image_of_injOn
    intro j1 _ j2 _ hj
    simp only at hj
    omega
  have hTsub : T ⊆ range r := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    simp only [hL, Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  -- zone part
  set F : ℕ → ℚ := fun x => if 0 < lev q (x - q) then 1 / 2 else 3 / 2 with hF
  have hzone : ∑ i ∈ range m, (rowpot3 lev q r m (r + 2 * i) + colpot3 lev q r m (r + 2 * i + 1)) =
      ∑ i ∈ range m, (F (r + 2 * i) + F (r + 2 * i + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    have n1 : ¬ (r + 2 * i < r) := by omega
    have n2 : ¬ (r + 2 * i + 1 < r) := by omega
    simp only [rowpot3, colpot3, n1, n2, if_false, hF, Nat.add_sub_cancel]
  have hFsum : ∑ j ∈ range (2 * m), F (r + j) = (m : ℚ) + (Lset.card : ℚ) := by
    rw [hL, Finset.card_filter]
    push_cast
    have : ∀ j ∈ range (2 * m), F (r + j) = 1 / 2 + (if lev q (r + j - q) = 0 then 1 else 0) := by
      intro j _
      simp only [hF]
      by_cases h0 : lev q (r + j - q) = 0
      · rw [if_neg (by omega), if_pos h0]; norm_num
      · rw [if_pos (by omega), if_neg h0]; norm_num
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    simp
    ring
  -- C part
  have hg : ∀ c ∈ range r, rowpot3 lev q r m c + colpot3 lev q r m c ≤
      2 - (if c ∈ T then 1 else 0) := by
    intro c hc
    have hcr := Finset.mem_range.mp hc
    by_cases hcT : c ∈ T
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hcT
      simp only [hL, Finset.mem_filter, Finset.mem_range] at hj
      have hnR := not_HR_of_low q r m hm hqr hj.1 hj.2
      have hnC := not_HC_of_low q r m hm hqr hj.1 hj.2
      have hlift : lev q (r + j - q) = 0 ∧ r ≤ (r + j - q) + q := ⟨hj.2, by omega⟩
      simp only [rowpot3, colpot3, if_pos hcr, if_neg hnR, if_neg hnC, if_pos hlift, if_pos hcT]
      norm_num
    · simp only [if_neg hcT]
      simp only [rowpot3, colpot3, if_pos hcr]
      by_cases hR : HR lev q r m c
      · simp only [if_pos hR]; norm_num
      · by_cases hC : HC lev q r m c
        · simp only [if_neg hR, if_pos hC]; norm_num
        · by_cases hl : lev q c = 0 ∧ r ≤ c + q
          · simp only [if_neg hR, if_neg hC, if_pos hl]; norm_num
          · simp only [if_neg hR, if_neg hC, if_neg hl]; norm_num
  have hCsum : ∑ c ∈ range r, (rowpot3 lev q r m c + colpot3 lev q r m c) ≤ 2 * r - Lset.card := by
    calc _ ≤ ∑ c ∈ range r, (2 - (if c ∈ T then (1 : ℚ) else 0)) := Finset.sum_le_sum hg
      _ = 2 * r - (T.card : ℚ) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← Finset.sum_filter]
        have : (range r).filter (fun c => c ∈ T) = T := by
          ext c; simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · exact fun h => h.2
          · intro hc; exact ⟨Finset.mem_range.mp (hTsub hc), hc⟩
        rw [this]; simp; ring
      _ = _ := by rw [hTcard]
  rw [hzone, zone_sum F r m, hFsum] at h
  have : (tropVal (HW lev q r m) : ℚ) ≤ ((2 * r + m : ℕ) : ℚ) := by
    push_cast; linarith
  exact_mod_cast this

end CatalanCore.Arith.Hybrid
