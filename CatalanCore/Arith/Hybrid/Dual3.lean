module

public import CatalanCore.Arith.Hybrid.Kq

@[expose] public section

/-!
# Dual D3 (DW §3): asymmetric half-integer potentials, `2m < q ≤ r`

Rows and columns get different potentials on the residue class of every *high* zone node: the
class of a high `X'`-node `z` gets rows `1/2`, columns `3/2`; the class of a high `Y'`-node gets
the reverse; the unpaired low set `U = {c : blk c = 0, r ≤ c + q}` is lifted to `1/2 + 1/2`;
a low zone node gets `3/2`, a high one `1/2`.  Value `2r - |U| + m + L` with `L ≤ |U|`, hence
`tropVal (HW q r m) ≤ 2r + m` (`trop_D3`).
-/

open Finset Classical

namespace CatalanCore.Arith.Hybrid

section D3

variable (q r m : ℕ)

/-- The class of the label `A` contains a high `X'` node. -/
def HR (A : ℕ) : Prop :=
  ∃ i < m, 0 < blk q (r + 2 * i - q) ∧ (q : ℤ) ∣ (A : ℤ) - ((r + 2 * i : ℕ) : ℤ)

/-- The class of the label `A` contains a high `Y'` node. -/
def HC (A : ℕ) : Prop :=
  ∃ i < m, 0 < blk q (r + 2 * i + 1 - q) ∧ (q : ℤ) ∣ (A : ℤ) - ((r + 2 * i + 1 : ℕ) : ℤ)

/-- Row potential of D3. -/
noncomputable def rowpot3 (A : ℕ) : ℚ :=
  if A < r then
    (if HR q r m A then 1 / 2 else if HC q r m A then 3 / 2
      else if blk q A = 0 ∧ r ≤ A + q then 1 / 2 else 1)
  else (if 0 < blk q (A - q) then 1 / 2 else 3 / 2)

/-- Column potential of D3. -/
noncomputable def colpot3 (A : ℕ) : ℚ :=
  if A < r then
    (if HR q r m A then 3 / 2 else if HC q r m A then 1 / 2
      else if blk q A = 0 ∧ r ≤ A + q then 1 / 2 else 1)
  else (if 0 < blk q (A - q) then 1 / 2 else 3 / 2)

variable {q r m}

lemma rowpot3_ge (A : ℕ) : 1 / 2 ≤ rowpot3 q r m A := by
  unfold rowpot3; split_ifs <;> norm_num

lemma colpot3_ge (A : ℕ) : 1 / 2 ≤ colpot3 q r m A := by
  unfold colpot3; split_ifs <;> norm_num

lemma HR_congr {A B : ℕ} (h : (q : ℤ) ∣ (A : ℤ) - B) : HR q r m A ↔ HR q r m B := by
  have key : ∀ {A B : ℕ}, (q : ℤ) ∣ (A : ℤ) - B → HR q r m B → HR q r m A := by
    intro A B h ⟨i, hi, hb, hd⟩
    refine ⟨i, hi, hb, ?_⟩
    have : (A : ℤ) - ((r + 2 * i : ℕ) : ℤ) = ((A : ℤ) - B) + ((B : ℤ) - ((r + 2 * i : ℕ) : ℤ)) := by ring
    rw [this]; exact dvd_add h hd
  exact ⟨fun hA => key (by rw [← dvd_neg]; simpa using h) hA, key h⟩

lemma HC_congr {A B : ℕ} (h : (q : ℤ) ∣ (A : ℤ) - B) : HC q r m A ↔ HC q r m B := by
  have key : ∀ {A B : ℕ}, (q : ℤ) ∣ (A : ℤ) - B → HC q r m B → HC q r m A := by
    intro A B h ⟨i, hi, hb, hd⟩
    refine ⟨i, hi, hb, ?_⟩
    have : (A : ℤ) - ((r + 2 * i + 1 : ℕ) : ℤ) =
        ((A : ℤ) - B) + ((B : ℤ) - ((r + 2 * i + 1 : ℕ) : ℤ)) := by ring
    rw [this]; exact dvd_add h hd
  exact ⟨fun hA => key (by rw [← dvd_neg]; simpa using h) hA, key h⟩

/-- Two distinct labels in the zone window are never congruent (`2m < q`). -/
lemma zone_not_cong (hm : 2 * m < q) {A B : ℕ} (hA : r ≤ A) (hA' : A < r + 2 * m) (hB : r ≤ B)
    (hB' : B < r + 2 * m) (hne : A ≠ B) : ¬ (q : ℤ) ∣ (A : ℤ) - B := by
  intro hd
  have := cong_large hne hd
  rcases lt_or_gt_of_ne hne with h | h
  · have hd' : (q : ℤ) ∣ (B : ℤ) - A := by rw [← dvd_neg]; simpa using hd
    have := Int.le_of_dvd (by omega) hd'; omega
  · have := Int.le_of_dvd (by omega) hd; omega

lemma lift_no_partner (hq1 : 1 ≤ q) {c c' : ℕ} (hl : blk q c = 0 ∧ r ≤ c + q) (hc' : c' < r)
    (hd : (q : ℤ) ∣ (c : ℤ) - c') : c' = c := by
  have hcq : c < q := by
    by_contra h
    have := blk_pos_of_ge hq1 (show q ≤ c by omega)
    omega
  have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  omega

lemma wt_le_two' (A B : ℕ) : (wt q A B : ℚ) ≤ 2 := by exact_mod_cast wt_le_two q A B

lemma wt_le_one' {A B : ℕ} (hne : A ≠ B) (hc : ¬ (q : ℤ) ∣ (A : ℤ) - B) : (wt q A B : ℚ) ≤ 1 := by
  exact_mod_cast wt_le_one_of_noncong hne hc

/-- Both labels in `C`. -/
lemma feas_CC (hq1 : 1 ≤ q) {c c' : ℕ} (hc : c < r) (hc' : c' < r) :
    (wt q c c' : ℚ) ≤ rowpot3 q r m c + colpot3 q r m c' := by
  have h1 := rowpot3_ge (q := q) (r := r) (m := m) c
  have h2 := colpot3_ge (q := q) (r := r) (m := m) c'
  by_cases hcc : c = c'
  · subst hcc
    rw [wt_diag]
    by_cases hb : 0 < blk q c
    · rw [if_pos hb]
      unfold rowpot3 colpot3
      simp only [if_pos hc]
      by_cases hR : HR q r m c
      · simp only [if_pos hR]; norm_num
      · by_cases hC : HC q r m c
        · simp only [if_neg hR, if_pos hC]; norm_num
        · have : ¬ (blk q c = 0 ∧ r ≤ c + q) := fun h => by omega
          simp only [if_neg hR, if_neg hC, if_neg this]; norm_num
    · rw [if_neg hb]; push_cast; linarith
  · by_cases hd : (q : ℤ) ∣ (c : ℤ) - c'
    · have hw := wt_le_two' (q := q) c c'
      unfold rowpot3 colpot3
      simp only [if_pos hc, if_pos hc']
      by_cases hR : HR q r m c
      · have hR' : HR q r m c' := (HR_congr hd).mp hR
        simp only [if_pos hR, if_pos hR']; linarith
      · have hR' : ¬ HR q r m c' := fun h => hR ((HR_congr hd).mpr h)
        by_cases hC : HC q r m c
        · have hC' : HC q r m c' := (HC_congr hd).mp hC
          simp only [if_neg hR, if_pos hC, if_neg hR', if_pos hC']; linarith
        · have hC' : ¬ HC q r m c' := fun h => hC ((HC_congr hd).mpr h)
          have n1 : ¬ (blk q c = 0 ∧ r ≤ c + q) := fun h => hcc (lift_no_partner hq1 h hc' hd).symm
          have hd' : (q : ℤ) ∣ (c' : ℤ) - c := by rw [← dvd_neg]; simpa using hd
          have n2 : ¬ (blk q c' = 0 ∧ r ≤ c' + q) := fun h => hcc (lift_no_partner hq1 h hc hd')
          simp only [if_neg hR, if_neg hC, if_neg n1, if_neg hR', if_neg hC', if_neg n2]; linarith
    · have := wt_le_one' hcc hd
      linarith

/-- Row in `C`, column a zone `Y'` node. -/
lemma feas_CY (hq1 : 1 ≤ q) (hm : 2 * m < q) {c j : ℕ} (hc : c < r) (hj : j < m) :
    (wt q c (r + 2 * j + 1) : ℚ) ≤ rowpot3 q r m c + colpot3 q r m (r + 2 * j + 1) := by
  have h1 := rowpot3_ge (q := q) (r := r) (m := m) c
  have h2 := colpot3_ge (q := q) (r := r) (m := m) (r + 2 * j + 1)
  have hw := wt_le_two' (q := q) c (r + 2 * j + 1)
  have hy : colpot3 q r m (r + 2 * j + 1) =
      (if 0 < blk q (r + 2 * j + 1 - q) then 1 / 2 else 3 / 2) := by
    unfold colpot3; rw [if_neg (by omega)]
  by_cases hlow : 0 < blk q (r + 2 * j + 1 - q)
  · rw [hy, if_pos hlow]
    by_cases hd : (q : ℤ) ∣ (c : ℤ) - ((r + 2 * j + 1 : ℕ) : ℤ)
    · have hHC : HC q r m c := (HC_congr hd).mpr ⟨j, hj, hlow, by simp⟩
      have hnR : ¬ HR q r m c := by
        rintro ⟨i, hi, -, hdi⟩
        have hzz : (q : ℤ) ∣ ((r + 2 * i : ℕ) : ℤ) - ((r + 2 * j + 1 : ℕ) : ℤ) := by
          have : ((r + 2 * i : ℕ) : ℤ) - ((r + 2 * j + 1 : ℕ) : ℤ) =
              ((c : ℤ) - ((r + 2 * j + 1 : ℕ) : ℤ)) - ((c : ℤ) - ((r + 2 * i : ℕ) : ℤ)) := by ring
          rw [this]; exact dvd_sub hd hdi
        exact zone_not_cong (r := r) hm (A := r + 2 * i) (B := r + 2 * j + 1) (by omega) (by omega) (by omega) (by omega) (by omega) hzz
      have : rowpot3 q r m c = 3 / 2 := by
        unfold rowpot3; rw [if_pos hc, if_neg hnR, if_pos hHC]
      rw [this]; linarith
    · have hne : c ≠ r + 2 * j + 1 := by omega
      have := wt_le_one' (q := q) hne hd
      linarith
  · rw [hy, if_neg hlow]; linarith

/-- Row a zone `X'` node, column in `C`. -/
lemma feas_XC (hq1 : 1 ≤ q) (hm : 2 * m < q) {i c : ℕ} (hi : i < m) (hc : c < r) :
    (wt q (r + 2 * i) c : ℚ) ≤ rowpot3 q r m (r + 2 * i) + colpot3 q r m c := by
  have h1 := rowpot3_ge (q := q) (r := r) (m := m) (r + 2 * i)
  have h2 := colpot3_ge (q := q) (r := r) (m := m) c
  have hw := wt_le_two' (q := q) (r + 2 * i) c
  have hx : rowpot3 q r m (r + 2 * i) =
      (if 0 < blk q (r + 2 * i - q) then 1 / 2 else 3 / 2) := by
    unfold rowpot3; rw [if_neg (by omega)]
  by_cases hlow : 0 < blk q (r + 2 * i - q)
  · rw [hx, if_pos hlow]
    by_cases hd : (q : ℤ) ∣ ((r + 2 * i : ℕ) : ℤ) - c
    · have hd' : (q : ℤ) ∣ (c : ℤ) - ((r + 2 * i : ℕ) : ℤ) := by rw [← dvd_neg]; simpa using hd
      have hHR : HR q r m c := ⟨i, hi, hlow, hd'⟩
      have : colpot3 q r m c = 3 / 2 := by
        unfold colpot3; rw [if_pos hc, if_pos hHR]
      rw [this]; linarith
    · have hne : r + 2 * i ≠ c := by omega
      have := wt_le_one' (q := q) hne hd
      linarith
  · rw [hx, if_neg hlow]; linarith

/-- Row `X'`, column `Y'`. -/
lemma feas_XY (hm : 2 * m < q) {i j : ℕ} (hi : i < m) (hj : j < m) :
    (wt q (r + 2 * i) (r + 2 * j + 1) : ℚ) ≤
      rowpot3 q r m (r + 2 * i) + colpot3 q r m (r + 2 * j + 1) := by
  have h1 := rowpot3_ge (q := q) (r := r) (m := m) (r + 2 * i)
  have h2 := colpot3_ge (q := q) (r := r) (m := m) (r + 2 * j + 1)
  have := wt_le_one' (q := q) (A := r + 2 * i) (B := r + 2 * j + 1) (by omega)
    (zone_not_cong (r := r) hm (A := r + 2 * i) (B := r + 2 * j + 1) (by omega) (by omega) (by omega) (by omega) (by omega))
  linarith

end D3

end CatalanCore.Arith.Hybrid
