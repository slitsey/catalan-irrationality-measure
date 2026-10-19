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

/-! ### D1 (trivial form): `u = v = 1` -/

theorem trop_D1 (q r m : ℕ) : (tropVal (HW q r m) : ℚ) ≤ 2 * ((r : ℚ) + m) := by
  have := trop_HW_le q r m (fun _ => 1) (fun _ => 1) (by
    intro a b
    have := wt_le_two q (Frame.hybRow r m a) (Frame.hybCol r m b)
    have : (HW q r m a b : ℚ) ≤ 2 := by unfold HW; exact_mod_cast this
    linarith)
  refine this.trans (le_of_eq ?_)
  unfold potVal
  simp
  ring

/-! ### D6: `q ≥ N` and `C` inside block 0 -/

/-- Potential of D6. -/
def pot6 (q r : ℕ) (A : ℕ) : ℚ := if r ≤ A ∧ 0 < blk q A then 1 else 0

theorem trop_D6 (q r m : ℕ) (hq : r + 2 * m ≤ q) (hC : ∀ c < r, blk q c = 0) :
    (tropVal (HW q r m) : ℚ) ≤ potVal (pot6 q r) (pot6 q r) r m := by
  apply trop_HW_le
  intro a b
  have hA := Frame_hybRow_lt r m a
  have hB := Frame_hybCol_lt r m b
  unfold HW
  set A := Frame.hybRow r m a
  set B := Frame.hybCol r m b
  have h0 : ∀ X, 0 ≤ pot6 q r X := fun X => by unfold pot6; split_ifs <;> norm_num
  by_cases hAB : A = B
  · rw [hAB, wt_diag]
    by_cases hBr : B < r
    · rw [hC B hBr]; simp; linarith [h0 B]
    · -- zone labels of a row and a column never coincide
      exfalso
      rcases a with c | i <;> rcases b with c' | j <;>
        simp [A, B, Frame.hybRow, Frame.hybCol] at hAB hBr <;> omega
  · by_cases hc : (q : ℤ) ∣ (A : ℤ) - B
    · have := cong_large' hAB hc
      have := max_lt hA hB
      omega
    · have h1 := wt_le_one_of_noncong hAB hc
      by_cases hbl : blk q A = blk q B
      · rw [wt_eq_zero_of_blk hAB hc hbl]; simp; linarith [h0 A, h0 B]
      · have hpos : (r ≤ A ∧ 0 < blk q A) ∨ (r ≤ B ∧ 0 < blk q B) := by
          by_contra hn
          push_neg at hn
          have hA0 : blk q A = 0 := by
            by_cases h : A < r
            · exact hC A h
            · have := hn.1 (by omega); omega
          have hB0 : blk q B = 0 := by
            by_cases h : B < r
            · exact hC B h
            · have := hn.2 (by omega); omega
          exact hbl (by rw [hA0, hB0])
        have : (wt q A B : ℚ) ≤ 1 := by exact_mod_cast h1
        rcases hpos with h | h
        · have : pot6 q r A = 1 := by unfold pot6; rw [if_pos h]
          linarith [h0 B]
        · have : pot6 q r B = 1 := by unfold pot6; rw [if_pos h]
          linarith [h0 A]

/-! ### D2: `2m < q ≤ r` -/

lemma blk_pos_of_ge {q L : ℕ} (hq : 1 ≤ q) (h : q ≤ L) : 0 < blk q L :=
  blk_pos_of (k := q) (Finset.mem_Icc.mpr ⟨hq, h⟩) (dvd_mul_right _ _)

/-- Potential of D2: `C`: `0` on the unpaired low set `U = {blk = 0, r ≤ c + q}`, else `1`;
zone: `1 + [x - q ∈ block 0]` (low nodes get 2). -/
def pot2 (q r : ℕ) (A : ℕ) : ℚ :=
  if A < r then (if blk q A = 0 ∧ r ≤ A + q then 0 else 1)
  else (1 + if blk q (A - q) = 0 then 1 else 0)

lemma pot2_nonneg (q r A : ℕ) : 0 ≤ pot2 q r A := by
  unfold pot2; split_ifs <;> norm_num

lemma pot2_zone_ge (q r X : ℕ) (hX : r ≤ X) : 1 ≤ pot2 q r X := by
  unfold pot2; rw [if_neg (by omega)]; split_ifs <;> norm_num

lemma pot2_zero_or (q r X : ℕ) : pot2 q r X = 0 ∨ 1 ≤ pot2 q r X := by
  unfold pot2; split_ifs <;> norm_num

lemma pot2_cong {q r m S L : ℕ} (hq1 : 1 ≤ q) (hm : 2 * m < q) (hqr : q ≤ r) (hSL : S < L)
    (hL : L < r + 2 * m) (hd : (q : ℤ) ∣ (L : ℤ) - S) : 2 ≤ pot2 q r S + pot2 q r L := by
  have hqLS : q ≤ L - S := by
    have := Int.le_of_dvd (by omega) hd; omega
  by_cases hLr : L < r
  · have h1 : pot2 q r L = 1 := by
      unfold pot2; rw [if_pos hLr]
      have := blk_pos_of_ge hq1 (show q ≤ L by omega)
      rw [if_neg (by omega)]
    have h2 : pot2 q r S = 1 := by
      unfold pot2; rw [if_pos (by omega)]
      rw [if_neg (by omega)]
    rw [h1, h2]; norm_num
  · have hSr : S < r := by omega
    by_cases hS : blk q S = 0 ∧ r ≤ S + q
    · have h2 : pot2 q r S = 0 := by unfold pot2; rw [if_pos hSr, if_pos hS]
      obtain ⟨t, ht⟩ := hd
      have ht1 : t = 1 := by
        have hq0 : (0 : ℤ) < q := by exact_mod_cast hq1
        have ht0 : 0 < t := by
          by_contra hh
          have : (t : ℤ) ≤ 0 := by omega
          nlinarith [ht, hq0, show (S : ℤ) < L by exact_mod_cast hSL]
        by_contra hne
        have : 2 ≤ t := by omega
        have : (q : ℤ) * 2 ≤ q * t := by nlinarith
        have := hS.2
        omega
      subst ht1
      have hLq : L - q = S := by omega
      have h1 : pot2 q r L = 2 := by
        unfold pot2; rw [if_neg hLr, hLq, if_pos hS.1]; norm_num
      rw [h1, h2]; norm_num
    · have h2 : pot2 q r S = 1 := by unfold pot2; rw [if_pos hSr, if_neg hS]
      have := pot2_zone_ge q r L (by omega)
      rw [h2]; linarith

lemma pot2_feasible {q r m A B : ℕ} (hq1 : 1 ≤ q) (hm : 2 * m < q) (hqr : q ≤ r)
    (hA : A < r + 2 * m) (hB : B < r + 2 * m):
    (wt q A B : ℚ) ≤ pot2 q r A + pot2 q r B := by
  have h0A := pot2_nonneg q r A
  have h0B := pot2_nonneg q r B
  by_cases hAB : A = B
  · subst hAB
    rw [wt_diag]
    by_cases hbl : 0 < blk q A
    · rw [if_pos hbl]
      by_cases hAr : A < r
      · have : pot2 q r A = 1 := by unfold pot2; rw [if_pos hAr, if_neg (by omega)]
        rw [this]; norm_num
      · have : 1 ≤ pot2 q r A := by unfold pot2; rw [if_neg hAr]; split_ifs <;> norm_num
        push_cast; linarith
    · rw [if_neg hbl]; push_cast; linarith
  · by_cases hc : (q : ℤ) ∣ (A : ℤ) - B
    · have h2 : (wt q A B : ℚ) ≤ 2 := by
        have := wt_le_two q A B; exact_mod_cast this
      rcases lt_or_gt_of_ne hAB with h | h
      · have hd : (q : ℤ) ∣ (B : ℤ) - A := by rw [← dvd_neg]; simpa using hc
        have := pot2_cong (r := r) (m := m) hq1 hm hqr h hB hd
        linarith
      · have := pot2_cong (r := r) (m := m) hq1 hm hqr h hA hc
        linarith
    · have h1 := wt_le_one_of_noncong hAB hc
      have h1' : (wt q A B : ℚ) ≤ 1 := by exact_mod_cast h1
      have p1 : ∀ X, X < r → pot2 q r X = 0 → blk q X = 0 := by
        intro X hX hp
        by_contra hb
        unfold pot2 at hp; rw [if_pos hX, if_neg (by omega)] at hp; norm_num at hp
      have p2 := pot2_zone_ge q r
      by_cases hz : pot2 q r A = 0 ∧ pot2 q r B = 0
      · have hAr : A < r := by
          by_contra hh; have := p2 A (by omega); linarith [hz.1]
        have hBr : B < r := by
          by_contra hh; have := p2 B (by omega); linarith [hz.2]
        have := wt_eq_zero_of_blk hAB hc (by rw [p1 A hAr hz.1, p1 B hBr hz.2])
        rw [this]; simp; linarith
      · have : 1 ≤ pot2 q r A + pot2 q r B := by
          rcases pot2_zero_or q r A with ha | ha <;> rcases pot2_zero_or q r B with hb | hb
          · exact absurd ⟨ha, hb⟩ hz
          · linarith
          · linarith
          · linarith
        linarith

theorem trop_D2 (q r m : ℕ) (hq1 : 1 ≤ q) (hm : 2 * m < q) (hqr : q ≤ r) :
    (tropVal (HW q r m) : ℚ) ≤ potVal (pot2 q r) (pot2 q r) r m := by
  apply trop_HW_le
  intro a b
  exact pot2_feasible hq1 hm hqr (Frame_hybRow_lt r m a) (Frame_hybCol_lt r m b)

end CatalanCore.Arith.Hybrid
