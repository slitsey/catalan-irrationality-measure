module

public import CatalanCore.Li2.Content.Moments
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P042

@[expose] public section

/-! Difference-prime convexity, determinant bound and exact asymptotic rate, II1-II4. -/
open Polynomial Finset Filter
open scoped Topology BigOperators
open CatalanCore.Li2.Port
open CatalanCore.Li2.Port.Unified

namespace CatalanCore.Li2.Content
open Port.Unified.Proofs.Arithmetic

private theorem sum_odd_rat (k : ℕ) :
    (∑ i ∈ Finset.range k, (2 * (i : ℚ) + 1)) = (k : ℚ) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private theorem sum_even_rat (k : ℕ) :
    (∑ i ∈ Finset.range k, 2 * (i : ℚ)) = (k : ℚ) * ((k : ℚ) - 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem phi_jensen (n a b : ℕ) :
    phi n (a + b) ≤ (phi n (2 * a) + phi n (2 * b)) / 2 := by
  dsimp [phi]
  push_cast
  apply max_le
  · have ha := le_max_left ((2 : ℚ) * a - n + 1) 0
    have hb := le_max_left ((2 : ℚ) * b - n + 1) 0
    linarith
  · have ha := le_max_right ((2 : ℚ) * a - n + 1) 0
    have hb := le_max_right ((2 : ℚ) * b - n + 1) 0
    linarith

theorem S_bound (n : ℕ) : S n ≤ 9 * (n : ℚ) ^ 2 / 4 := by
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
  rcases hm with rfl | rfl
  · have hzero : ∑ i ∈ Finset.range m, phi (2 * m) (2 * i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiq : (i : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      dsimp [phi]
      push_cast
      exact max_eq_right (by linarith)
    have hterm (i : ℕ) : phi (2 * m) (2 * (m + i)) = 2 * (i : ℚ) + 1 := by
      dsimp [phi]
      push_cast
      rw [max_eq_left (by nlinarith [Nat.cast_nonneg (α := ℚ) i])]
      ring
    unfold S
    rw [show 2 * (2 * m) = m + 3 * m by omega, Finset.sum_range_add, hzero]
    simp_rw [hterm]
    rw [sum_odd_rat]
    push_cast
    nlinarith
  · have hzero : ∑ i ∈ Finset.range m, phi (2 * m + 1) (2 * i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiq : (i : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      dsimp [phi]
      push_cast
      exact max_eq_right (by linarith)
    have hterm (i : ℕ) : phi (2 * m + 1) (2 * (m + i)) = 2 * (i : ℚ) := by
      dsimp [phi]
      push_cast
      rw [max_eq_left (by nlinarith [Nat.cast_nonneg (α := ℚ) i])]
      ring
    unfold S
    rw [show 2 * (2 * m + 1) = m + (3 * m + 2) by omega,
      Finset.sum_range_add, hzero]
    simp_rw [hterm]
    rw [sum_even_rat]
    push_cast
    nlinarith

private theorem S_gap (n : ℕ) :
    0 ≤ 9 * (n : ℚ) ^ 2 / 4 - S n ∧
      9 * (n : ℚ) ^ 2 / 4 - S n ≤ 1 / 4 := by
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
  rcases hm with rfl | rfl
  · have hzero : ∑ i ∈ Finset.range m, phi (2 * m) (2 * i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiq : (i : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      dsimp [phi]
      push_cast
      exact max_eq_right (by linarith)
    have hterm (i : ℕ) : phi (2 * m) (2 * (m + i)) = 2 * (i : ℚ) + 1 := by
      dsimp [phi]
      push_cast
      rw [max_eq_left (by nlinarith [Nat.cast_nonneg (α := ℚ) i])]
      ring
    unfold S
    rw [show 2 * (2 * m) = m + 3 * m by omega, Finset.sum_range_add, hzero]
    simp_rw [hterm]
    rw [sum_odd_rat]
    push_cast
    constructor <;> nlinarith
  · have hzero : ∑ i ∈ Finset.range m, phi (2 * m + 1) (2 * i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiq : (i : ℚ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      dsimp [phi]
      push_cast
      exact max_eq_right (by linarith)
    have hterm (i : ℕ) : phi (2 * m + 1) (2 * (m + i)) = 2 * (i : ℚ) := by
      dsimp [phi]
      push_cast
      rw [max_eq_left (by nlinarith [Nat.cast_nonneg (α := ℚ) i])]
      ring
    unfold S
    rw [show 2 * (2 * m + 1) = m + (3 * m + 2) by omega,
      Finset.sum_range_add, hzero]
    simp_rw [hterm]
    rw [sum_even_rat]
    push_cast
    constructor <;> nlinarith

theorem difference_rate (f : ℝ) :
    Tendsto (fun n : ℕ => -f * (S n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (-(9 / 4) * f)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => (1 / 4 : ℝ) * (n : ℝ)⁻¹ ^ 2)
      atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul (hi.pow 2) using 1 <;> norm_num
  have hbounds : ∀ᶠ n : ℕ in atTop,
      0 ≤ 9 / 4 - (S n : ℝ) / (n : ℝ) ^ 2 ∧
      9 / 4 - (S n : ℝ) / (n : ℝ) ^ 2 ≤ (1 / 4 : ℝ) * (n : ℝ)⁻¹ ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hd : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hne
    have hs : 0 ≤ 9 * (n : ℝ) ^ 2 / 4 - (S n : ℝ) ∧
        9 * (n : ℝ) ^ 2 / 4 - (S n : ℝ) ≤ 1 / 4 := by
      have h0 := (Rat.cast_nonneg (K := ℝ)).mpr (S_gap n).1
      have h1 := (Rat.cast_le (K := ℝ)).mpr (S_gap n).2
      push_cast at h0 h1
      exact ⟨h0, h1⟩
    have heq : 9 / 4 - (S n : ℝ) / (n : ℝ) ^ 2 =
        (9 * (n : ℝ) ^ 2 / 4 - (S n : ℝ)) / (n : ℝ) ^ 2 := by
      field_simp
      <;> ring
    rw [heq]
    refine ⟨div_nonneg hs.1 (le_of_lt hd), ?_⟩
    simpa only [div_eq_mul_inv, inv_pow] using
      div_le_div_of_nonneg_right hs.2 (le_of_lt hd)
  have he := squeeze_zero' (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2) hb
  have hs : Tendsto (fun n : ℕ => (S n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (9 / 4)) := by
    convert ((tendsto_const_nhds (x := (9 / 4 : ℝ))).sub he) using 1 <;> first | (funext n; ring) | ring
  convert (tendsto_const_nhds.mul hs : Tendsto
    (fun n : ℕ => -f * ((S n : ℝ) / (n : ℝ) ^ 2)) atTop (𝓝 (-f * (9 / 4)))) using 1 <;> ring

private lemma diffEntryDraft (p : ℕ) [Fact p.Prime] (z f : ℚ)
    (hf : 0 ≤ f) (h1 : z ≠ 1) (hr : Port.Li2.VG p (z / (1 - z)) (-f))
    (hz : Port.Li2.VG p z 0) (hi : Port.Li2.VG p z⁻¹ 0)
    {n : ℕ} (hn : 1 ≤ n) {a b : ℕ} (ha : a < 2*n) (hb : b < 2*n) :
    Port.Li2.GV p (ParameterFamily.numeratorFunctional z (4*n) (Port.Li2.gramNum n a b))
      (-2 * L p n - f * phi n (a+b)) := by
  have hL0 : 0 ≤ L p n := Nat.cast_nonneg _
  have hp0 : 0 ≤ phi n (a+b) := by dsimp [phi]; exact le_max_right _ _
  unfold ParameterFamily.numeratorFunctional
  apply Apery.GV.add
  · exact Apery.GV.C (gramU_entry_VG_f p z f h1 hf hr hn ha hb)
  · apply Apery.GV.sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hres := Port.Li2.gramRes_VG p n a b hj1 hj2
    have hc : Port.Li2.VG p ((j : ℚ) * z⁻¹ ^ j) 0 := by
      simpa using (Apery.VG.natCast (p := p) j).mul (hi.pow j)
    have ht : Port.Li2.VG p (Port.Li2.parameterTau z j) (-2 * L p n) :=
      parameterTau_VG_log p z hz (by omega : j ≤ 7*n-2)
    have hlin : Port.Li2.GV p (X - C (Port.Li2.parameterTau z j)) (-2 * L p n) :=
      (Apery.GV.X.mono (by linarith)).sub (Apery.GV.C ht)
    refine ((Apery.GV.C hres).mul ((Apery.GV.C hc).mul hlin)).mono ?_
    nlinarith

theorem Qtilde_GV_f (p : ℕ) [Fact p.Prime] (z f : ℚ)
    (hf : 0 ≤ f) (h1 : z ≠ 1) (hr : Port.Li2.VG p (z / (1 - z)) (-f))
    (hz : Port.Li2.VG p z 0) (hi : Port.Li2.VG p z⁻¹ 0) {n : ℕ} (hn : 1 ≤ n) :
    Port.Li2.GV p (ParameterFamily.Qtilde z n) (-f * S n - 4 * n * L p n) := by
  let w : Fin (2*n) → ℚ := fun i => -f / 2 * phi n (2*i.val) - L p n
  have hentry : ∀ i j : Fin (2*n),
      Port.Li2.GV p (ParameterFamily.binomGram z n i j) (w i + w j) := by
    intro i j
    have h := diffEntryDraft p z f hf h1 hr hz hi hn i.isLt j.isLt
    refine h.mono ?_
    have hJ := mul_le_mul_of_nonneg_left (phi_jensen n i.val j.val) hf
    dsimp [w]
    nlinarith
  have hsum : (∑ i : Fin (2*n), w i) = -f / 2 * S n - 2 * n * L p n := by
    dsimp [w]
    rw [Fin.sum_univ_eq_sum_range (fun i => -f / 2 * phi n (2*i) - L p n)]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    dsimp [S]
    push_cast
    ring
  have hdet := Apery.det_GV (p := p) (ParameterFamily.binomGram z n) w w hentry
  rw [ParameterFamily.Qtilde_eq_binomGram_det]
  convert hdet using 1
  rw [hsum]
  ring

end CatalanCore.Li2.Content

#print axioms CatalanCore.Li2.Content.phi_jensen
#print axioms CatalanCore.Li2.Content.S_bound
#print axioms CatalanCore.Li2.Content.difference_rate
#print axioms CatalanCore.Li2.Content.Qtilde_GV_f
