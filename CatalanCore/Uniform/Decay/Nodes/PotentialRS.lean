module
public import CatalanCore.Uniform.Decay.Nodes.PotentialPS
@[expose] public section

/-!
# Punctured node potentials (Part 1, Lemma `puncture`), without a truncated kernel

For an integer node `a` of a node set `A` and integer nodes `b ≠ a`,
`elog a b ≤ elog (a + i) b + 1/(2 (a-b)²)` and the diagonal terms agree, and
`∑_{b ∈ A, b ≠ a} 1/(a-b)² ≤ 4`.  Therefore the punctured counting potential at `a` is at most the
regularised potential at the free point `a + i` (distance `≥ 1` from the real axis, so the free
potential discrepancy applies uniformly in `a`) plus the constant `2`, and the regularised
potential is at most the exact interval potential at the real point `a`.
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

theorem sum_inv_sq_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ^ 2 ≤ 2 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    have : 1 / ((N : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

theorem sum_inv_sq_pos (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) :
    ∑ n ∈ S, 1 / (n : ℝ) ^ 2 ≤ 2 := by
  by_cases hne : S.Nonempty
  · set N := S.sup id with hNdef
    have hN : 1 ≤ N := by
      obtain ⟨x, hx⟩ := hne
      exact (hS x hx).trans (Finset.le_sup (f := id) hx)
    have hsub : S ⊆ Finset.Icc 1 N := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨hS n hn, Finset.le_sup (f := id) hn⟩
    calc ∑ n ∈ S, 1 / (n : ℝ) ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 - 1 / (N : ℝ) := sum_inv_sq_Icc N hN
      _ ≤ 2 := by have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
                  linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

theorem sum_inv_sq_nodes (A : Finset ℕ) (a : ℕ) :
    ∑ b ∈ A.erase a, 1 / ((a : ℝ) - b) ^ 2 ≤ 4 := by
  have hsplit : A.erase a = (A.filter (fun b => b < a)) ∪ (A.filter (fun b => a < b)) := by
    ext b
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hb, hbA⟩
      rcases lt_or_gt_of_ne hb with h | h
      · exact Or.inl ⟨hbA, h⟩
      · exact Or.inr ⟨hbA, h⟩
    · rintro (⟨hbA, h⟩ | ⟨hbA, h⟩)
      · exact ⟨h.ne, hbA⟩
      · exact ⟨h.ne', hbA⟩
  have hdisj : Disjoint (A.filter (fun b => b < a)) (A.filter (fun b => a < b)) := by
    rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hL : ∑ b ∈ A.filter (fun b => b < a), 1 / ((a : ℝ) - b) ^ 2 ≤ 2 := by
    have : ∑ b ∈ A.filter (fun b => b < a), 1 / ((a : ℝ) - b) ^ 2 =
        ∑ n ∈ (A.filter (fun b => b < a)).image (fun b => a - b), 1 / (n : ℝ) ^ 2 := by
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl (fun b hb => ?_)
        have hb' : b < a := (Finset.mem_filter.mp hb).2
        rw [Nat.cast_sub hb'.le]
      · intro x hx y hy hxy
        have hx' := (Finset.mem_filter.mp hx).2
        have hy' := (Finset.mem_filter.mp hy).2
        simp only at hxy
        omega
    rw [this]
    refine sum_inv_sq_pos _ (fun n hn => ?_)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    have := (Finset.mem_filter.mp hb).2
    omega
  have hU : ∑ b ∈ A.filter (fun b => a < b), 1 / ((a : ℝ) - b) ^ 2 ≤ 2 := by
    have : ∑ b ∈ A.filter (fun b => a < b), 1 / ((a : ℝ) - b) ^ 2 =
        ∑ n ∈ (A.filter (fun b => a < b)).image (fun b => b - a), 1 / (n : ℝ) ^ 2 := by
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl (fun b hb => ?_)
        have hb' : a < b := (Finset.mem_filter.mp hb).2
        rw [Nat.cast_sub hb'.le]
        ring_nf
      · intro x hx y hy hxy
        have hx' := (Finset.mem_filter.mp hx).2
        have hy' := (Finset.mem_filter.mp hy).2
        simp only at hxy
        omega
    rw [this]
    refine sum_inv_sq_pos _ (fun n hn => ?_)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    have := (Finset.mem_filter.mp hb).2
    omega
  linarith

/-- Pointwise regularisation of the node kernel at distinct integers. -/
theorem elog_le_regular (a b : ℕ) (hab : a ≠ b) :
    elog (a : ℂ) (b : ℂ) ≤ elog ((a : ℂ) + Complex.I) (b : ℂ) + 1 / (2 * ((a : ℝ) - b) ^ 2) := by
  have h1 : elog (a : ℂ) (b : ℂ) = kern (a : ℂ) (b : ℝ) := by
    rw [kern_eq_elog]; simp
  have h2 : elog ((a : ℂ) + Complex.I) (b : ℂ) = kern ((a : ℂ) + Complex.I) (b : ℝ) := by
    rw [kern_eq_elog]; simp
  rw [h1, h2]
  unfold kern
  simp only [Complex.natCast_re, Complex.add_re, Complex.I_re, add_zero, Complex.natCast_im,
    Complex.add_im, Complex.I_im, zero_add, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  have hq : 0 < ((a : ℝ) - b) ^ 2 := by
    have : (a : ℝ) - b ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
    positivity
  set q : ℝ := ((a : ℝ) - b) ^ 2 with hqdef
  have hlog : Real.log (q + 1) - Real.log q ≤ 1 / q := by
    rw [← Real.log_div (by linarith) hq.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < (q + 1) / q by positivity)
    have e : (q + 1) / q - 1 = 1 / q := by field_simp; ring
    linarith
  have : -(1 / 2) * Real.log q ≤ -(1 / 2) * Real.log (q + 1) + 1 / (2 * q) := by
    have e : 1 / (2 * q) = (1 / 2) * (1 / q) := by field_simp
    rw [e]
    nlinarith [hlog]
  exact this

theorem elog_reg_le (α x : ℝ) : elog ((α : ℂ) + Complex.I) (x : ℂ) ≤ elog (α : ℂ) (x : ℂ) := by
  have h1 : elog (α : ℂ) (x : ℂ) = kern (α : ℂ) x := by rw [kern_eq_elog]
  have h2 : elog ((α : ℂ) + Complex.I) (x : ℂ) = kern ((α : ℂ) + Complex.I) x := by
    rw [kern_eq_elog]
  rw [h1, h2]
  unfold kern
  simp only [Complex.ofReal_re, Complex.add_re, Complex.I_re, add_zero, Complex.ofReal_im,
    Complex.add_im, Complex.I_im, zero_add, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  by_cases hq : (α - x) ^ 2 = 0
  · rw [hq]; simp
  · have hpos : 0 < (α - x) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hq)
    have := Real.log_le_log hpos (show (α - x) ^ 2 ≤ (α - x) ^ 2 + 1 by linarith)
    linarith

theorem upieces_w_nonneg (B : BlockCollection) (r : ℕ) : ∀ P ∈ B.upieces r, 0 ≤ P.w := by
  intro P hP
  unfold BlockCollection.upieces at hP
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hP
  show (0 : ℝ) ≤ 1 / ((B.block i).d : ℝ)
  positivity

namespace BlockGeom

/-- Physical free-point discrepancy of the row list (any complex `z`). -/
theorem rows_phys (G : BlockGeom) {r : ℕ} (z : ℂ) {Bd δ M : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd)
    (hδ : 0 < δ) (hd : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), δ ≤ ‖z - (t : ℂ)‖)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), ‖z - (t : ℂ)‖ ≤ M) :
    |(∑ j ∈ (G.geometry r).rows, elog z (j : ℂ)) -
        ((G.rowU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum| ≤
      G.rowConstR * (|kern z (Bd * r)| + 2 * (Real.log M - Real.log δ)) := by
  have hb : 0 ≤ Bd * r := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; positivity
  have hps : ∀ P ∈ G.rowU r, 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ Bd * r := by
    intro P hP
    unfold rowU at hP
    rcases List.mem_append.mp hP with h | h
    · exact upieces_bound G.common r hBc P h
    · exact upieces_bound G.row r hBr P h
  have hA : ∀ j ∈ (G.geometry r).rows, (j : ℝ) ≤ Bd * r := by
    intro j hj
    rcases G.mem_rows_cases r j hj with h | h
    · exact node_lt_bound G.common r j hBc h
    · exact node_lt_bound G.row r j hBr h
  exact free_potential_discrepancy (G.geometry r).rows (G.rowU r) z hb hδ hd hM hps hA
    (fun t ht => G.rows_real_discrepancy r ht.1)

/-- **Punctured row potential at a node.**  For a node `a` of the row list, the (diagonal-free)
counting potential at the scaled node `a/r` is at most `r U_{μ_R}(a/r)` plus
`D · 3 log (Bd r + 1) + 2 + K log r`, uniformly in `a`, in `r`, and in the balancing trim. -/
theorem rows_rs_scaled (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) {a : ℕ} (ha : a ∈ (G.geometry r).rows) :
    (∑ b ∈ (G.geometry r).rows, elog ((a : ℂ) / r) ((b : ℂ) / r)) ≤
      r * ppotC G.rowPieces ((a : ℂ) / r) +
        G.rowConstR * (3 * Real.log (Bd * r + 1)) + 2 + G.rowConst * Real.log r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hA : ∀ j ∈ (G.geometry r).rows, (j : ℝ) ≤ Bd * r := by
    intro j hj
    rcases G.mem_rows_cases r j hj with h | h
    · exact node_lt_bound G.common r j hBc h
    · exact node_lt_bound G.row r j hBr h
  have haB := hA a ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  set z : ℂ := (a : ℂ) + Complex.I with hz
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), (1 : ℝ) ≤ ‖z - (t : ℂ)‖ := by
    intro t _
    have h1 : (z - (t : ℂ)).im = 1 := by simp [hz]
    have := Complex.abs_im_le_norm (z - (t : ℂ))
    rw [h1] at this
    simpa using this
  have hM : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), ‖z - (t : ℂ)‖ ≤ Bd * r + 1 := by
    intro t ht
    have : z - (t : ℂ) = (((a : ℝ) - t : ℝ) : ℂ) + Complex.I := by simp [hz]; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
    have : |(a : ℝ) - t| ≤ Bd * r := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    linarith
  have hfp := G.rows_phys z hBd0 hBc hBr one_pos hd hM
  -- kern bound
  have hb : 0 ≤ Bd * r := by positivity
  have hd' : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), (1 : ℝ) ≤ ‖z - (t : ℂ)‖ := hd
  have hkb : |kern z (Bd * r)| ≤ Real.log (Bd * r + 1) := by
    have hbm : Bd * r ∈ Set.Icc (0 : ℝ) (Bd * r) := ⟨hb, le_rfl⟩
    have k1 := kern_le hb one_pos hd' hbm
    have k2 := ge_kern hb one_pos hd' hM hbm
    rw [Real.log_one] at k1
    rw [abs_le]; constructor <;> linarith
  have hlogM : 0 ≤ Real.log (Bd * r + 1) := Real.log_nonneg (by linarith)
  have hfp' : |(∑ j ∈ (G.geometry r).rows, elog z (j : ℂ)) -
        ((G.rowU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum| ≤
      G.rowConstR * (3 * Real.log (Bd * r + 1)) := by
    refine hfp.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rw [Real.log_one]
    linarith
  -- regularisation: sum over the row list at the integer node a
  have hreg : ∑ b ∈ (G.geometry r).rows, elog (a : ℂ) (b : ℂ) ≤
      ∑ b ∈ (G.geometry r).rows, elog z (b : ℂ) + 2 := by
    have hterm : ∀ b ∈ (G.geometry r).rows, elog (a : ℂ) (b : ℂ) ≤
        elog z (b : ℂ) + (if b = a then 0 else 1 / (2 * ((a : ℝ) - b) ^ 2)) := by
      intro b hb'
      by_cases hba : b = a
      · subst hba
        simp [elog, hz]
      · rw [if_neg hba]
        exact elog_le_regular a b (Ne.symm hba)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add (le_refl _) ?_
    have hsplit : ∑ b ∈ (G.geometry r).rows, (if b = a then (0 : ℝ) else 1 / (2 * ((a : ℝ) - b) ^ 2)) =
        ∑ b ∈ (G.geometry r).rows.erase a, 1 / (2 * ((a : ℝ) - b) ^ 2) := by
      calc ∑ b ∈ (G.geometry r).rows, (if b = a then (0 : ℝ) else 1 / (2 * ((a : ℝ) - b) ^ 2))
          = ∑ b ∈ (G.geometry r).rows.erase a,
              (if b = a then (0 : ℝ) else 1 / (2 * ((a : ℝ) - b) ^ 2)) :=
            (Finset.sum_erase _ (by simp)).symm
        _ = _ := Finset.sum_congr rfl (fun b hb => if_neg (Finset.mem_erase.mp hb).1)
    rw [hsplit]
    have h4 := sum_inv_sq_nodes (G.geometry r).rows a
    have : ∑ b ∈ (G.geometry r).rows.erase a, 1 / (2 * ((a : ℝ) - b) ^ 2) =
        (1 / 2) * ∑ b ∈ (G.geometry r).rows.erase a, 1 / ((a : ℝ) - b) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      have hne : ((a : ℝ) - b) ^ 2 ≠ 0 := by
        have : (a : ℝ) - b ≠ 0 := sub_ne_zero.mpr (by
          have := (Finset.mem_erase.mp hb).1
          exact_mod_cast this.symm)
        positivity
      field_simp
    rw [this]
    linarith
  -- the regularised limit is at most the exact limit
  have hlimle : ((G.rowU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum ≤
      ((G.rowU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog (a : ℂ) (x : ℂ)).sum := by
    refine List.sum_le_sum (fun P hP => ?_)
    have hw : 0 ≤ P.w := by
      unfold rowU at hP
      rcases List.mem_append.mp hP with h | h
      · exact upieces_w_nonneg G.common r P h
      · exact upieces_w_nonneg G.row r P h
    have hlh : P.lo ≤ P.hi := by
      unfold rowU at hP
      rcases List.mem_append.mp hP with h | h
      · exact (upieces_bound G.common r hBc P h).2.1
      · exact (upieces_bound G.row r hBr P h).2.1
    refine mul_le_mul_of_nonneg_left ?_ hw
    refine intervalIntegral.integral_mono_on hlh (intervalIntegrable_elog z _ _)
      (intervalIntegrable_elog (a : ℂ) _ _) (fun x _ => ?_)
    exact elog_reg_le (a : ℝ) x
  -- scaling
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  have hconv : ∀ b ∈ (G.geometry r).rows,
      elog ((a : ℂ) / r) ((b : ℂ) / r) ≤ elog (a : ℂ) (b : ℂ) + Real.log r := by
    intro b _
    by_cases hba : b = a
    · subst hba
      simp [elog]; exact hlog
    · have hne : ‖(a : ℂ) - (b : ℂ)‖ ≠ 0 := by
        apply norm_ne_zero_iff.mpr
        exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hba)
      unfold elog
      have : (a : ℂ) / r - (b : ℂ) / r = ((a : ℂ) - (b : ℂ)) / r := by ring
      rw [this, norm_div, Complex.norm_natCast, Real.log_div hne hr'.ne']
      linarith
  have hsum : ∑ b ∈ (G.geometry r).rows, elog ((a : ℂ) / r) ((b : ℂ) / r) ≤
      ∑ b ∈ (G.geometry r).rows, elog (a : ℂ) (b : ℂ) +
        ((G.geometry r).rows.card : ℝ) * Real.log r := by
    refine (Finset.sum_le_sum hconv).trans ?_
    rw [Finset.sum_add_distrib]
    simp
  have hlim := phys_limit G.rowPieces hr (a : ℂ)
  rw [← G.rowU_eq r, G.pmass_rowPieces] at hlim
  have hcard := (abs_le.mp (G.card_rows_bound r)).2
  have hfp2 := (abs_le.mp hfp').2
  nlinarith [mul_le_mul_of_nonneg_right hcard hlog, hsum, hreg, hlimle, hlim, hfp2]

/-- Physical free-point discrepancy of the column list (any complex `z`). -/
theorem cols_phys (G : BlockGeom) {r : ℕ} (z : ℂ) {Bd δ M : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    (hδ : 0 < δ) (hd : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), δ ≤ ‖z - (t : ℂ)‖)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), ‖z - (t : ℂ)‖ ≤ M) :
    |(∑ j ∈ (G.geometry r).cols, elog z (j : ℂ)) -
        ((G.colU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum| ≤
      G.colConstR * (|kern z (Bd * r)| + 2 * (Real.log M - Real.log δ)) := by
  have hb : 0 ≤ Bd * r := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; positivity
  have hps : ∀ P ∈ G.colU r, 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ Bd * r := by
    intro P hP
    unfold colU at hP
    rcases List.mem_append.mp hP with h | h
    · exact upieces_bound G.common r hBc P h
    · exact upieces_bound G.column r hBq P h
  have hA : ∀ j ∈ (G.geometry r).cols, (j : ℝ) ≤ Bd * r := by
    intro j hj
    rcases G.mem_cols_cases r j hj with h | h
    · exact node_lt_bound G.common r j hBc h
    · exact node_lt_bound G.column r j hBq h
  exact free_potential_discrepancy (G.geometry r).cols (G.colU r) z hb hδ hd hM hps hA
    (fun t ht => G.cols_real_discrepancy r ht.1)

/-- **Punctured row potential at a node.**  For a node `a` of the column list, the (diagonal-free)
counting potential at the scaled node `a/r` is at most `r U_{μ_R}(a/r)` plus
`D · 3 log (Bd r + 1) + 2 + K log r`, uniformly in `a`, in `r`, and in the balancing trim. -/
theorem cols_rs_scaled (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd) {a : ℕ} (ha : a ∈ (G.geometry r).cols) :
    (∑ b ∈ (G.geometry r).cols, elog ((a : ℂ) / r) ((b : ℂ) / r)) ≤
      r * ppotC G.colPieces ((a : ℂ) / r) +
        G.colConstR * (3 * Real.log (Bd * r + 1)) + 2 + G.colConst * Real.log r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hA : ∀ j ∈ (G.geometry r).cols, (j : ℝ) ≤ Bd * r := by
    intro j hj
    rcases G.mem_cols_cases r j hj with h | h
    · exact node_lt_bound G.common r j hBc h
    · exact node_lt_bound G.column r j hBq h
  have haB := hA a ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  set z : ℂ := (a : ℂ) + Complex.I with hz
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), (1 : ℝ) ≤ ‖z - (t : ℂ)‖ := by
    intro t _
    have h1 : (z - (t : ℂ)).im = 1 := by simp [hz]
    have := Complex.abs_im_le_norm (z - (t : ℂ))
    rw [h1] at this
    simpa using this
  have hM : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), ‖z - (t : ℂ)‖ ≤ Bd * r + 1 := by
    intro t ht
    have : z - (t : ℂ) = (((a : ℝ) - t : ℝ) : ℂ) + Complex.I := by simp [hz]; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
    have : |(a : ℝ) - t| ≤ Bd * r := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    linarith
  have hfp := G.cols_phys z hBd0 hBc hBq one_pos hd hM
  -- kern bound
  have hb : 0 ≤ Bd * r := by positivity
  have hd' : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), (1 : ℝ) ≤ ‖z - (t : ℂ)‖ := hd
  have hkb : |kern z (Bd * r)| ≤ Real.log (Bd * r + 1) := by
    have hbm : Bd * r ∈ Set.Icc (0 : ℝ) (Bd * r) := ⟨hb, le_rfl⟩
    have k1 := kern_le hb one_pos hd' hbm
    have k2 := ge_kern hb one_pos hd' hM hbm
    rw [Real.log_one] at k1
    rw [abs_le]; constructor <;> linarith
  have hlogM : 0 ≤ Real.log (Bd * r + 1) := Real.log_nonneg (by linarith)
  have hfp' : |(∑ j ∈ (G.geometry r).cols, elog z (j : ℂ)) -
        ((G.colU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum| ≤
      G.colConstR * (3 * Real.log (Bd * r + 1)) := by
    refine hfp.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rw [Real.log_one]
    linarith
  -- regularisation: sum over the column list at the integer node a
  have hreg : ∑ b ∈ (G.geometry r).cols, elog (a : ℂ) (b : ℂ) ≤
      ∑ b ∈ (G.geometry r).cols, elog z (b : ℂ) + 2 := by
    have hterm : ∀ b ∈ (G.geometry r).cols, elog (a : ℂ) (b : ℂ) ≤
        elog z (b : ℂ) + (if b = a then 0 else 1 / (2 * ((a : ℝ) - b) ^ 2)) := by
      intro b hb'
      by_cases hba : b = a
      · subst hba
        simp [elog, hz]
      · rw [if_neg hba]
        exact elog_le_regular a b (Ne.symm hba)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add (le_refl _) ?_
    have hsplit : ∑ b ∈ (G.geometry r).cols, (if b = a then (0 : ℝ) else 1 / (2 * ((a : ℝ) - b) ^ 2)) =
        ∑ b ∈ (G.geometry r).cols.erase a, 1 / (2 * ((a : ℝ) - b) ^ 2) := by
      calc ∑ b ∈ (G.geometry r).cols, (if b = a then (0 : ℝ) else 1 / (2 * ((a : ℝ) - b) ^ 2))
          = ∑ b ∈ (G.geometry r).cols.erase a,
              (if b = a then (0 : ℝ) else 1 / (2 * ((a : ℝ) - b) ^ 2)) :=
            (Finset.sum_erase _ (by simp)).symm
        _ = _ := Finset.sum_congr rfl (fun b hb => if_neg (Finset.mem_erase.mp hb).1)
    rw [hsplit]
    have h4 := sum_inv_sq_nodes (G.geometry r).cols a
    have : ∑ b ∈ (G.geometry r).cols.erase a, 1 / (2 * ((a : ℝ) - b) ^ 2) =
        (1 / 2) * ∑ b ∈ (G.geometry r).cols.erase a, 1 / ((a : ℝ) - b) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      have hne : ((a : ℝ) - b) ^ 2 ≠ 0 := by
        have : (a : ℝ) - b ≠ 0 := sub_ne_zero.mpr (by
          have := (Finset.mem_erase.mp hb).1
          exact_mod_cast this.symm)
        positivity
      field_simp
    rw [this]
    linarith
  -- the regularised limit is at most the exact limit
  have hlimle : ((G.colU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum ≤
      ((G.colU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog (a : ℂ) (x : ℂ)).sum := by
    refine List.sum_le_sum (fun P hP => ?_)
    have hw : 0 ≤ P.w := by
      unfold colU at hP
      rcases List.mem_append.mp hP with h | h
      · exact upieces_w_nonneg G.common r P h
      · exact upieces_w_nonneg G.column r P h
    have hlh : P.lo ≤ P.hi := by
      unfold colU at hP
      rcases List.mem_append.mp hP with h | h
      · exact (upieces_bound G.common r hBc P h).2.1
      · exact (upieces_bound G.column r hBq P h).2.1
    refine mul_le_mul_of_nonneg_left ?_ hw
    refine intervalIntegral.integral_mono_on hlh (intervalIntegrable_elog z _ _)
      (intervalIntegrable_elog (a : ℂ) _ _) (fun x _ => ?_)
    exact elog_reg_le (a : ℝ) x
  -- scaling
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  have hconv : ∀ b ∈ (G.geometry r).cols,
      elog ((a : ℂ) / r) ((b : ℂ) / r) ≤ elog (a : ℂ) (b : ℂ) + Real.log r := by
    intro b _
    by_cases hba : b = a
    · subst hba
      simp [elog]; exact hlog
    · have hne : ‖(a : ℂ) - (b : ℂ)‖ ≠ 0 := by
        apply norm_ne_zero_iff.mpr
        exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hba)
      unfold elog
      have : (a : ℂ) / r - (b : ℂ) / r = ((a : ℂ) - (b : ℂ)) / r := by ring
      rw [this, norm_div, Complex.norm_natCast, Real.log_div hne hr'.ne']
      linarith
  have hsum : ∑ b ∈ (G.geometry r).cols, elog ((a : ℂ) / r) ((b : ℂ) / r) ≤
      ∑ b ∈ (G.geometry r).cols, elog (a : ℂ) (b : ℂ) +
        ((G.geometry r).cols.card : ℝ) * Real.log r := by
    refine (Finset.sum_le_sum hconv).trans ?_
    rw [Finset.sum_add_distrib]
    simp
  have hlim := phys_limit G.colPieces hr (a : ℂ)
  rw [← G.colU_eq r, G.pmass_colPieces] at hlim
  have hcard := (abs_le.mp (G.card_cols_bound r)).2
  have hfp2 := (abs_le.mp hfp').2
  nlinarith [mul_le_mul_of_nonneg_right hcard hlog, hsum, hreg, hlimle, hlim, hfp2]

end BlockGeom

end CatalanCore.Uniform
