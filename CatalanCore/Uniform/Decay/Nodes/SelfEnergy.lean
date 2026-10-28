module
public import CatalanCore.Uniform.Decay.Nodes.RegularVar
public import CatalanCore.Uniform.Decay.Nodes.PotentialRS
@[expose] public section

/-!
# Self-energy of the node lists (Part 1, Lemma `self-energy`): the lower bound

For the row list `R_r` (and the column list), in physical coordinates,

`mutE (rowU r) (rowU r) - E_AS ≤ ∑_{a ∈ R_r} ∑_{b ∈ R_r} elog a b`,

`E_AS = N · 3 D log (Bd r + 1) + 6 (r M) W + 5 D (1/2) log (1 + (Bd r)²) (r M)` (explicit),
where `D = rowConstR`, `N = #R_r`, `W = ∑ w`.  Proof: regularise at `a + i` (pointwise lower
bound, equality on the diagonal), apply the free-point discrepancy at each `a`, then the Abel
discrepancy once more in `a` for the smooth regularised potential `kapInt`, and finally compare
`kapInt` with the exact interval potential (`kapInt_ge`).
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay MeasureTheory Set intervalIntegral

namespace Decay.Nodes

/-- **Generic node-sum discrepancy** for a `C¹` kernel with an explicit variation bound. -/
theorem node_sum_discrepancy (A : Finset ℕ) (ps : List Piece) {g g' : ℝ → ℝ} {b D V : ℝ}
    (hb : 0 ≤ b) (hg : ∀ t ∈ Icc (0 : ℝ) b, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Icc 0 b))
    (hps : ∀ P ∈ ps, 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ b)
    (hA : ∀ j ∈ A, (j : ℝ) ≤ b)
    (hD : ∀ t ∈ Icc (0 : ℝ) b,
      |((A.filter (fun j : ℕ => j ≤ ⌊t⌋₊)).card : ℝ) - lamSum ps t| ≤ D)
    (hV : ∫ t in Ioc 0 b, |g' t| ≤ V) :
    |(∑ j ∈ A, g j) - (ps.map fun P => P.w * ∫ x in P.lo..P.hi, g x).sum| ≤
      D * (|g b| + V) := by
  have habel := abel_discrepancy (indic A) (g := g) (g' := g') (Λ := lamSum ps)
    (b := b) (D := D) hb hg hg' (continuous_lamSum ps)
    (fun t ht => by rw [sum_indic_Icc]; exact hD t ht)
  have hsum : ∑ k ∈ Icc 0 ⌊b⌋₊, g k * indic A k = ∑ j ∈ A, g j := by
    rw [sum_mul_indic]
    have : A.filter (fun j : ℕ => j ≤ ⌊b⌋₊) = A := by
      apply Finset.filter_true_of_mem
      intro j hj
      exact Nat.le_floor (hA j hj)
    rw [this]
  have hlam : lamSum ps b = (ps.map fun P => P.w * (P.hi - P.lo)).sum := by
    unfold lamSum
    congr 1
    refine List.map_congr_left (fun P hP => ?_)
    have h := hps P hP
    unfold pieceLam
    rw [min_eq_right h.2.2, max_eq_right (by linarith [h.2.1])]
  have hibp := ibp_list ps hps hg hg'
  rw [hibp]
  rw [hsum, hlam] at habel
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0 ⟨le_rfl, hb⟩)
  refine habel.trans ?_
  have : |g b| + ∫ t in Ioc 0 b, |g' t| ≤ |g b| + V := by linarith
  exact mul_le_mul_of_nonneg_left this hD0

/-- The exact interval potential integrates to the interval energy. -/
theorem integral_Ucl (a b c d : ℝ) :
    ∫ x in a..b, -(Lam (x - c) - Lam (x - d)) = pairEnergy a b c d := by
  rw [← pairEnergy_eq_integral]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  exact (integral_neg_log_abs x c d).symm

/-- Lower bound for the integral of the regularised potential against a piece. -/
theorem piece_integral_kap_ge {P : Piece} {lo' hi' : ℝ} (hw : 0 ≤ P.w) (hlh : P.lo ≤ P.hi) :
    P.w * (pairEnergy P.lo P.hi lo' hi' - 6 * (P.hi - P.lo)) ≤
      P.w * ∫ x in P.lo..P.hi, kapInt lo' hi' x := by
  refine mul_le_mul_of_nonneg_left ?_ hw
  have hc1 : Continuous fun x : ℝ => -(Lam (x - lo') - Lam (x - hi')) - 6 :=
    (((continuous_Lam.comp (continuous_id.sub continuous_const)).sub
      (continuous_Lam.comp (continuous_id.sub continuous_const))).neg).sub continuous_const
  have i1 : IntervalIntegrable (fun x : ℝ => -(Lam (x - lo') - Lam (x - hi')) - 6)
      MeasureTheory.volume P.lo P.hi := hc1.intervalIntegrable _ _
  have i2 : IntervalIntegrable (kapInt lo' hi') MeasureTheory.volume P.lo P.hi :=
    (continuous_kapInt lo' hi').intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hlh i1 i2 (fun x _ => kapInt_ge lo' hi' x)
  have e : ∫ x in P.lo..P.hi, (-(Lam (x - lo') - Lam (x - hi')) - 6) =
      pairEnergy P.lo P.hi lo' hi' - 6 * (P.hi - P.lo) := by
    rw [intervalIntegral.integral_sub, integral_Ucl]
    · simp; ring
    · exact (((continuous_Lam.comp (continuous_id.sub continuous_const)).sub
        (continuous_Lam.comp (continuous_id.sub continuous_const))).neg).intervalIntegrable _ _
    · exact intervalIntegrable_const
  linarith

/-- The sum over nodes of the regularised potential of one piece, from below. -/
theorem outer_kap_ge (A : Finset ℕ) (ps : List Piece) {b D : ℝ} (P' : Piece)
    (hb : 0 ≤ b)
    (hps : ∀ P ∈ ps, 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ b)
    (hP' : 0 ≤ P'.lo ∧ P'.lo ≤ P'.hi ∧ P'.hi ≤ b)
    (hwps : ∀ P ∈ ps, 0 ≤ P.w)
    (hA : ∀ j ∈ A, (j : ℝ) ≤ b)
    (hD : ∀ t ∈ Icc (0 : ℝ) b,
      |((A.filter (fun j : ℕ => j ≤ ⌊t⌋₊)).card : ℝ) - lamSum ps t| ≤ D) :
    (ps.map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi - 6 * (P.hi - P.lo))).sum -
        D * (|kapInt P'.lo P'.hi b| + 4 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + b ^ 2)))) ≤
      ∑ a ∈ A, kapInt P'.lo P'.hi a := by
  have hd := node_sum_discrepancy A ps (g := kapInt P'.lo P'.hi) (g' := kapD P'.lo P'.hi)
    (b := b) (D := D) (V := 4 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + b ^ 2)))) hb
    (fun t _ => hasDerivAt_kapInt _ _ t) (continuous_kapD _ _).continuousOn hps hA hD
    (integral_abs_kapD_le hP'.1 hP'.2.1 hP'.2.2)
  have hlow : (ps.map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi - 6 * (P.hi - P.lo))).sum ≤
      (ps.map fun P => P.w * ∫ x in P.lo..P.hi, kapInt P'.lo P'.hi x).sum :=
    List.sum_le_sum (fun P hP => piece_integral_kap_ge (hwps P hP) (hps P hP).2.1)
  have := (abs_le.mp hd).1
  linarith

theorem elog_regI_nat (a : ℕ) (y : ℝ) :
    elog ((a : ℂ) + Complex.I) (y : ℂ) = kap (a : ℝ) y := by
  have := elog_regI (a : ℝ) y
  simpa using this

theorem lsum_sub (L : List Piece) (f g : Piece → ℝ) :
    (L.map fun x => f x - g x).sum = (L.map f).sum - (L.map g).sum := by
  induction L with
  | nil => simp
  | cons Q L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]; ring

theorem sum_swap_list (A : Finset ℕ) (L : List Piece) (F : Piece → ℕ → ℝ) :
    ∑ a ∈ A, (L.map fun P' => F P' a).sum = (L.map fun P' => ∑ a ∈ A, F P' a).sum := by
  induction L with
  | nil => simp
  | cons Q L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

end Decay.Nodes

namespace BlockGeom

/-- Regularised potential at a node, from below. -/
theorem rows_reg_ge (G : BlockGeom) {r : ℕ} {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) {a : ℕ} (ha : a ∈ (G.geometry r).rows) :
    ((G.rowU r).map fun P' => P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum -
        G.rowConstR * (3 * Real.log (Bd * r + 1)) ≤
      ∑ b ∈ (G.geometry r).rows, elog ((a : ℂ) + Complex.I) (b : ℂ) := by
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
  have hb : 0 ≤ Bd * r := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; positivity
  have hkb : |kern z (Bd * r)| ≤ Real.log (Bd * r + 1) := by
    have hbm : Bd * r ∈ Set.Icc (0 : ℝ) (Bd * r) := ⟨hb, le_rfl⟩
    have k1 := kern_le hb one_pos hd hbm
    have k2 := ge_kern hb one_pos hd hM hbm
    rw [Real.log_one] at k1
    rw [abs_le]; constructor <;> linarith
  have hlogM : 0 ≤ Real.log (Bd * r + 1) := Real.log_nonneg (by linarith)
  have hfp' : |(∑ j ∈ (G.geometry r).rows, elog z (j : ℂ)) -
        ((G.rowU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum| ≤
      G.rowConstR * (3 * Real.log (Bd * r + 1)) := by
    refine hfp.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rw [Real.log_one]
    linarith
  have hL : ((G.rowU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum =
      ((G.rowU r).map fun P' => P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum := by
    refine congrArg List.sum (List.map_congr_left (fun P _ => ?_))
    congr 1
    rw [← integral_kap]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    exact elog_regI_nat a x
  rw [hL] at hfp'
  have := (abs_le.mp hfp').1
  linarith

/-- **Self-energy lower bound, rows, physical coordinates.** -/
theorem rows_as_phys (G : BlockGeom) {r : ℕ} {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) :
    mutE (G.rowU r) (G.rowU r)
      - ((G.geometry r).rows.card : ℝ) * (G.rowConstR * (3 * Real.log (Bd * r + 1)))
      - ((G.rowU r).map fun P' => P'.w * (6 * pmass (G.rowU r) +
          G.rowConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum
    ≤ ∑ a ∈ (G.geometry r).rows, ∑ b ∈ (G.geometry r).rows, elog (a : ℂ) (b : ℂ) := by
  have hb : 0 ≤ Bd * r := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; positivity
  have hps : ∀ P ∈ G.rowU r, 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ Bd * r := by
    intro P hP
    unfold rowU at hP
    rcases List.mem_append.mp hP with h | h
    · exact upieces_bound G.common r hBc P h
    · exact upieces_bound G.row r hBr P h
  have hwps : ∀ P ∈ G.rowU r, 0 ≤ P.w := by
    intro P hP
    unfold rowU at hP
    rcases List.mem_append.mp hP with h | h
    · exact upieces_w_nonneg G.common r P h
    · exact upieces_w_nonneg G.row r P h
  have hA : ∀ j ∈ (G.geometry r).rows, (j : ℝ) ≤ Bd * r := by
    intro j hj
    rcases G.mem_rows_cases r j hj with h | h
    · exact node_lt_bound G.common r j hBc h
    · exact node_lt_bound G.row r j hBr h
  have hD : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r),
      |(((G.geometry r).rows.filter (fun j : ℕ => j ≤ ⌊t⌋₊)).card : ℝ) - lamSum (G.rowU r) t| ≤
        G.rowConstR := fun t ht => G.rows_real_discrepancy r ht.1
  -- Step 1+2: pointwise regularisation and the free-point discrepancy
  have hstep : ∀ a ∈ (G.geometry r).rows,
      ((G.rowU r).map fun P' => P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum -
        G.rowConstR * (3 * Real.log (Bd * r + 1)) ≤
      ∑ b ∈ (G.geometry r).rows, elog (a : ℂ) (b : ℂ) := by
    intro a ha
    refine (G.rows_reg_ge hBd0 hBc hBr ha).trans (Finset.sum_le_sum (fun b _ => ?_))
    have := elog_reg_le (a : ℝ) (b : ℝ)
    simpa using this
  have hsum1 : ∑ a ∈ (G.geometry r).rows,
      (((G.rowU r).map fun P' => P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum -
        G.rowConstR * (3 * Real.log (Bd * r + 1))) ≤
      ∑ a ∈ (G.geometry r).rows, ∑ b ∈ (G.geometry r).rows, elog (a : ℂ) (b : ℂ) :=
    Finset.sum_le_sum hstep
  rw [Finset.sum_sub_distrib] at hsum1
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum1
  have hswap := sum_swap_list (G.geometry r).rows (G.rowU r)
    (fun P' a => P'.w * kapInt P'.lo P'.hi (a : ℝ))
  -- Step 3: per piece lower bound
  have hpiece : ∀ P' ∈ G.rowU r,
      P'.w * ((G.rowU r).map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi)).sum -
        P'.w * (6 * pmass (G.rowU r) +
          G.rowConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2))))) ≤
      ∑ a ∈ (G.geometry r).rows, P'.w * kapInt P'.lo P'.hi (a : ℝ) := by
    intro P' hP'
    have hP'b := hps P' hP'
    have hw' := hwps P' hP'
    have h := outer_kap_ge (G.geometry r).rows (G.rowU r) P' hb hps hP'b hwps hA hD
    have hbk := abs_kapInt_le hP'b.1 hP'b.2.1 hP'b.2.2 (⟨hb, le_rfl⟩ : Bd * r ∈ Set.Icc 0 (Bd * r))
    have hsplit : ((G.rowU r).map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi -
          6 * (P.hi - P.lo))).sum =
        ((G.rowU r).map fun P => P.w * pairEnergy P.lo P.hi P'.lo P'.hi).sum -
          6 * pmass (G.rowU r) := by
      unfold pmass
      have e : (G.rowU r).map (fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi -
            6 * (P.hi - P.lo))) =
          (G.rowU r).map (fun P => P.w * pairEnergy P.lo P.hi P'.lo P'.hi - 6 * Piece.mass P) :=
        List.map_congr_left (fun P _ => by unfold Piece.mass; ring)
      rw [e, lsum_sub, List.sum_map_mul_left]
    rw [hsplit] at h
    rw [← Finset.mul_sum]
    have hD0 : (0 : ℝ) ≤ (G.rowConstR : ℝ) := Nat.cast_nonneg _
    have h2 : G.rowConstR * (|kapInt P'.lo P'.hi (Bd * r)| +
        4 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))) ≤
        G.rowConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hD0
    have h3 : ((G.rowU r).map fun P => P.w * pairEnergy P.lo P.hi P'.lo P'.hi).sum -
        6 * pmass (G.rowU r) - G.rowConstR * (5 * ((P'.hi - P'.lo) *
          ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))) ≤
        ∑ a ∈ (G.geometry r).rows, kapInt P'.lo P'.hi (a : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left h3 hw'
    nlinarith [this]
  have hsum2 : ((G.rowU r).map fun P' =>
        P'.w * ((G.rowU r).map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi)).sum -
        P'.w * (6 * pmass (G.rowU r) +
          G.rowConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum ≤
      ((G.rowU r).map fun P' => ∑ a ∈ (G.geometry r).rows,
        P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum :=
    List.sum_le_sum hpiece
  rw [lsum_sub] at hsum2
  -- identify the energy
  have hE : ((G.rowU r).map fun P' =>
      P'.w * ((G.rowU r).map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi)).sum).sum =
      mutE (G.rowU r) (G.rowU r) := by
    unfold mutE
    refine congrArg List.sum (List.map_congr_left (fun Q _ => ?_))
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left (fun P _ => ?_))
    unfold pairInteraction
    rw [pairEnergy_comm P.lo P.hi Q.lo Q.hi]
    ring
  rw [hE] at hsum2
  rw [hswap] at hsum1
  linarith

/-- Regularised potential at a node, from below (columns). -/
theorem cols_reg_ge (G : BlockGeom) {r : ℕ} {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd) {a : ℕ} (ha : a ∈ (G.geometry r).cols) :
    ((G.colU r).map fun P' => P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum -
        G.colConstR * (3 * Real.log (Bd * r + 1)) ≤
      ∑ b ∈ (G.geometry r).cols, elog ((a : ℂ) + Complex.I) (b : ℂ) := by
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
  have hb : 0 ≤ Bd * r := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; positivity
  have hkb : |kern z (Bd * r)| ≤ Real.log (Bd * r + 1) := by
    have hbm : Bd * r ∈ Set.Icc (0 : ℝ) (Bd * r) := ⟨hb, le_rfl⟩
    have k1 := kern_le hb one_pos hd hbm
    have k2 := ge_kern hb one_pos hd hM hbm
    rw [Real.log_one] at k1
    rw [abs_le]; constructor <;> linarith
  have hlogM : 0 ≤ Real.log (Bd * r + 1) := Real.log_nonneg (by linarith)
  have hfp' : |(∑ j ∈ (G.geometry r).cols, elog z (j : ℂ)) -
        ((G.colU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum| ≤
      G.colConstR * (3 * Real.log (Bd * r + 1)) := by
    refine hfp.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rw [Real.log_one]
    linarith
  have hL : ((G.colU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum =
      ((G.colU r).map fun P' => P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum := by
    refine congrArg List.sum (List.map_congr_left (fun P _ => ?_))
    congr 1
    rw [← integral_kap]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    exact elog_regI_nat a x
  rw [hL] at hfp'
  have := (abs_le.mp hfp').1
  linarith

/-- **Self-energy lower bound, columns, physical coordinates.** -/
theorem cols_as_phys (G : BlockGeom) {r : ℕ} {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd) :
    mutE (G.colU r) (G.colU r)
      - ((G.geometry r).cols.card : ℝ) * (G.colConstR * (3 * Real.log (Bd * r + 1)))
      - ((G.colU r).map fun P' => P'.w * (6 * pmass (G.colU r) +
          G.colConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum
    ≤ ∑ a ∈ (G.geometry r).cols, ∑ b ∈ (G.geometry r).cols, elog (a : ℂ) (b : ℂ) := by
  have hb : 0 ≤ Bd * r := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; positivity
  have hps : ∀ P ∈ G.colU r, 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ Bd * r := by
    intro P hP
    unfold colU at hP
    rcases List.mem_append.mp hP with h | h
    · exact upieces_bound G.common r hBc P h
    · exact upieces_bound G.column r hBq P h
  have hwps : ∀ P ∈ G.colU r, 0 ≤ P.w := by
    intro P hP
    unfold colU at hP
    rcases List.mem_append.mp hP with h | h
    · exact upieces_w_nonneg G.common r P h
    · exact upieces_w_nonneg G.column r P h
  have hA : ∀ j ∈ (G.geometry r).cols, (j : ℝ) ≤ Bd * r := by
    intro j hj
    rcases G.mem_cols_cases r j hj with h | h
    · exact node_lt_bound G.common r j hBc h
    · exact node_lt_bound G.column r j hBq h
  have hD : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r),
      |(((G.geometry r).cols.filter (fun j : ℕ => j ≤ ⌊t⌋₊)).card : ℝ) - lamSum (G.colU r) t| ≤
        G.colConstR := fun t ht => G.cols_real_discrepancy r ht.1
  -- Step 1+2: pointwise regularisation and the free-point discrepancy
  have hstep : ∀ a ∈ (G.geometry r).cols,
      ((G.colU r).map fun P' => P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum -
        G.colConstR * (3 * Real.log (Bd * r + 1)) ≤
      ∑ b ∈ (G.geometry r).cols, elog (a : ℂ) (b : ℂ) := by
    intro a ha
    refine (G.cols_reg_ge hBd0 hBc hBq ha).trans (Finset.sum_le_sum (fun b _ => ?_))
    have := elog_reg_le (a : ℝ) (b : ℝ)
    simpa using this
  have hsum1 : ∑ a ∈ (G.geometry r).cols,
      (((G.colU r).map fun P' => P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum -
        G.colConstR * (3 * Real.log (Bd * r + 1))) ≤
      ∑ a ∈ (G.geometry r).cols, ∑ b ∈ (G.geometry r).cols, elog (a : ℂ) (b : ℂ) :=
    Finset.sum_le_sum hstep
  rw [Finset.sum_sub_distrib] at hsum1
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum1
  have hswap := sum_swap_list (G.geometry r).cols (G.colU r)
    (fun P' a => P'.w * kapInt P'.lo P'.hi (a : ℝ))
  -- Step 3: per piece lower bound
  have hpiece : ∀ P' ∈ G.colU r,
      P'.w * ((G.colU r).map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi)).sum -
        P'.w * (6 * pmass (G.colU r) +
          G.colConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2))))) ≤
      ∑ a ∈ (G.geometry r).cols, P'.w * kapInt P'.lo P'.hi (a : ℝ) := by
    intro P' hP'
    have hP'b := hps P' hP'
    have hw' := hwps P' hP'
    have h := outer_kap_ge (G.geometry r).cols (G.colU r) P' hb hps hP'b hwps hA hD
    have hbk := abs_kapInt_le hP'b.1 hP'b.2.1 hP'b.2.2 (⟨hb, le_rfl⟩ : Bd * r ∈ Set.Icc 0 (Bd * r))
    have hsplit : ((G.colU r).map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi -
          6 * (P.hi - P.lo))).sum =
        ((G.colU r).map fun P => P.w * pairEnergy P.lo P.hi P'.lo P'.hi).sum -
          6 * pmass (G.colU r) := by
      unfold pmass
      have e : (G.colU r).map (fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi -
            6 * (P.hi - P.lo))) =
          (G.colU r).map (fun P => P.w * pairEnergy P.lo P.hi P'.lo P'.hi - 6 * Piece.mass P) :=
        List.map_congr_left (fun P _ => by unfold Piece.mass; ring)
      rw [e, lsum_sub, List.sum_map_mul_left]
    rw [hsplit] at h
    rw [← Finset.mul_sum]
    have hD0 : (0 : ℝ) ≤ (G.colConstR : ℝ) := Nat.cast_nonneg _
    have h2 : G.colConstR * (|kapInt P'.lo P'.hi (Bd * r)| +
        4 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))) ≤
        G.colConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hD0
    have h3 : ((G.colU r).map fun P => P.w * pairEnergy P.lo P.hi P'.lo P'.hi).sum -
        6 * pmass (G.colU r) - G.colConstR * (5 * ((P'.hi - P'.lo) *
          ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))) ≤
        ∑ a ∈ (G.geometry r).cols, kapInt P'.lo P'.hi (a : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left h3 hw'
    nlinarith [this]
  have hsum2 : ((G.colU r).map fun P' =>
        P'.w * ((G.colU r).map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi)).sum -
        P'.w * (6 * pmass (G.colU r) +
          G.colConstR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum ≤
      ((G.colU r).map fun P' => ∑ a ∈ (G.geometry r).cols,
        P'.w * kapInt P'.lo P'.hi (a : ℝ)).sum :=
    List.sum_le_sum hpiece
  rw [lsum_sub] at hsum2
  -- identify the energy
  have hE : ((G.colU r).map fun P' =>
      P'.w * ((G.colU r).map fun P => P.w * (pairEnergy P.lo P.hi P'.lo P'.hi)).sum).sum =
      mutE (G.colU r) (G.colU r) := by
    unfold mutE
    refine congrArg List.sum (List.map_congr_left (fun Q _ => ?_))
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left (fun P _ => ?_))
    unfold pairInteraction
    rw [pairEnergy_comm P.lo P.hi Q.lo Q.hi]
    ring
  rw [hE] at hsum2
  rw [hswap] at hsum1
  linarith

end BlockGeom

end CatalanCore.Uniform
