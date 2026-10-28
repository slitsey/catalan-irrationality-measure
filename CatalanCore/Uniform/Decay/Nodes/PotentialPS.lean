module
public import CatalanCore.Uniform.Decay.Nodes.Scaled
@[expose] public section

/-!
# Free-point counting potentials of the row and column lists

`rows_ps_scaled`/`cols_ps_scaled`: for `σ = z/r` at physical distance in `[δ, M]` from `[0, Bd r]`,

`|∑_{j ∈ R_r} elog (z/r) (j/r) - r · U_{μ_R}(z/r)| ≤ D (|kern z b| + 2 (log M - log δ)) + K log r`

with `D = rowConstR`, `K = rowConst`, `b = Bd r`, uniform in the balancing trim and in `r`.
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

theorem pmass_cons (P : Piece) (ps : List Piece) : pmass (P :: ps) = P.mass + pmass ps := by
  simp [pmass]

/-- Physical limit of a list of scaled pieces. -/
theorem phys_limit (ps : List Piece) {r : ℕ} (hr : 0 < r) (z : ℂ) :
    ((ps.map fun P : Piece => (⟨P.w, P.lo * r, P.hi * r⟩ : Piece)).map
        fun Q : Piece => Q.w * ∫ x in Q.lo..Q.hi, elog z (x : ℂ)).sum =
      r * ppotC ps (z / r) - r * pmass ps * Real.log r := by
  induction ps with
  | nil => simp [ppotC, pmass]
  | cons P ps ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [piece_integral_scale z hr P.w P.lo P.hi]
    unfold ppotC pmass at ih ⊢
    simp only [List.map_cons, List.sum_cons, Piece.mass] at ih ⊢
    have : (List.map (fun P : Piece => P.w * ∫ t in P.lo..P.hi, elog (z / r) (t : ℂ)) ps).sum =
      (List.map (fun P : Piece => P.w * ∫ t in P.lo..P.hi, elog (z / r) (t : ℂ)) ps).sum := rfl
    linarith [ih]

namespace PeriodicBlock

theorem upiece_eq (b : PeriodicBlock) (r : ℕ) :
    b.upiece r = (⟨b.piece.w, b.piece.lo * r, b.piece.hi * r⟩ : Piece) := rfl

end PeriodicBlock

namespace BlockCollection

theorem upieces_eq (B : BlockCollection) (r : ℕ) :
    B.upieces r = B.pieces.map fun P : Piece => (⟨P.w, P.lo * r, P.hi * r⟩ : Piece) := by
  unfold upieces pieces
  rw [List.map_map]
  rfl

end BlockCollection

namespace BlockGeom

theorem rowU_eq (G : BlockGeom) (r : ℕ) :
    G.rowU r = G.rowPieces.map fun P : Piece => (⟨P.w, P.lo * r, P.hi * r⟩ : Piece) := by
  unfold rowU rowPieces
  rw [List.map_append, G.common.upieces_eq, G.row.upieces_eq]

theorem colU_eq (G : BlockGeom) (r : ℕ) :
    G.colU r = G.colPieces.map fun P : Piece => (⟨P.w, P.lo * r, P.hi * r⟩ : Piece) := by
  unfold colU colPieces
  rw [List.map_append, G.common.upieces_eq, G.column.upieces_eq]

/-- Mass rounding: `|#R_r - M r| ≤ D_R`. -/
theorem card_rows_bound (G : BlockGeom) (r : ℕ) :
    |(((G.geometry r).rows.card : ℕ) : ℝ) - (G.totalMass : ℝ) * r| ≤ G.rowConst := by
  have hc := G.card_common r
  have hx := G.row.count_bounds r
  have ht := (G.trim_bound r).1
  have hk : (G.geometry r).X'.card ≤ (G.row.nodes r).card := by
    have := Finset.card_le_card (G.trim.subset (G.row.nodes r) (G.borderSize r))
    exact this
  have hrows : (G.geometry r).rows.card = (G.geometry r).C.card + (G.geometry r).X'.card := by
    unfold Rect.Geometry.rows
    exact Finset.card_union_of_disjoint (G.geometry r).disjCX
  rw [hrows]
  have hCq : G.common.mass * r - G.common.n ≤ (((G.geometry r).C.card : ℕ) : ℚ) := hc.1
  have hCq' : (((G.geometry r).C.card : ℕ) : ℚ) ≤ G.common.mass * r + G.common.n := hc.2
  have hXq1 : (((G.geometry r).X'.card : ℕ) : ℚ) ≤ G.row.mass * r + G.row.n := by
    have : (((G.geometry r).X'.card : ℕ) : ℚ) ≤ (((G.row.nodes r).card : ℕ) : ℚ) := by
      exact_mod_cast hk
    linarith [hx.2]
  have hXq2 : G.row.mass * r - G.row.n - (G.row.n + G.column.n) ≤
      (((G.geometry r).X'.card : ℕ) : ℚ) := by
    have : ((G.row.nodes r).card : ℚ) ≤ (G.geometry r).X'.card + (G.row.n + G.column.n : ℕ) := by
      exact_mod_cast (by omega : (G.row.nodes r).card ≤ (G.geometry r).X'.card + (G.row.n + G.column.n))
    push_cast at this
    linarith [hx.1]
  have hq : |((((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℚ)) -
      (G.common.mass + G.row.mass) * r| ≤ (G.rowConst : ℚ) := by
    rw [abs_le]
    unfold rowConst
    push_cast
    constructor <;> push_cast <;> nlinarith [hCq, hCq', hXq1, hXq2]
  have hq' : ((|((((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℚ)) -
      (G.common.mass + G.row.mass) * r| : ℚ) : ℝ) ≤ ((G.rowConst : ℚ) : ℝ) := by
    exact_mod_cast hq
  push_cast at hq'
  unfold totalMass gamma beta
  push_cast
  simpa using hq'

/-- Mass rounding for the column list: `|#Q_r - M r| ≤ D_Q`. -/
theorem card_cols_bound (G : BlockGeom) (r : ℕ) :
    |(((G.geometry r).cols.card : ℕ) : ℝ) - (G.totalMass : ℝ) * r| ≤ G.colConst := by
  have hc := G.card_common r
  have hx := G.column.count_bounds r
  rw [← G.border_mass] at hx
  have ht := (G.trim_bound r).2
  have hk : (G.geometry r).Y'.card ≤ (G.column.nodes r).card := by
    have := Finset.card_le_card (G.trim.subset (G.column.nodes r) (G.borderSize r))
    exact this
  have hrows : (G.geometry r).cols.card = (G.geometry r).C.card + (G.geometry r).Y'.card := by
    unfold Rect.Geometry.cols
    exact Finset.card_union_of_disjoint (G.geometry r).disjCY
  rw [hrows]
  have hCq : G.common.mass * r - G.common.n ≤ (((G.geometry r).C.card : ℕ) : ℚ) := hc.1
  have hCq' : (((G.geometry r).C.card : ℕ) : ℚ) ≤ G.common.mass * r + G.common.n := hc.2
  have hXq1 : (((G.geometry r).Y'.card : ℕ) : ℚ) ≤ G.row.mass * r + G.column.n := by
    have : (((G.geometry r).Y'.card : ℕ) : ℚ) ≤ (((G.column.nodes r).card : ℕ) : ℚ) := by
      exact_mod_cast hk
    linarith [hx.2]
  have hXq2 : G.row.mass * r - G.column.n - (G.row.n + G.column.n) ≤
      (((G.geometry r).Y'.card : ℕ) : ℚ) := by
    have : ((G.column.nodes r).card : ℚ) ≤ (G.geometry r).Y'.card + (G.row.n + G.column.n : ℕ) := by
      exact_mod_cast (by omega : (G.column.nodes r).card ≤ (G.geometry r).Y'.card + (G.row.n + G.column.n))
    push_cast at this
    linarith [hx.1]
  have hq : |((((G.geometry r).C.card + (G.geometry r).Y'.card : ℕ) : ℚ)) -
      (G.common.mass + G.row.mass) * r| ≤ (G.colConst : ℚ) := by
    rw [abs_le]
    unfold colConst
    push_cast
    constructor <;> push_cast <;> nlinarith [hCq, hCq', hXq1, hXq2]
  have hq' : ((|((((G.geometry r).C.card + (G.geometry r).Y'.card : ℕ) : ℚ)) -
      (G.common.mass + G.row.mass) * r| : ℚ) : ℝ) ≤ ((G.colConst : ℚ) : ℝ) := by
    exact_mod_cast hq
  push_cast at hq'
  unfold totalMass gamma beta
  push_cast
  simpa using hq'

theorem mem_rows_cases (G : BlockGeom) (r j : ℕ) (h : j ∈ (G.geometry r).rows) :
    j ∈ G.common.nodes r ∨ j ∈ G.row.nodes r := by
  unfold Rect.Geometry.rows at h
  rcases Finset.mem_union.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (G.trim.subset _ _ h)

theorem mem_cols_cases (G : BlockGeom) (r j : ℕ) (h : j ∈ (G.geometry r).cols) :
    j ∈ G.common.nodes r ∨ j ∈ G.column.nodes r := by
  unfold Rect.Geometry.cols at h
  rcases Finset.mem_union.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (G.trim.subset _ _ h)

theorem node_lt_bound (B : BlockCollection) (r j : ℕ) {Bd : ℝ}
    (hB : ∀ i, ((B.block i).v : ℝ) ≤ Bd) (h : j ∈ B.nodes r) : (j : ℝ) ≤ Bd * r := by
  unfold BlockCollection.nodes at h
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
  have := ((B.block i).mem_nodes r j).mp hi
  have h2 : ((j : ℚ)) < (B.block i).v * r := this.2.1
  have h3 : (j : ℝ) < ((B.block i).v : ℝ) * r := by exact_mod_cast h2
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith [hB i]

theorem upieces_bound (B : BlockCollection) (r : ℕ) {Bd : ℝ}
    (hB : ∀ i, ((B.block i).v : ℝ) ≤ Bd) :
    ∀ P ∈ B.upieces r, 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ Bd * r := by
  intro P hP
  unfold BlockCollection.upieces at hP
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hP
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hu : (0 : ℝ) ≤ ((B.block i).u : ℝ) := by exact_mod_cast (B.block i).hu
  have huv : ((B.block i).u : ℝ) ≤ ((B.block i).v : ℝ) := by exact_mod_cast (B.block i).huv.le
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ ((B.block i).u : ℝ) * r
    positivity
  · show ((B.block i).u : ℝ) * r ≤ ((B.block i).v : ℝ) * r
    exact mul_le_mul_of_nonneg_right huv hr
  · show ((B.block i).v : ℝ) * r ≤ Bd * r
    exact mul_le_mul_of_nonneg_right (hB i) hr

/-- **Row free-point potential.** -/
theorem rows_ps_scaled (G : BlockGeom) {r : ℕ} (hr : 0 < r) (z : ℂ) {Bd δ M : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd)
    (hδ : 0 < δ) (hd : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), δ ≤ ‖z - (t : ℂ)‖)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), ‖z - (t : ℂ)‖ ≤ M) :
    |(∑ j ∈ (G.geometry r).rows, elog (z / r) ((j : ℂ) / r)) - r * ppotC G.rowPieces (z / r)| ≤
      G.rowConstR * (|kern z (Bd * r)| + 2 * (Real.log M - Real.log δ)) +
        G.rowConst * Real.log r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hb : 0 ≤ Bd * r := by positivity
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
  have hfp := free_potential_discrepancy (G.geometry r).rows (G.rowU r) z hb hδ hd hM hps hA
    (fun t ht => G.rows_real_discrepancy r ht.1)
  -- conversions
  have hconv : ∀ j ∈ (G.geometry r).rows,
      elog (z / r) ((j : ℂ) / r) = elog z (j : ℂ) + Real.log r := by
    intro j hj
    have hjb := hA j hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hdj := hd (j : ℝ) ⟨hj0, hjb⟩
    have hne : ‖z - (j : ℂ)‖ ≠ 0 := by
      have : 0 < ‖z - ((j : ℝ) : ℂ)‖ := lt_of_lt_of_le hδ hdj
      simpa using this.ne'
    unfold elog
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have : z / r - (j : ℂ) / r = (z - (j : ℂ)) / r := by ring
    rw [this, norm_div, Complex.norm_natCast, Real.log_div hne hr'.ne']
    ring
  have hsum : ∑ j ∈ (G.geometry r).rows, elog (z / r) ((j : ℂ) / r) =
      ∑ j ∈ (G.geometry r).rows, elog z (j : ℂ) +
        ((G.geometry r).rows.card : ℝ) * Real.log r := by
    rw [Finset.sum_congr rfl hconv, Finset.sum_add_distrib]
    simp
  have hlim := phys_limit G.rowPieces hr z
  rw [← G.rowU_eq r] at hlim
  rw [G.pmass_rowPieces] at hlim
  have hcard := G.card_rows_bound r
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  rw [hsum]
  have e : (∑ j ∈ (G.geometry r).rows, elog z (j : ℂ) +
        ((G.geometry r).rows.card : ℝ) * Real.log r) - r * ppotC G.rowPieces (z / r) =
      ((∑ j ∈ (G.geometry r).rows, elog z (j : ℂ)) -
        ((G.rowU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum) +
      (((G.geometry r).rows.card : ℝ) - (G.totalMass : ℝ) * r) * Real.log r := by
    have := hlim
    linarith [this]
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add hfp ?_)
  rw [abs_mul, abs_of_nonneg hlog]
  exact mul_le_mul_of_nonneg_right hcard hlog

/-- **Column free-point potential.** -/
theorem cols_ps_scaled (G : BlockGeom) {r : ℕ} (hr : 0 < r) (z : ℂ) {Bd δ M : ℝ}
    (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    (hδ : 0 < δ) (hd : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), δ ≤ ‖z - (t : ℂ)‖)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) (Bd * r), ‖z - (t : ℂ)‖ ≤ M) :
    |(∑ j ∈ (G.geometry r).cols, elog (z / r) ((j : ℂ) / r)) - r * ppotC G.colPieces (z / r)| ≤
      G.colConstR * (|kern z (Bd * r)| + 2 * (Real.log M - Real.log δ)) +
        G.colConst * Real.log r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hb : 0 ≤ Bd * r := by positivity
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
  have hfp := free_potential_discrepancy (G.geometry r).cols (G.colU r) z hb hδ hd hM hps hA
    (fun t ht => G.cols_real_discrepancy r ht.1)
  -- conversions
  have hconv : ∀ j ∈ (G.geometry r).cols,
      elog (z / r) ((j : ℂ) / r) = elog z (j : ℂ) + Real.log r := by
    intro j hj
    have hjb := hA j hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hdj := hd (j : ℝ) ⟨hj0, hjb⟩
    have hne : ‖z - (j : ℂ)‖ ≠ 0 := by
      have : 0 < ‖z - ((j : ℝ) : ℂ)‖ := lt_of_lt_of_le hδ hdj
      simpa using this.ne'
    unfold elog
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have : z / r - (j : ℂ) / r = (z - (j : ℂ)) / r := by ring
    rw [this, norm_div, Complex.norm_natCast, Real.log_div hne hr'.ne']
    ring
  have hsum : ∑ j ∈ (G.geometry r).cols, elog (z / r) ((j : ℂ) / r) =
      ∑ j ∈ (G.geometry r).cols, elog z (j : ℂ) +
        ((G.geometry r).cols.card : ℝ) * Real.log r := by
    rw [Finset.sum_congr rfl hconv, Finset.sum_add_distrib]
    simp
  have hlim := phys_limit G.colPieces hr z
  rw [← G.colU_eq r] at hlim
  rw [G.pmass_colPieces] at hlim
  have hcard := G.card_cols_bound r
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  rw [hsum]
  have e : (∑ j ∈ (G.geometry r).cols, elog z (j : ℂ) +
        ((G.geometry r).cols.card : ℝ) * Real.log r) - r * ppotC G.colPieces (z / r) =
      ((∑ j ∈ (G.geometry r).cols, elog z (j : ℂ)) -
        ((G.colU r).map fun P => P.w * ∫ x in P.lo..P.hi, elog z (x : ℂ)).sum) +
      (((G.geometry r).cols.card : ℝ) - (G.totalMass : ℝ) * r) * Real.log r := by
    have := hlim
    linarith [this]
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add hfp ?_)
  rw [abs_mul, abs_of_nonneg hlog]
  exact mul_le_mul_of_nonneg_right hcard hlog

end BlockGeom
end CatalanCore.Uniform
