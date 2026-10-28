module
public import CatalanCore.Uniform.Decay.Nodes.FreePotential
public import CatalanCore.Uniform.Decay.Nodes.Limit
@[expose] public section

/-!
# Real-cut discrepancy of block node lists, in physical coordinates

For a `BlockGeom` the row list `R_r = C ∪ X'` has counting function within
`D_R + n_C + n_row` (real cut) of the cumulative function `lamSum (rowU G r)` of the
unscaled pieces `(1/d, [u r, v r])`.  This is the hypothesis `hD` of
`free_potential_discrepancy`, with explicit constants.
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset

namespace PeriodicBlock

/-- Unscaled limiting piece of one block residue at scale `r`: density `1/d` on `[u r, v r]`. -/
noncomputable def upiece (b : PeriodicBlock) (r : ℕ) : Piece :=
  ⟨1 / (b.d : ℝ), (b.u : ℝ) * r, (b.v : ℝ) * r⟩

/-- The rational Lebesgue prediction of `Count` is the cumulative function of the piece. -/
theorem prefixMass_cast (b : PeriodicBlock) (r : ℕ) (x : ℚ) :
    ((b.prefixMass r x : ℚ) : ℝ) = pieceLam (1 / (b.d : ℝ)) ((b.u : ℝ) * r) ((b.v : ℝ) * r) (x : ℝ) := by
  have hd : (0 : ℝ) < b.d := by exact_mod_cast b.hd
  have hc : (0 : ℝ) ≤ 1 / (b.d : ℝ) := by positivity
  unfold prefixMass pieceLam mass
  push_cast
  have e1 : ((x : ℝ) - b.u * r) / b.d = (1 / (b.d : ℝ)) * ((x : ℝ) - b.u * r) := by ring
  have e2 : ((b.v : ℝ) - b.u) / b.d * r = (1 / (b.d : ℝ)) * ((b.v : ℝ) * r - b.u * r) := by ring
  rw [e1, e2, ← mul_min_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc, mul_zero,
    ← min_sub_sub_right]

theorem abs_pieceLam_sub_le {w lo hi : ℝ} (hw : 0 ≤ w) (t t' : ℝ) :
    |pieceLam w lo hi t - pieceLam w lo hi t'| ≤ w * |t - t'| := by
  unfold pieceLam
  rw [← mul_sub, abs_mul, abs_of_nonneg hw]
  refine mul_le_mul_of_nonneg_left ?_ hw
  have key : ∀ p q : ℝ, |max 0 p - max 0 q| ≤ |p - q| := by
    intro p q
    rw [max_comm 0 p, max_comm 0 q]
    exact abs_max_sub_max_le_abs p q 0
  refine (key _ _).trans ?_
  have h := abs_min_sub_min_le_max t hi t' hi
  have h0 : max |t - t'| |hi - hi| = |t - t'| := by simp
  rw [h0] at h
  have h2 : min t hi - lo - (min t' hi - lo) = min t hi - min t' hi := by ring
  rw [h2]
  exact h

end PeriodicBlock

namespace BlockCollection

/-- Unscaled limiting pieces of a block collection. -/
noncomputable def upieces (B : BlockCollection) (r : ℕ) : List Piece :=
  (List.finRange B.n).map fun i => (B.block i).upiece r

theorem lamSum_upieces (B : BlockCollection) (r : ℕ) (t : ℝ) :
    lamSum (B.upieces r) t =
      ∑ i, pieceLam (1 / ((B.block i).d : ℝ)) (((B.block i).u : ℝ) * r)
        (((B.block i).v : ℝ) * r) t := by
  unfold lamSum upieces
  rw [List.map_map, ← Fin.sum_univ_def]
  rfl

theorem prefixMass_cast (B : BlockCollection) (r : ℕ) (x : ℚ) :
    ((B.prefixMass r x : ℚ) : ℝ) = lamSum (B.upieces r) (x : ℝ) := by
  rw [lamSum_upieces]
  unfold prefixMass
  push_cast
  exact Finset.sum_congr rfl fun i _ => (B.block i).prefixMass_cast r x

theorem abs_lamSum_sub_le (B : BlockCollection) (r : ℕ) (t t' : ℝ) :
    |lamSum (B.upieces r) t - lamSum (B.upieces r) t'| ≤ B.n * |t - t'| := by
  rw [lamSum_upieces, lamSum_upieces, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |pieceLam (1 / ((B.block i).d : ℝ)) (((B.block i).u : ℝ) * r)
        (((B.block i).v : ℝ) * r) t - pieceLam (1 / ((B.block i).d : ℝ))
        (((B.block i).u : ℝ) * r) (((B.block i).v : ℝ) * r) t'|
      ≤ ∑ _i : Fin B.n, (1 : ℝ) * |t - t'| := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hd : (1 : ℝ) ≤ (B.block i).d := by exact_mod_cast (B.block i).hd
        have hw : 1 / ((B.block i).d : ℝ) ≤ 1 := by
          rw [div_le_one (by linarith)]; exact hd
        refine (PeriodicBlock.abs_pieceLam_sub_le (by positivity) t t').trans ?_
        exact mul_le_mul_of_nonneg_right hw (abs_nonneg _)
    _ = B.n * |t - t'| := by simp

end BlockCollection

namespace BlockGeom

/-- Unscaled limiting row measure `μ_C + μ_X` at scale `r`. -/
noncomputable def rowU (G : BlockGeom) (r : ℕ) : List Piece :=
  G.common.upieces r ++ G.row.upieces r

noncomputable def colU (G : BlockGeom) (r : ℕ) : List Piece :=
  G.common.upieces r ++ G.column.upieces r

theorem lamSum_append (A B : List Piece) (t : ℝ) : lamSum (A ++ B) t = lamSum A t + lamSum B t := by
  simp [lamSum]

/-- Constant of the real-cut row discrepancy. -/
def rowConstR (G : BlockGeom) : ℕ := G.rowConst + G.common.n + G.row.n

def colConstR (G : BlockGeom) : ℕ := G.colConst + G.common.n + G.column.n

theorem card_filter_le_floor (A : Finset ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((A.filter (fun j : ℕ => j ≤ ⌊t⌋₊)).card : ℝ) = (prefixCount A (⌊t⌋₊ : ℚ) : ℝ) := by
  unfold prefixCount
  congr 2
  ext j
  simp only [Finset.mem_filter]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
  · exact_mod_cast h2
  · exact_mod_cast h2

/-- **Real-cut discrepancy of the row list**, as needed by `free_potential_discrepancy`. -/
theorem rows_real_discrepancy (G : BlockGeom) (r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |(((G.geometry r).rows.filter (fun j : ℕ => j ≤ ⌊t⌋₊)).card : ℝ) - lamSum (G.rowU r) t|
      ≤ G.rowConstR := by
  rw [card_filter_le_floor _ t ht]
  have h1 := G.abs_prefixCount_rows_sub_le r (⌊t⌋₊ : ℚ)
  have hmass : ((G.rowMass r (⌊t⌋₊ : ℚ) : ℚ) : ℝ) = lamSum (G.rowU r) (⌊t⌋₊ : ℝ) := by
    unfold rowMass rowU
    push_cast
    rw [lamSum_append, G.common.prefixMass_cast, G.row.prefixMass_cast]
    simp
  have hfl : |(⌊t⌋₊ : ℝ) - t| ≤ 1 := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le ht))]
    linarith [Nat.lt_floor_add_one t]
  have h2 : |lamSum (G.rowU r) (⌊t⌋₊ : ℝ) - lamSum (G.rowU r) t| ≤ G.common.n + G.row.n := by
    unfold rowU
    rw [lamSum_append, lamSum_append]
    have a1 := G.common.abs_lamSum_sub_le r (⌊t⌋₊ : ℝ) t
    have a2 := G.row.abs_lamSum_sub_le r (⌊t⌋₊ : ℝ) t
    have : lamSum (G.common.upieces r) (⌊t⌋₊ : ℝ) + lamSum (G.row.upieces r) (⌊t⌋₊ : ℝ) -
        (lamSum (G.common.upieces r) t + lamSum (G.row.upieces r) t) =
        (lamSum (G.common.upieces r) (⌊t⌋₊ : ℝ) - lamSum (G.common.upieces r) t) +
        (lamSum (G.row.upieces r) (⌊t⌋₊ : ℝ) - lamSum (G.row.upieces r) t) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg (α := ℝ) G.common.n),
      mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg (α := ℝ) G.row.n)]
  have h1' : |((prefixCount (G.geometry r).rows (⌊t⌋₊ : ℚ) : ℕ) : ℝ) -
      lamSum (G.rowU r) (⌊t⌋₊ : ℝ)| ≤ G.rowConst := by
    have := h1
    rw [← hmass]
    exact_mod_cast this
  have := abs_sub_le (((prefixCount (G.geometry r).rows (⌊t⌋₊ : ℚ) : ℕ) : ℝ))
    (lamSum (G.rowU r) (⌊t⌋₊ : ℝ)) (lamSum (G.rowU r) t)
  unfold rowConstR
  push_cast
  linarith

/-- **Real-cut discrepancy of the column list**, as needed by `free_potential_discrepancy`. -/
theorem cols_real_discrepancy (G : BlockGeom) (r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |(((G.geometry r).cols.filter (fun j : ℕ => j ≤ ⌊t⌋₊)).card : ℝ) - lamSum (G.colU r) t|
      ≤ G.colConstR := by
  rw [card_filter_le_floor _ t ht]
  have h1 := G.abs_prefixCount_cols_sub_le r (⌊t⌋₊ : ℚ)
  have hmass : ((G.colMass r (⌊t⌋₊ : ℚ) : ℚ) : ℝ) = lamSum (G.colU r) (⌊t⌋₊ : ℝ) := by
    unfold colMass colU
    push_cast
    rw [lamSum_append, G.common.prefixMass_cast, G.column.prefixMass_cast]
    simp
  have hfl : |(⌊t⌋₊ : ℝ) - t| ≤ 1 := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le ht))]
    linarith [Nat.lt_floor_add_one t]
  have h2 : |lamSum (G.colU r) (⌊t⌋₊ : ℝ) - lamSum (G.colU r) t| ≤ G.common.n + G.column.n := by
    unfold colU
    rw [lamSum_append, lamSum_append]
    have a1 := G.common.abs_lamSum_sub_le r (⌊t⌋₊ : ℝ) t
    have a2 := G.column.abs_lamSum_sub_le r (⌊t⌋₊ : ℝ) t
    have : lamSum (G.common.upieces r) (⌊t⌋₊ : ℝ) + lamSum (G.column.upieces r) (⌊t⌋₊ : ℝ) -
        (lamSum (G.common.upieces r) t + lamSum (G.column.upieces r) t) =
        (lamSum (G.common.upieces r) (⌊t⌋₊ : ℝ) - lamSum (G.common.upieces r) t) +
        (lamSum (G.column.upieces r) (⌊t⌋₊ : ℝ) - lamSum (G.column.upieces r) t) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg (α := ℝ) G.common.n),
      mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg (α := ℝ) G.column.n)]
  have h1' : |((prefixCount (G.geometry r).cols (⌊t⌋₊ : ℚ) : ℕ) : ℝ) -
      lamSum (G.colU r) (⌊t⌋₊ : ℝ)| ≤ G.colConst := by
    have := h1
    rw [← hmass]
    exact_mod_cast this
  have := abs_sub_le (((prefixCount (G.geometry r).cols (⌊t⌋₊ : ℚ) : ℕ) : ℝ))
    (lamSum (G.colU r) (⌊t⌋₊ : ℝ)) (lamSum (G.colU r) t)
  unfold colConstR
  push_cast
  linarith

end BlockGeom
end CatalanCore.Uniform
