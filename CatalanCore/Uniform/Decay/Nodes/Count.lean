module
public import CatalanCore.Uniform.Frame.Block
@[expose] public section

/-!
# Prefix-count discrepancy of periodic-block nodes (Uniform Decay v2, Part 1, Lemma `counts`)

A block `{u r ≤ j < v r, j ≡ residue (mod d)}` has prefix count within `1` of the Lebesgue
prediction `max 0 (min ((x - u r)/d) (mass * r))` (mass `(v-u)/d`).  Everything is
explicit and uniform in the scale `r` and the cut `x`; collections add one per block, and the
balancing trim of a `BlockGeom` adds at most its trim size.
-/

namespace CatalanCore.Uniform
open Finset

/-- Number of elements of `s` that are at most `x`. -/
def prefixCount (s : Finset ℕ) (x : ℚ) : ℕ := (s.filter (fun j : ℕ => (j : ℚ) ≤ x)).card

theorem prefixCount_union_of_disjoint {s t : Finset ℕ} (h : Disjoint s t) (x : ℚ) :
    prefixCount (s ∪ t) x = prefixCount s x + prefixCount t x := by
  unfold prefixCount
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint (h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

theorem prefixCount_le_of_subset {s t : Finset ℕ} (h : s ⊆ t) (x : ℚ) :
    prefixCount s x ≤ prefixCount t x :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem prefixCount_le_add_sdiff {s t : Finset ℕ} (h : s ⊆ t) (x : ℚ) :
    prefixCount t x ≤ prefixCount s x + (t \ s).card := by
  unfold prefixCount
  have hsub : t.filter (fun j : ℕ => (j : ℚ) ≤ x) ⊆
      s.filter (fun j : ℕ => (j : ℚ) ≤ x) ∪ (t \ s) := by
    intro j hj
    obtain ⟨hjt, hjx⟩ := Finset.mem_filter.mp hj
    by_cases hjs : j ∈ s
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjs, hjx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hjt, hjs⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem prefixCount_biUnion {n : ℕ} (A : Fin n → Finset ℕ)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (x : ℚ) :
    prefixCount (Finset.univ.biUnion A) x = ∑ i, prefixCount (A i) x := by
  unfold prefixCount
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  intro i _ j _ hij
  exact (hA hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

namespace PeriodicBlock

/-- The Lebesgue prediction for the number of block nodes at most `x`:
`(1/d) |[u r, v r] ∩ (-∞, x]|`. -/
def prefixMass (b : PeriodicBlock) (r : ℕ) (x : ℚ) : ℚ :=
  max 0 (min ((x - b.u * r) / b.d) (b.mass * r))

theorem prefixMass_nonneg (b : PeriodicBlock) (r : ℕ) (x : ℚ) : 0 ≤ b.prefixMass r x :=
  le_max_left _ _

/-- Index cutoff: `k ≤ y` iff `k < cutoff y`. -/
noncomputable def cutoff (y : ℚ) : ℕ := if 0 ≤ y then ⌊y⌋₊ + 1 else 0

theorem le_iff_lt_cutoff (y : ℚ) (k : ℕ) : (k : ℚ) ≤ y ↔ k < cutoff y := by
  unfold cutoff
  by_cases hy : 0 ≤ y
  · rw [if_pos hy, Nat.lt_succ_iff, Nat.le_floor_iff hy]
  · rw [if_neg hy]
    simp only [Nat.not_lt_zero, iff_false, not_le]
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    linarith [not_le.mp hy]

theorem prefixCount_eq (b : PeriodicBlock) (r : ℕ) (x : ℚ) :
    prefixCount (b.nodes r) x =
      min (b.upper r) (cutoff ((x - b.residue) / b.d)) - b.lower r := by
  have hd : (0 : ℚ) < b.d := by exact_mod_cast b.hd
  unfold prefixCount nodes
  rw [Finset.filter_image, Finset.card_image_of_injective]
  · have : (Finset.Ico (b.lower r) (b.upper r)).filter
        (fun k => (((b.d * k + b.residue : ℕ)) : ℚ) ≤ x) =
        Finset.Ico (b.lower r) (min (b.upper r) (cutoff ((x - b.residue) / b.d))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ico, lt_min_iff]
      have hk : (((b.d * k + b.residue : ℕ)) : ℚ) ≤ x ↔ (k : ℚ) ≤ (x - b.residue) / b.d := by
        push_cast
        rw [le_div_iff₀ hd]
        constructor <;> intro h <;> nlinarith
      have hk' : ((fun k : ℕ => (((b.d * k + b.residue : ℕ)) : ℚ) ≤ x) k) ↔
          (k : ℚ) ≤ (x - b.residue) / b.d := hk
      simp only [Function.comp_apply] at *
      rw [hk, le_iff_lt_cutoff]
      tauto
    rw [this, Nat.card_Ico]
  · intro a c hac
    have hmul : b.d * a = b.d * c := Nat.add_right_cancel hac
    exact Nat.eq_of_mul_eq_mul_left b.hd hmul

private theorem ceil_lt_add_one' {a : ℚ} (ha : -1 < a) : (⌈a⌉₊ : ℚ) < a + 1 := by
  by_cases h : 0 ≤ a
  · exact Nat.ceil_lt_add_one h
  · have heq : ⌈a⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith)
    rw [heq]; norm_num; linarith

/-- **Per-block prefix discrepancy**, constant `1`, uniform in `r` and the cut `x`. -/
theorem abs_prefixCount_sub_prefixMass_le (b : PeriodicBlock) (r : ℕ) (x : ℚ) :
    |(prefixCount (b.nodes r) x : ℚ) - b.prefixMass r x| ≤ 1 := by
  have hd : (0 : ℚ) < b.d := by exact_mod_cast b.hd
  have hs : (b.residue : ℚ) < b.d := by exact_mod_cast b.hresidue
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  set y : ℚ := (x - b.residue) / b.d with hy
  set a : ℚ := (b.u * r - b.residue) / b.d with ha
  set bb : ℚ := (b.v * r - b.residue) / b.d with hbb
  have hamone : -1 < a := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith [b.hu]
  have hbmone : -1 < bb := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith [b.hu, b.huv]
  have hL1 : a ≤ (b.lower r : ℚ) := Nat.le_ceil a
  have hL2 : (b.lower r : ℚ) < a + 1 := ceil_lt_add_one' hamone
  have hU1 : bb ≤ (b.upper r : ℚ) := Nat.le_ceil bb
  have hU2 : (b.upper r : ℚ) < bb + 1 := ceil_lt_add_one' hbmone
  have hba : bb - a = b.mass * r := by simp only [hbb, ha]; unfold mass; ring
  have hya : y - a = (x - b.u * r) / b.d := by simp only [hy, ha]; ring
  have hmodel : b.prefixMass r x = max 0 (min y bb - a) := by
    unfold prefixMass
    rw [← hba, ← hya]
    congr 1
    rw [← min_sub_sub_right]
  rw [hmodel, prefixCount_eq]
  set W := cutoff y with hW
  have hWy : y < 0 → W = 0 := fun h => by simp [hW, cutoff, not_le.mpr h]
  have hWy' : 0 ≤ y → y < (W : ℚ) ∧ (W : ℚ) ≤ y + 1 := by
    intro h
    have hW' : W = ⌊y⌋₊ + 1 := by simp [hW, cutoff, h]
    rw [hW']
    push_cast
    exact ⟨Nat.lt_floor_add_one y, by linarith [Nat.floor_le h]⟩
  by_cases hneg : y < 0
  · rw [hWy hneg]
    simp only [_root_.min_zero, Nat.zero_sub, Nat.cast_zero, zero_sub]
    have h1 : 0 ≤ max 0 (min y bb - a) := le_max_left _ _
    have h2 : max 0 (min y bb - a) ≤ 1 := by
      refine max_le (by norm_num) ?_
      linarith [min_le_left y bb]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · push Not at hneg
    obtain ⟨hW1, hW2⟩ := hWy' hneg
    set M : ℕ := min (b.upper r) W with hM
    have hMcast : (M : ℚ) = min (b.upper r : ℚ) (W : ℚ) := by simp [hM]
    have hM1 : min y bb ≤ (M : ℚ) := by
      rw [hMcast]
      exact le_min (le_trans (min_le_right _ _) hU1) (le_trans (min_le_left _ _) hW1.le)
    have hM2 : (M : ℚ) ≤ min y bb + 1 := by
      rw [hMcast]
      by_cases hc : bb ≤ y
      · rw [min_eq_right hc]
        linarith [min_le_left (b.upper r : ℚ) (W : ℚ)]
      · push Not at hc
        rw [min_eq_left hc.le]
        linarith [min_le_right (b.upper r : ℚ) (W : ℚ)]
    have hcount : (((M - b.lower r : ℕ)) : ℚ) = max 0 ((M : ℚ) - b.lower r) := by
      by_cases hle : b.lower r ≤ M
      · rw [Nat.cast_sub hle]
        exact (max_eq_right (by
          have : (b.lower r : ℚ) ≤ M := by exact_mod_cast hle
          linarith)).symm
      · push Not at hle
        rw [Nat.sub_eq_zero_of_le hle.le]
        simp only [Nat.cast_zero]
        exact (max_eq_left (by
          have : (M : ℚ) ≤ b.lower r := by exact_mod_cast hle.le
          linarith)).symm
    rw [hcount]
    have key : ∀ p q : ℚ, |max 0 p - max 0 q| ≤ |p - q| := by
      intro p q
      rw [max_comm 0 p, max_comm 0 q]
      exact abs_max_sub_max_le_abs p q 0
    refine (key _ _).trans ?_
    rw [abs_le]
    constructor <;> linarith

end PeriodicBlock

/-! ### Collections -/

namespace BlockCollection

/-- Lebesgue prediction of the prefix count of a block collection. -/
def prefixMass (B : BlockCollection) (r : ℕ) (x : ℚ) : ℚ := ∑ i, (B.block i).prefixMass r x

theorem prefixCount_nodes (B : BlockCollection) (r : ℕ) (x : ℚ) :
    prefixCount (B.nodes r) x = ∑ i, prefixCount ((B.block i).nodes r) x :=
  prefixCount_biUnion _ (fun _ _ hij => B.separated r hij) x

/-- **Collection prefix discrepancy**: at most one per block, uniform in `r` and `x`. -/
theorem abs_prefixCount_sub_prefixMass_le (B : BlockCollection) (r : ℕ) (x : ℚ) :
    |(prefixCount (B.nodes r) x : ℚ) - B.prefixMass r x| ≤ B.n := by
  rw [B.prefixCount_nodes]
  unfold prefixMass
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |(prefixCount ((B.block i).nodes r) x : ℚ) - (B.block i).prefixMass r x|
      ≤ ∑ _i : Fin B.n, (1 : ℚ) :=
        Finset.sum_le_sum fun i _ => (B.block i).abs_prefixCount_sub_prefixMass_le r x
    _ = B.n := by simp

end BlockCollection

/-! ### Row and column node lists of a block geometry -/

namespace BlockGeom

/-- Lebesgue prediction of the row node list `C ∪ X'`: common plus row blocks. -/
def rowMass (G : BlockGeom) (r : ℕ) (x : ℚ) : ℚ :=
  G.common.prefixMass r x + G.row.prefixMass r x

/-- Lebesgue prediction of the column node list `C ∪ Y'`. -/
def colMass (G : BlockGeom) (r : ℕ) (x : ℚ) : ℚ :=
  G.common.prefixMass r x + G.column.prefixMass r x

/-- The prefix-discrepancy constant of the row list, `D_R = E_C + E_X + T`, with
`E_A = n_A` (one per block) and `T = n_row + n_column` the trim bound. -/
def rowConst (G : BlockGeom) : ℕ := G.common.n + G.row.n + (G.row.n + G.column.n)

def colConst (G : BlockGeom) : ℕ := G.common.n + G.column.n + (G.row.n + G.column.n)

theorem prefixCount_rows (G : BlockGeom) (r : ℕ) (x : ℚ) :
    prefixCount (G.geometry r).rows x =
      prefixCount (G.common.nodes r) x + prefixCount (G.geometry r).X' x :=
  prefixCount_union_of_disjoint (G.geometry r).disjCX x

theorem prefixCount_cols (G : BlockGeom) (r : ℕ) (x : ℚ) :
    prefixCount (G.geometry r).cols x =
      prefixCount (G.common.nodes r) x + prefixCount (G.geometry r).Y' x :=
  prefixCount_union_of_disjoint (G.geometry r).disjCY x

/-- A trimmed border prefix count differs from the raw one by at most the trim size. -/
theorem trim_prefix_row (G : BlockGeom) (r : ℕ) (x : ℚ) :
    |(prefixCount (G.geometry r).X' x : ℚ) - prefixCount (G.row.nodes r) x| ≤
      G.row.n + G.column.n := by
  have hsub : (G.geometry r).X' ⊆ G.row.nodes r := G.trim.subset _ _
  have h1 := prefixCount_le_of_subset hsub x
  have h2 := prefixCount_le_add_sdiff hsub x
  have hcard : ((G.row.nodes r) \ (G.geometry r).X').card ≤ G.row.n + G.column.n := by
    rw [Finset.card_sdiff_of_subset hsub]
    exact (G.trim_bound r).1
  have h3 : (prefixCount (G.row.nodes r) x : ℚ) ≤ prefixCount (G.geometry r).X' x +
      ((G.row.n + G.column.n : ℕ) : ℚ) := by exact_mod_cast h2.trans (by omega)
  have h1' : (prefixCount (G.geometry r).X' x : ℚ) ≤ prefixCount (G.row.nodes r) x := by
    exact_mod_cast h1
  rw [abs_le]
  push_cast at h3
  constructor <;> linarith

theorem trim_prefix_col (G : BlockGeom) (r : ℕ) (x : ℚ) :
    |(prefixCount (G.geometry r).Y' x : ℚ) - prefixCount (G.column.nodes r) x| ≤
      G.row.n + G.column.n := by
  have hsub : (G.geometry r).Y' ⊆ G.column.nodes r := G.trim.subset _ _
  have h1 := prefixCount_le_of_subset hsub x
  have h2 := prefixCount_le_add_sdiff hsub x
  have hcard : ((G.column.nodes r) \ (G.geometry r).Y').card ≤ G.row.n + G.column.n := by
    rw [Finset.card_sdiff_of_subset hsub]
    exact (G.trim_bound r).2
  have h3 : (prefixCount (G.column.nodes r) x : ℚ) ≤ prefixCount (G.geometry r).Y' x +
      ((G.row.n + G.column.n : ℕ) : ℚ) := by exact_mod_cast h2.trans (by omega)
  have h1' : (prefixCount (G.geometry r).Y' x : ℚ) ≤ prefixCount (G.column.nodes r) x := by
    exact_mod_cast h1
  rw [abs_le]
  push_cast at h3
  constructor <;> linarith

/-- **Row-list prefix discrepancy** `D_R = E_C + E_X + T`, uniform over every balancing
convention and every cut. -/
theorem abs_prefixCount_rows_sub_le (G : BlockGeom) (r : ℕ) (x : ℚ) :
    |(prefixCount (G.geometry r).rows x : ℚ) - G.rowMass r x| ≤ G.rowConst := by
  rw [G.prefixCount_rows]
  have hc := G.common.abs_prefixCount_sub_prefixMass_le r x
  have hx := G.row.abs_prefixCount_sub_prefixMass_le r x
  have ht := G.trim_prefix_row r x
  unfold rowMass rowConst
  push_cast
  rw [abs_le] at hc hx ht ⊢
  constructor <;> linarith [hc.1, hc.2, hx.1, hx.2, ht.1, ht.2]

theorem abs_prefixCount_cols_sub_le (G : BlockGeom) (r : ℕ) (x : ℚ) :
    |(prefixCount (G.geometry r).cols x : ℚ) - G.colMass r x| ≤ G.colConst := by
  rw [G.prefixCount_cols]
  have hc := G.common.abs_prefixCount_sub_prefixMass_le r x
  have hx := G.column.abs_prefixCount_sub_prefixMass_le r x
  have ht := G.trim_prefix_col r x
  unfold colMass colConst
  push_cast
  rw [abs_le] at hc hx ht ⊢
  constructor <;> linarith [hc.1, hc.2, hx.1, hx.2, ht.1, ht.2]

end BlockGeom
end CatalanCore.Uniform
