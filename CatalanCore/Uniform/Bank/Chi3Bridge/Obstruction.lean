import CatalanCore.Uniform.Frame.Block
set_option Elab.async false

/-! Lane B, B3e: the old `commonMinorFam` node geometry is not a `BlockGeom`.

The old χ₋₃ family (`CatalanCore.Rect.commonMinorFam p6Frame Quarter.Adm d`) has, for every `r ≥ 1`,
common nodes `0, …, r-1`, row nodes `r, r+2, …` and column nodes `r+1, r+3, …`; in particular `r` is
a row node and `r+1` a column node at EVERY scale `r`.  The residue of a periodic block is fixed, so
no `BlockGeom` (hence no `BlockGeom.family`) can have these border nodes at all scales. -/

namespace CatalanCore.Uniform.Bank.Chi3Bridge
open CatalanCore.Uniform

theorem no_blockgeom_has_old_border_nodes (G : BlockGeom) :
    ¬ ∀ r : ℕ, 1 ≤ r → r ∈ (G.geometry r).X' ∧ r + 1 ∈ (G.geometry r).Y' := by
  intro H
  -- a scale `R` beyond every `1/(v-1)` of a row block with `v > 1`
  set R : ℕ := (∑ i : Fin G.row.n, ⌈(1 : ℚ) / ((G.row.block i).v - 1)⌉₊) + 1 with hR
  have hR1 : 1 ≤ R := by omega
  obtain ⟨hX, _⟩ := H (R + 1) (by omega)
  have hXrow : R + 1 ∈ G.row.nodes (R + 1) := G.trim.subset _ _ hX
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hXrow
  obtain ⟨hu, hv, -⟩ := (G.row.block i).mem_nodes (R + 1) (R + 1) |>.mp hi
  have hRq : (0 : ℚ) < ((R + 1 : ℕ) : ℚ) := by positivity
  push_cast at hu hv hRq
  have hv1 : 1 < (G.row.block i).v := by
    by_contra h
    push Not at h
    nlinarith
  have hu1 : (G.row.block i).u ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith
  have hu0 := (G.row.block i).hu
  have hle : ⌈(1 : ℚ) / ((G.row.block i).v - 1)⌉₊ ≤ ∑ j : Fin G.row.n, ⌈(1 : ℚ) / ((G.row.block j).v - 1)⌉₊ :=
    Finset.single_le_sum (f := fun j : Fin G.row.n => ⌈(1 : ℚ) / ((G.row.block j).v - 1)⌉₊)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hceil : (1 : ℚ) / ((G.row.block i).v - 1) ≤ ⌈(1 : ℚ) / ((G.row.block i).v - 1)⌉₊ :=
    Nat.le_ceil _
  have hpos : (0 : ℚ) < (G.row.block i).v - 1 := by linarith
  have hle' : (⌈(1 : ℚ) / ((G.row.block i).v - 1)⌉₊ : ℚ) + 1 ≤ R := by
    have : ⌈(1 : ℚ) / ((G.row.block i).v - 1)⌉₊ + 1 ≤ R := by omega
    exact_mod_cast this
  have hkey : (1 : ℚ) < ((G.row.block i).v - 1) * R := by
    have h1 : 1 ≤ ((G.row.block i).v - 1) * (⌈(1 : ℚ) / ((G.row.block i).v - 1)⌉₊ : ℚ) := by
      calc (1 : ℚ) = ((G.row.block i).v - 1) * (1 / ((G.row.block i).v - 1)) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hceil hpos.le
    nlinarith
  have hRq0 : (0 : ℚ) ≤ R := Nat.cast_nonneg _
  have hmem : R + 1 ∈ (G.row.block i).nodes R := by
    refine ((G.row.block i).mem_nodes R (R + 1)).mpr ⟨?_, ?_, ?_⟩
    · push_cast; nlinarith
    · push_cast; nlinarith
    · exact ((G.row.block i).mem_nodes (R + 1) (R + 1) |>.mp hi).2.2
  have hrow : R + 1 ∈ G.row.nodes R :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hmem⟩
  obtain ⟨-, hY⟩ := H R hR1
  have hcol : R + 1 ∈ G.column.nodes R := G.trim.subset _ _ hY
  exact Finset.disjoint_left.mp (G.disjRC R) hrow hcol

end CatalanCore.Uniform.Bank.Chi3Bridge
