module
public import CatalanCore.Uniform.Frame.Block
public import CatalanCore.Uniform.NV.StepGeometry
@[expose] public section

namespace CatalanCore.Uniform
open Finset
open NV

/-- Trimming nodes creates at most one new step component per removed node. -/
theorem components_subset {X Y : Finset ℕ} (hYX : Y ⊆ X) (L : ℕ) :
    componentCount Y L ≤ componentCount X L + (X \ Y).card := by
  have hnew : (stepEnds Y L \ stepEnds X L).card ≤ (X \ Y).card := by
    apply Finset.card_le_card_of_injOn (fun a => a + L)
    · intro a ha
      obtain ⟨haY, haX⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨hay, hnot⟩ := mem_stepEnds.mp haY
      have hnext : a + L ∈ X := by
        by_contra h
        exact haX (mem_stepEnds.mpr ⟨hYX hay, h⟩)
      exact Finset.mem_sdiff.mpr ⟨hnext, hnot⟩
    · intro a ha b hb heq
      exact Nat.add_right_cancel heq
  have hcard := Finset.card_le_card_sdiff_add_card (s := stepEnds Y L) (t := stepEnds X L)
  unfold componentCount
  omega

/-- A union cannot have more components than the sum of its parts. -/
theorem components_union (X Y : Finset ℕ) (L : ℕ) :
    componentCount (X ∪ Y) L ≤ componentCount X L + componentCount Y L := by
  have hsub : stepEnds (X ∪ Y) L ⊆ stepEnds X L ∪ stepEnds Y L := by
    intro a ha
    obtain ⟨ha, hn⟩ := mem_stepEnds.mp ha
    rcases Finset.mem_union.mp ha with hx | hy
    · exact Finset.mem_union_left _ (mem_stepEnds.mpr ⟨hx, fun h => hn (Finset.mem_union_left _ h)⟩)
    · exact Finset.mem_union_right _ (mem_stepEnds.mpr ⟨hy, fun h => hn (Finset.mem_union_right _ h)⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem components_biUnion {ι : Type} [DecidableEq ι] (s : Finset ι)
    (Z : ι → Finset ℕ) (L : ℕ) :
    componentCount (s.biUnion Z) L ≤ ∑ i ∈ s, componentCount (Z i) L := by
  induction s using Finset.induction_on with
  | empty => simp [componentCount, stepEnds]
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (components_union _ _ L).trans (Nat.add_le_add_left ih _)

namespace PeriodicBlock

/-- A single residue block contains at most L/d step-L chains. -/
theorem components_le (b : PeriodicBlock) (r L : ℕ) (hdiv : b.d ∣ L) :
    componentCount (b.nodes r) L ≤ L / b.d := by
  have hmult : b.d * (L / b.d) = L := by
    simpa [Nat.mul_comm] using Nat.div_mul_cancel hdiv
  have hinj : (stepEnds (b.nodes r) L : Set ℕ).InjOn (fun j => j / b.d) := by
    intro a ha c hc heq
    have hma := (b.mem_nodes r a).mp ((mem_stepEnds.mp ha).1)
    have hmc := (b.mem_nodes r c).mp ((mem_stepEnds.mp hc).1)
    have hA := Nat.mod_add_div a b.d
    have hC := Nat.mod_add_div c b.d
    rw [hma.2.2] at hA
    rw [hmc.2.2] at hC
    change a / b.d = c / b.d at heq
    rw [heq] at hA
    omega
  have hmap : Set.MapsTo (fun j => j / b.d) (stepEnds (b.nodes r) L)
      (Finset.Ico (b.upper r - L / b.d) (b.upper r)) := by
    intro j hj
    obtain ⟨hjn, hjnot⟩ := mem_stepEnds.mp hj
    obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hjn
    have hklo := (Finset.mem_Ico.mp hk).1
    have hkhi := (Finset.mem_Ico.mp hk).2
    have hquot : j / b.d = k := by
      rw [← hkj, Nat.mul_add_div b.hd, Nat.div_eq_of_lt b.hresidue, add_zero]
    have hlast : b.upper r ≤ k + L / b.d := by
      by_contra h
      apply hjnot
      apply Finset.mem_image.mpr
      refine ⟨k + L / b.d, Finset.mem_Ico.mpr
        ⟨hklo.trans (Nat.le_add_right _ _), Nat.lt_of_not_ge h⟩, ?_⟩
      rw [Nat.mul_add, hmult]
      omega
    change j / b.d ∈ Finset.Ico (b.upper r - L / b.d) (b.upper r)
    rw [hquot]
    exact Finset.mem_Ico.mpr ⟨by omega, hkhi⟩
  have hcard := Finset.card_le_card_of_injOn (fun j => j / b.d) hmap hinj
  rw [Nat.card_Ico] at hcard
  have hlength : b.upper r - (b.upper r - L / b.d) ≤ L / b.d := by
    rw [tsub_tsub_eq_min]
    exact min_le_right _ _
  exact hcard.trans hlength

end PeriodicBlock

namespace BlockCollection

def componentBudget (B : BlockCollection) (L : ℕ) : ℕ := ∑ i, L / (B.block i).d

theorem components_le (B : BlockCollection) (r L : ℕ)
    (hdiv : ∀ i, (B.block i).d ∣ L) :
    componentCount (B.nodes r) L ≤ B.componentBudget L := by
  apply (components_biUnion Finset.univ (fun i => (B.block i).nodes r) L).trans
  exact Finset.sum_le_sum fun i _ => (B.block i).components_le r L (hdiv i)

theorem n_le_budget (B : BlockCollection) (L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i, (B.block i).d ∣ L) : B.n ≤ B.componentBudget L := by
  have h : ∑ i : Fin B.n, 1 ≤ ∑ i : Fin B.n, L / (B.block i).d := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.div_pos (Nat.le_of_dvd hL (hdiv i)) (B.block i).hd
  simpa [componentBudget] using h

end BlockCollection

namespace BlockGeom

/-- The two border trims together have the same bounded discrepancy charge. -/
theorem trim_total_bound (G : BlockGeom) (r : ℕ) :
    ((G.row.nodes r) \ (G.geometry r).X').card +
      ((G.column.nodes r) \ (G.geometry r).Y').card ≤ G.row.n + G.column.n := by
  have hbound := G.trim_bound r
  have hx : (G.geometry r).X'.card = G.borderSize r := by
    change (G.trim.keep _ _).card = _
    rw [G.trim.card]
    exact min_eq_left (min_le_left _ _)
  have hy : (G.geometry r).Y'.card = G.borderSize r := by
    change (G.trim.keep _ _).card = _
    rw [G.trim.card]
    exact min_eq_left (min_le_right _ _)
  change ((G.row.nodes r) \ G.trim.keep (G.row.nodes r) (G.borderSize r)).card +
    ((G.column.nodes r) \ G.trim.keep (G.column.nodes r) (G.borderSize r)).card ≤ _
  change (G.trim.keep (G.row.nodes r) (G.borderSize r)).card = _ at hx
  change (G.trim.keep (G.column.nodes r) (G.borderSize r)).card = _ at hy
  change (G.row.nodes r).card - (G.trim.keep (G.row.nodes r) (G.borderSize r)).card ≤ _ ∧
    (G.column.nodes r).card - (G.trim.keep (G.column.nodes r) (G.borderSize r)).card ≤ _ at hbound
  rw [hx, hy] at hbound
  rw [Finset.card_sdiff_of_subset (G.trim.subset _ _),
    Finset.card_sdiff_of_subset (G.trim.subset _ _), hx, hy]
  unfold borderSize at *
  omega

/-- The paper's conservative uniform component constants, including balancing
trims, follow from actual finite node geometry. -/
theorem component_bounds (G : BlockGeom) (r L : ℕ) (hL : 0 < L)
    (hC : ∀ i, (G.common.block i).d ∣ L)
    (hX : ∀ i, (G.row.block i).d ∣ L)
    (hY : ∀ i, (G.column.block i).d ∣ L) :
    componentCount (G.geometry r).C L ≤ G.common.componentBudget L ∧
    componentCount ((G.geometry r).C ∪ (G.geometry r).X' ∪ (G.geometry r).Y') L ≤
      G.common.componentBudget L + 2 * (G.row.componentBudget L + G.column.componentBudget L) := by
  refine ⟨G.common.components_le r L hC, ?_⟩
  have hc := G.common.components_le r L hC
  have hx := (components_subset (G.trim.subset (G.row.nodes r) (G.borderSize r)) L).trans
    (Nat.add_le_add_right (G.row.components_le r L hX) _)
  have hy := (components_subset (G.trim.subset (G.column.nodes r) (G.borderSize r)) L).trans
    (Nat.add_le_add_right (G.column.components_le r L hY) _)
  have hu1 := components_union (G.geometry r).C (G.geometry r).X' L
  have hu2 := components_union ((G.geometry r).C ∪ (G.geometry r).X') (G.geometry r).Y' L
  have ht := G.trim_total_bound r
  have hnx := G.row.n_le_budget L hL hX
  have hny := G.column.n_le_budget L hL hY
  change componentCount (G.common.nodes r) L ≤ _ at hc
  change componentCount (G.trim.keep (G.row.nodes r) (G.borderSize r)) L ≤ _ at hx
  change componentCount (G.trim.keep (G.column.nodes r) (G.borderSize r)) L ≤ _ at hy
  change componentCount (G.common.nodes r ∪ G.trim.keep (G.row.nodes r) (G.borderSize r)) L ≤
    componentCount (G.common.nodes r) L +
      componentCount (G.trim.keep (G.row.nodes r) (G.borderSize r)) L at hu1
  change componentCount ((G.common.nodes r ∪ G.trim.keep (G.row.nodes r) (G.borderSize r)) ∪
    G.trim.keep (G.column.nodes r) (G.borderSize r)) L ≤
    componentCount (G.common.nodes r ∪ G.trim.keep (G.row.nodes r) (G.borderSize r)) L +
      componentCount (G.trim.keep (G.column.nodes r) (G.borderSize r)) L at hu2
  change ((G.row.nodes r) \ G.trim.keep _ _).card +
    ((G.column.nodes r) \ G.trim.keep _ _).card ≤ _ at ht
  change componentCount ((G.common.nodes r ∪ G.trim.keep (G.row.nodes r) (G.borderSize r)) ∪
    G.trim.keep (G.column.nodes r) (G.borderSize r)) L ≤ _
  omega

end BlockGeom
end CatalanCore.Uniform



