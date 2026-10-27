module
public import CatalanCore.Uniform.Frame.NVTransport
public import CatalanCore.Uniform.Frame.Components
public import CatalanCore.Uniform.Frame.Threshold
public import CatalanCore.Uniform.NV.FrameResult
@[expose] public section

namespace CatalanCore.Uniform.NVAdapter
open Finset Matrix Module

/-- The actual finite frame pencil has the full step-component corank bound,
without a visibility hypothesis. -/
theorem finite_corank_of_nonempty (Fr : Frame) (U : ℚ) (G : Rect.Geometry)
    (L : ℕ) (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hn : 1 ≤ G.C.card + G.k) :
    finrank ℚ (LinearMap.ker
      (Rect.FullN Fr (fun a : G.C => (a : ℕ)) G.xs G.ys U).mulVecLin) ≤
      (Fr.d * L + NV.componentCount (G.C ∪ G.X' ∪ G.Y') L +
        NV.componentCount G.C L - 2) / 2 := by
  have h := NV.frame_step_component_corank Fr U (model G)
    L G.C.card G.k hL hd hw (G.C ∪ G.X' ∪ G.Y') G.C
    (fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _ ha)) rfl
    (full_nodes_card G) (model_union G) (model_inter G) (model_rows_card G) hn
  rw [corank_model] at h
  exact h
/-- The exact finite common-deletion theorem on the actual frame pencil,
including deletion size equal to its actual corank. -/
theorem finite_common_deletion_exact_of_nonempty (Fr : Frame) (U : ℚ) (G : Rect.Geometry)
    (L : ℕ) (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hn : 1 ≤ G.C.card + G.k)
    (hvis : NV.componentCount (G.C ∪ G.X' ∪ G.Y') L + Fr.d * L ≤ G.C.card + 3) :
    ∃ S : Finset G.C,
      G.C.card - S.card = finrank ℚ (LinearMap.ker
        (Rect.FullN Fr (fun a : G.C => (a : ℕ)) G.xs G.ys U).mulVecLin) ∧
      G.C.card - S.card ≤ (Fr.d * L + NV.componentCount (G.C ∪ G.X' ∪ G.Y') L +
        NV.componentCount G.C L - 2) / 2 ∧
      (Rect.FullN Fr (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys U).det ≠ 0 := by
  obtain ⟨s,hs,hbound,hdet⟩ := NV.frame_step_component_nv_exact Fr U (model G)
    L G.C.card G.k hL hd hw (G.C ∪ G.X' ∪ G.Y') G.C
    (fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _ ha)) rfl
    (full_nodes_card G) (model_union G) (model_inter G) (model_rows_card G) hn hvis
  obtain ⟨S,hcard,hS⟩ := retained_of_model_deletion Fr U G s hdet
  refine ⟨S,?_,?_,hS⟩
  · rw [hcard,hs,corank_model]
  · rw [hcard]
    exact hbound

private theorem empty_corank {I : Type} [Fintype I] [DecidableEq I] [IsEmpty I]
    (M : Matrix I I ℚ) : finrank ℚ (LinearMap.ker M.mulVecLin) = 0 := by
  have h := Submodule.finrank_le (LinearMap.ker M.mulVecLin)
  have hdim : finrank ℚ (I → ℚ) = 0 := by simp
  omega

/-- The actual corank theorem also includes the empty determinant convention. -/
theorem finite_corank (Fr : Frame) (U : ℚ) (G : Rect.Geometry)
    (L : ℕ) (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) :
    finrank ℚ (LinearMap.ker
      (Rect.FullN Fr (fun a : G.C => (a : ℕ)) G.xs G.ys U).mulVecLin) ≤
      (Fr.d * L + NV.componentCount (G.C ∪ G.X' ∪ G.Y') L +
        NV.componentCount G.C L - 2) / 2 := by
  by_cases hn : 1 ≤ G.C.card + G.k
  · exact finite_corank_of_nonempty Fr U G L hL hd hw hn
  · have hc : G.C.card = 0 := by omega
    have hk : G.k = 0 := by omega
    letI : IsEmpty G.C := Fintype.card_eq_zero_iff.mp (by simpa using hc)
    letI : IsEmpty (Fin G.k) := Fintype.card_eq_zero_iff.mp (by simpa using hk)
    rw [empty_corank]
    exact Nat.zero_le _

/-- Finite selection in the complete paper domain, with empty determinant 1. -/
theorem finite_common_deletion_exact (Fr : Frame) (U : ℚ) (G : Rect.Geometry)
    (L : ℕ) (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hvis : NV.componentCount (G.C ∪ G.X' ∪ G.Y') L + Fr.d * L ≤ G.C.card + 3) :
    ∃ S : Finset G.C,
      G.C.card - S.card = finrank ℚ (LinearMap.ker
        (Rect.FullN Fr (fun a : G.C => (a : ℕ)) G.xs G.ys U).mulVecLin) ∧
      G.C.card - S.card ≤ (Fr.d * L + NV.componentCount (G.C ∪ G.X' ∪ G.Y') L +
        NV.componentCount G.C L - 2) / 2 ∧
      (Rect.FullN Fr (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys U).det ≠ 0 := by
  by_cases hn : 1 ≤ G.C.card + G.k
  · exact finite_common_deletion_exact_of_nonempty Fr U G L hL hd hw hn hvis
  · have hc : G.C.card = 0 := by omega
    have hk : G.k = 0 := by omega
    letI : IsEmpty G.C := Fintype.card_eq_zero_iff.mp (by simpa using hc)
    letI : IsEmpty (Fin G.k) := Fintype.card_eq_zero_iff.mp (by simpa using hk)
    refine ⟨univ,?_,?_,?_⟩
    · simp only [Finset.card_univ,Fintype.card_coe,Nat.sub_self]
      exact (empty_corank _).symm
    · simp only [Finset.card_univ,Fintype.card_coe,Nat.sub_self]
      exact Nat.zero_le _
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero

end CatalanCore.Uniform.NVAdapter

namespace CatalanCore.Uniform.BlockGeom
open Finset

/-- Conservative exact fixed step-component constants. -/
def commonComponents (G : BlockGeom) (L : ℕ) : ℕ := G.common.componentBudget L
def allComponents (G : BlockGeom) (L : ℕ) : ℕ :=
  G.common.componentBudget L + 2 * (G.row.componentBudget L + G.column.componentBudget L)
def selectionDepth (G : BlockGeom) (Fr : Frame) (L : ℕ) : ℕ :=
  (Fr.d * L + G.allComponents L + G.commonComponents L - 2) / 2

def selectionThreshold (G : BlockGeom) (Fr : Frame) (L : ℕ) : ℕ :=
  G.visibilityThreshold (max 1 (G.allComponents L + Fr.d * L - 3))

/-- Full periodic-block characteristic-zero selector for the actual family.
The theorem proves the source, component, visibility and determinant adapters;
no nonvanishing provider is assumed. Every fixed-depth family containing the
proved depth is allowed. -/
theorem hasNV0 (G : BlockGeom) (Fr : Frame) (L depth : ℕ)
    (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (hC : ∀ i, (G.common.block i).d ∣ L)
    (hX : ∀ i, (G.row.block i).d ∣ L)
    (hY : ∀ i, (G.column.block i).d ∣ L)
    (hdepth : G.selectionDepth Fr L ≤ depth) :
    HasNV0 (G.family Fr depth) G.scale := by
  apply NodeFamily.hasNV0_of_minors Fr G.geometry depth (G.selectionThreshold Fr L)
  intro r hr U
  have hvisible := G.common_ge_of_threshold
    (max 1 (G.allComponents L + Fr.d * L - 3)) r hr
  obtain ⟨hcommon,hall⟩ := G.component_bounds r L (by omega) hC hX hY
  have hpos : 1 ≤ (G.geometry r).C.card + (G.geometry r).k := by omega
  have hvis : NV.componentCount ((G.geometry r).C ∪ (G.geometry r).X' ∪ (G.geometry r).Y') L +
      Fr.d * L ≤ (G.geometry r).C.card + 3 := by
    change NV.componentCount _ L ≤ G.allComponents L at hall
    omega
  obtain ⟨S,hcard,hbound,hdet⟩ := NVAdapter.finite_common_deletion_exact_of_nonempty
    Fr U (G.geometry r) L hL hd hw hpos hvis
  refine ⟨S,?_,hdet⟩
  apply hbound.trans
  apply le_trans _ hdepth
  change NV.componentCount _ L ≤ G.commonComponents L at hcommon
  change NV.componentCount _ L ≤ G.allComponents L at hall
  change (Fr.d * L + NV.componentCount _ L + NV.componentCount _ L - 2) / 2 ≤
    (Fr.d * L + G.allComponents L + G.commonComponents L - 2) / 2
  omega

#print axioms hasNV0
end CatalanCore.Uniform.BlockGeom




