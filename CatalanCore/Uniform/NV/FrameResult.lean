module
public import CatalanCore.Uniform.NV.FrameStep
public import CatalanCore.Uniform.NV.Visibility
@[expose] public section
open Polynomial Finset Matrix Module
namespace CatalanCore.Uniform.NV

/-- Every merged nonzero rational frame has the full step-component corank bound.
All scalar source identities and pole obstructions are constructed from Fr. -/
theorem frame_step_component_corank (Fr : Frame) (U : ℚ) (G : NodeGeometry (K := ℚ))
    (L c m : ℕ) (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z) (hC : C.card = c) (hZ : Z.card = c+2*m)
    (hunion : G.rows ∪ G.cols = fieldNodes Z) (hinter : G.rows ∩ G.cols = fieldNodes C)
    (hrows : G.rows.card = c+m) (hn : 1 ≤ c+m) :
    finrank ℚ (LinearMap.ker (G.matrix (onNaturals (framePrefix Fr))
      (onNaturals (frameJet Fr U))).mulVecLin) ≤
      (Fr.d*L+componentCount Z L+componentCount C L-2)/2 := by
  obtain ⟨a,ha⟩ := framePoleSet_nonempty Fr L hd hL
  have hpole := frame_pole_certificate Fr L hL hw a ha
  have hdeg := frame_pole_degrees Fr L
  exact step_component_corank G L (Fr.d*L) c m _ _ _ _ (frameStepData Fr U L) a hpole
    (frame_pole_count_ge_two Fr L hd hL hw) hdeg.1.le hdeg.2
    Z C hCZ hC hZ hunion hinter hrows hn

/-- The finite step-component nonvanishing theorem for every rational frame,
including deletion size equal to the actual corank. -/
theorem frame_step_component_nv_exact (Fr : Frame) (U : ℚ) (G : NodeGeometry (K := ℚ))
    (L c m : ℕ) (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z) (hC : C.card = c) (hZ : Z.card = c+2*m)
    (hunion : G.rows ∪ G.cols = fieldNodes Z) (hinter : G.rows ∩ G.cols = fieldNodes C)
    (hrows : G.rows.card = c+m) (hn : 1 ≤ c+m)
    (hvis : componentCount Z L+Fr.d*L ≤ c+3) :
    ∃ s : Finset (G.rows ∩ G.cols : Finset ℚ),
      s.card = finrank ℚ (LinearMap.ker (G.matrix (onNaturals (framePrefix Fr))
        (onNaturals (frameJet Fr U))).mulVecLin) ∧
      s.card ≤ (Fr.d*L+componentCount Z L+componentCount C L-2)/2 ∧
      ((G.matrix (onNaturals (framePrefix Fr)) (onNaturals (frameJet Fr U))).submatrix
        (Subtype.val : {i // i ∉ s.image G.common} → G.rows) Subtype.val).det ≠ 0 := by
  obtain ⟨a,ha⟩ := framePoleSet_nonempty Fr L hd hL
  have hpole := frame_pole_certificate Fr L hL hw a ha
  have hdeg := frame_pole_degrees Fr L
  have hE := commonEval_injective G L (Fr.d*L) c m _ _ _ _ (frameStepData Fr U L) a hpole
    (frame_pole_count_ge_two Fr L hd hL hw) hdeg.1.le hdeg.2
    Z C hCZ hC hZ hunion hinter hrows hn hvis
  obtain ⟨s,hs,hdet⟩ := common_deletion_exact G (onNaturals (framePrefix Fr))
    (onNaturals (frameJet Fr U)) (by omega) hE
  refine ⟨s,hs,?_,hdet⟩
  rw [hs]
  exact frame_step_component_corank Fr U G L c m hL hd hw Z C hCZ hC hZ hunion hinter hrows hn

/-- Convenient bound-only form for finite-family assembly. -/
theorem frame_step_component_nv (Fr : Frame) (U : ℚ) (G : NodeGeometry (K := ℚ))
    (L c m : ℕ) (hL : 1 ≤ L) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z) (hC : C.card = c) (hZ : Z.card = c+2*m)
    (hunion : G.rows ∪ G.cols = fieldNodes Z) (hinter : G.rows ∩ G.cols = fieldNodes C)
    (hrows : G.rows.card = c+m) (hn : 1 ≤ c+m)
    (hvis : componentCount Z L+Fr.d*L ≤ c+3) :
    ∃ s : Finset (G.rows ∩ G.cols : Finset ℚ),
      s.card ≤ (Fr.d*L+componentCount Z L+componentCount C L-2)/2 ∧
      ((G.matrix (onNaturals (framePrefix Fr)) (onNaturals (frameJet Fr U))).submatrix
        (Subtype.val : {i // i ∉ s.image G.common} → G.rows) Subtype.val).det ≠ 0 := by
  obtain ⟨s,_,hb,hdet⟩ := frame_step_component_nv_exact Fr U G L c m hL hd hw
    Z C hCZ hC hZ hunion hinter hrows hn hvis
  exact ⟨s,hb,hdet⟩

#print axioms frame_step_component_corank
#print axioms frame_step_component_nv_exact
end CatalanCore.Uniform.NV
