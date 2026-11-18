module
public import CatalanCore.Li2.DecayCert.Lattice.CellPenalty
public import CatalanCore.Li2.DecayCert.Lattice.Energy
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem latticeSetupCheck_parts (z : ℚ) (d : LatticeInput) (c : LatticeSetup)
    (hc : latticeSetupCheck z d c=true) :
    (0 < |z| ∧ |z| < 1 ∧ 1≤c.cutoff ∧ d.Y≤c.cutoff) ∧
    latticeShapeCheck d=true ∧ datumCheck d.data c.density=true ∧
    chainCheck 0 d.Y (c.supportCells.map (fun x => ⟨x.left,x.right⟩))=true ∧
    (∀ x∈c.supportCells,cellUBF (fullLatticeCell z d x) x.witness=true) ∧
    chainCheck d.Y c.cutoff (c.rightCells.map (fun x => ⟨x.left,x.right⟩))=true ∧
    (∀ x∈c.rightCells,rightCellCheck z d x=true) ∧
    scalarUpperCheck (latticeTailExpr z d c) c.theta=true ∧
    scalarUpperCheck (seAdd (seRat (3/(c.cutoff+1))) (.log c.terms |z|)) 0=true ∧
    ∃ e,latticeEnergyExpr d c.energy=some e ∧ scalarUpperCheck e c.Iup=true := by
  simp only [latticeSetupCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha,hb⟩,hd⟩,hl⟩,hcl⟩,hr⟩,hcr⟩,ht⟩,hs⟩,he⟩
  refine ⟨ha,hb,hd,hl,hcl,hr,hcr,ht,hs,?_⟩
  cases hE : latticeEnergyExpr d c.energy with
  | none => simp only [hE,Bool.false_eq_true] at he
  | some e => exact ⟨e,rfl,by simpa only [hE] using he⟩

theorem latticeSetupCheck_sound (z : ℚ) (d : LatticeInput) (c : LatticeSetup)
    (hc : latticeSetupCheck z d c=true) :
    I d.data.dual.σ ≤ (c.Iup:ℝ) ∧
    (∫ x in Ici (0:ℝ),pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(c.theta:ℝ))) ≤ (latticePW d c:ℝ) := by
  rcases latticeSetupCheck_parts z d c hc with ⟨ha,hshape,hd,hl,hcl,hr,hcr,ht,hs,he⟩
  have hz : z≠0 := by intro h; simp [h] at ha
  have hf : Continuous (fun x : ℝ => pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(c.theta:ℝ))) :=
    ((continuous_W_real _ _).sub continuous_const).max continuous_const
  have hlb := chainCheck_sound 0 d.Y _ hl
  have hleft := chainCheck_cells_integral_bound 0 d.Y c.supportCells (fun x => ⟨x.left,x.right⟩) hl _ hf
    (fun x => penaltyBoundQ x.scale x.witness (x.right-x.left) c.theta) (by
      intro x hx
      have hb := hlb.2.2.1 ⟨x.left,x.right⟩ (List.mem_map.mpr ⟨x,hx,rfl⟩)
      exact fullLatticeCell_penalty z hz d c.density hd x c.theta hb.1 hb.2.1.le (hcl x hx))
  have hright := chainCheck_cells_integral_bound d.Y c.cutoff c.rightCells (fun x => ⟨x.left,x.right⟩) hr _ hf
    (fun x => penaltyBoundQ x.scale x.witness (x.right-x.left) c.theta) (by
      intro x hx
      exact rightCell_penalty z hz d c.density hd hshape x c.theta (hcr x hx))
  have hC : (0:ℝ)≤(c.cutoff:ℝ) := by exact_mod_cast (show (0:ℚ)≤c.cutoff by linarith [ha.2.2.1])
  have hzero : ∀ x : ℝ,(c.cutoff:ℝ)≤x → pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(c.theta:ℝ))=0 := by
    intro x hx
    exact max_eq_right (sub_nonpos.mpr (latticeTail_checked z d c hd ha.2.2.1 ht hs x hx))
  refine ⟨?_,?_⟩
  · rcases he with ⟨e,hE,hcap⟩
    exact (latticeEnergyExpr_upper d c.density hd hshape c.energy e hE).trans (scalarUpperCheck_sound _ _ hcap)
  · rw [integral_Ici_of_zero_tail _ _ hC hzero]
    have hsum := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable (0:ℝ) (d.Y:ℝ)) (hf.intervalIntegrable (d.Y:ℝ) (c.cutoff:ℝ))
    rw [← hsum]
    have hb := add_le_add hleft hright
    simpa only [latticePW,Rat.cast_add,Rat.cast_zero] using hb
#print axioms latticeSetupCheck_sound
end
end CatalanCore.Li2.DecayCert
