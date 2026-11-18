module
public import CatalanCore.Li2.DecayCert.Lattice.Setup
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem latticeCheck_parts (z : ℚ) (d : LatticeInput) (c : LatticeSetup) (p : LatticeCert)
    (hp : latticeCheck z d c p=true) :
    0<p.rho ∧ chainCheck 1 4 (p.atomCells.map (fun x => ⟨x.left,x.right⟩))=true ∧
    (∀ x∈p.atomCells,cellUBF (latticeAtomCell z d x) x.witness=true) ∧
    scalarLowerCheck p.lower (seSum [seScale (-12) (.log c.terms 2),
      seRat (-4-c.Iup-2*c.theta-2*latticePW d c-latticePA d c p)])=true := by
  simp only [latticeCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hp
  rcases hp with ⟨⟨⟨hr,hc⟩,ha⟩,he⟩
  exact ⟨hr,hc,ha,he⟩

theorem latticePA_upper (z : ℚ) (d : LatticeInput) (c : LatticeSetup) (p : LatticeCert)
    (hsetup : latticeSetupCheck z d c=true) (hp : latticeCheck z d c p=true) :
    atomPenalty (z:ℝ) (p.rho:ℝ) d.data.dual.σ (c.theta:ℝ)≤(latticePA d c p:ℝ) := by
  rcases latticeSetupCheck_parts z d c hsetup with ⟨ha,hshape,hd,hl,hcl,hr,hcr,ht,hs,he⟩
  rcases latticeCheck_parts z d c p hp with ⟨hrho,hchain,hcells,hscalar⟩
  have hz : z≠0 := by intro h; simp [h] at ha
  have hf : Continuous (fun x => pos (A (z:ℝ) (p.rho:ℝ) d.data.dual.σ x-(c.theta:ℝ))) :=
    ((continuous_A_real _ _ _).sub continuous_const).max continuous_const
  have hb := chainCheck_sound 1 4 _ hchain
  have hI := chainCheck_cells_integral_bound 1 4 p.atomCells (fun x => ⟨x.left,x.right⟩) hchain _ hf
    (fun x => penaltyBoundQ x.scale x.witness (x.right-x.left) (p.rho+c.theta)) (by
      intro x hx
      have hbx := hb.2.2.1 ⟨x.left,x.right⟩ (List.mem_map.mpr ⟨x,hx,rfl⟩)
      have hi := latticeAtomCell_penalty z hz d c.density hd x (p.rho+c.theta) hbx.1 hbx.2.2 hbx.2.1.le (hcells x hx)
      have heq : (fun s : ℝ => pos (A (z:ℝ) (p.rho:ℝ) d.data.dual.σ s-(c.theta:ℝ)))=
          fun s => pos (omega (z:ℝ) s-2*U d.data.dual.σ (-(s:ℂ))-((p.rho+c.theta:ℚ):ℝ)) := by
        funext s
        congr 1
        simp only [A,Rat.cast_add]
        ring
      rw [heq]
      exact hi)
  simpa only [atomPenalty,latticePA,Rat.cast_one,Rat.cast_ofNat] using hI

theorem latticeCert_D_ge (z : ℚ) (d : LatticeInput) (c : LatticeSetup) (p : LatticeCert)
    (hsetup : latticeSetupCheck z d c=true) (hp : latticeCheck z d c p=true) :
    (p.lower:ℝ)≤ -(12*Real.log 2+4)-I d.data.dual.σ-2*(c.theta:ℝ)-
      2*(∫ x in Ici (0:ℝ),pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(c.theta:ℝ)))-
        atomPenalty (z:ℝ) (p.rho:ℝ) d.data.dual.σ (c.theta:ℝ) := by
  have hparts := latticeCheck_parts z d c p hp
  have hl := scalarLowerCheck_sound _ _ hparts.2.2.2
  simp only [seSum_value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    seScale_value,ScalarExpr.value,seRat_value,Rat.cast_neg,Rat.cast_ofNat] at hl
  push_cast at hl
  have hI := latticeSetupCheck_sound z d c hsetup
  have hA := latticePA_upper z d c p hsetup hp
  linarith

theorem latticeCover_D_ge (z : ℚ) (d : LatticeInput) (c : LatticeSetup) (p : LatticeCoverCert)
    (hsetup : latticeSetupCheck z d c=true) (hp : latticeCoverCheck z d c p=true) :
    ∀ q∈p.pairs,(0:ℚ)<q.rho ∧
      (q.lower:ℝ)≤ -(12*Real.log 2+4)-I d.data.dual.σ-2*(c.theta:ℝ)-
        2*(∫ x in Ici (0:ℝ),pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(c.theta:ℝ)))-
          atomPenalty (z:ℝ) (q.rho:ℝ) d.data.dual.σ (c.theta:ℝ) := by
  intro q hq
  have hc : latticeCheck z d c q=true := List.all_eq_true.mp hp q hq
  exact ⟨(latticeCheck_parts z d c q hc).1,latticeCert_D_ge z d c q hsetup hc⟩
#print axioms latticePA_upper
#print axioms latticeCert_D_ge
#print axioms latticeCover_D_ge
end
end CatalanCore.Li2.DecayCert
