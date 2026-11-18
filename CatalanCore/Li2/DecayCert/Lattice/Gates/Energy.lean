module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Energy.Tables
public import CatalanCore.Li2.DecayCert.Lattice.Energy
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.LatticeGate
open CatalanCore.Li2.Decay

theorem energyTableCheck_I_upper (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (hshape : latticeShapeCheck d=true)
    (w : LatticeEnergyWitness) (S : ℤ) (mu sm : List ℚ) (upper : List ℤ) (cap : ℚ)
    (hc : energyTableCheck d w S mu sm upper cap=true) :
    I d.data.dual.σ ≤ (cap:ℝ) := by
  obtain ⟨e,he,hu⟩ := energyTableCheck_sound d w S mu sm upper cap hc
  exact (latticeEnergyExpr_upper d dw hd hshape w e he).trans hu
#print axioms energyTableCheck_I_upper
end CatalanCore.Li2.DecayCert.LatticeGate
