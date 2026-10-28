import CatalanCore.Uniform.Decay.PolyChain.CheckMain

/-!
Axiom audit for lane D, package D7 (`Uniform/Decay/PolyChain`), plus an exact check that the
sevenths polygon of `hyp.py` passes the Boolean admissibility test `okB` of `checkP`.
-/

open CatalanCore.Uniform.Decay.Polygon

namespace CatalanCore.Uniform.Decay.PolyChain.AuditD7

/-- The sevenths polygon (`hyp.py`, same data as D4's audit). -/
def sevenths : RatPolygon where
  r0 := 273 / 2000
  verts := [(-8809027 / 50000000, 787 / 10000), (-11253987 / 50000000, 1041 / 5000)]
  s := 5000 / 1353

theorem sevenths_okB : sevenths.okB = true := by decide +kernel

end CatalanCore.Uniform.Decay.PolyChain.AuditD7

#print axioms CatalanCore.Uniform.Decay.PolyChain.norm_polyW_le_vq
#print axioms CatalanCore.Uniform.Decay.PolyChain.log_qP_le
#print axioms CatalanCore.Uniform.Decay.PolyChain.integral_vP_le
#print axioms CatalanCore.Uniform.Decay.PolyChain.integrand_le_poly
#print axioms CatalanCore.Uniform.Decay.PolyChain.det_bound_poly
#print axioms CatalanCore.Uniform.Decay.PolyChain.theoremN_poly
#print axioms CatalanCore.Uniform.Decay.Nodes.energy_block_d
#print axioms CatalanCore.Uniform.BlockGeom.ps_hyp_d
#print axioms CatalanCore.Uniform.BlockGeom.energy_geom_d
#print axioms CatalanCore.Uniform.BlockGeom.energy_geom_small_d
#print axioms CatalanCore.Uniform.Decay.PolyChain.pathPt_affine
#print axioms CatalanCore.Uniform.Decay.PolyChain.scaled_upper
#print axioms CatalanCore.Uniform.Decay.PolyChain.g_ge_poly
#print axioms CatalanCore.Uniform.Decay.PolyChain.lemmaBG_gen
#print axioms CatalanCore.Uniform.Decay.PolyChain.poly_dist
#print axioms CatalanCore.Uniform.Decay.PolyChain.poly_norm
#print axioms CatalanCore.Uniform.Decay.PolyChain.poly_atom_or_ge
#print axioms CatalanCore.Uniform.Decay.PolyChain.hasAllMinorDecay_of_certG_poly
#print axioms CatalanCore.Uniform.Decay.PolyChain.exists_certCoreGsNuP
#print axioms CatalanCore.Uniform.Decay.Polygon.RatPolygon.okB_sound
#print axioms CatalanCore.Uniform.Decay.Cert.SplineData.checkP_sound
#print axioms CatalanCore.Uniform.Decay.PolyChain.hasScaledDecay_of_check_poly
#print axioms CatalanCore.Uniform.Decay.PolyChain.AuditD7.sevenths_okB
#print axioms CatalanCore.Uniform.Decay.Cert.SplineData.basicOkP_sound
