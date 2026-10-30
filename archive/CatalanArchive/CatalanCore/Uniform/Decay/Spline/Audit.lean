module

public import CatalanCore.Uniform.Decay.Spline.Final
public import CatalanCore.Uniform.Decay.Spline.Mesh
public import CatalanCore.Uniform.Decay.Spline.Bridge
public import CatalanCore.Uniform.Decay.Spline.EnergySigned
public import CatalanCore.Uniform.Decay.Spline.UnuReal
public import CatalanCore.Uniform.Decay.Spline.PolyDensity

/-! Axiom audit for lane D, package D2 (`Uniform/Decay/Spline`). -/

#print axioms CatalanCore.Decay.Usig_ge_signed
#print axioms CatalanCore.Decay.pt_ineqWS
#print axioms CatalanCore.Decay.energy_rectWS
#print axioms CatalanCore.Decay.sum_abs_le_one_of_nonneg
#print axioms CatalanCore.SignedChain.decay_coreW
#print axioms CatalanCore.SignedChain.decay_of_certG_rect_slope
#print axioms CatalanCore.SignedChain.hasDecay_commonMinorFam
#print axioms CatalanCore.SignedChain.HybridDecayDataS.hybridDecay
#print axioms CatalanCore.SignedChain.HybridDecayDataS.membersDecay
#print axioms CatalanCore.SignedChain.HybridDecayDataS.pairDecay
#print axioms CatalanCore.SignedChain.HybridDecayDataS.commonMinorDecay
#print axioms CatalanCore.Uniform.Decay.Spline.integral_phiM_le
#print axioms CatalanCore.Uniform.Decay.Spline.piece_smooth
#print axioms CatalanCore.Uniform.Decay.Spline.smooth_err
#print axioms CatalanCore.Uniform.Decay.Spline.energy_smooth_err
#print axioms CatalanCore.Uniform.Decay.Spline.midpoint_err
#print axioms CatalanCore.Uniform.Decay.Spline.usig_atom_err
#print axioms CatalanCore.Uniform.Decay.Spline.energy_atom_err
#print axioms CatalanCore.Uniform.Decay.Spline.etaN_le_mesh
#print axioms CatalanCore.Uniform.Decay.Spline.energy_atom_err_mesh
#print axioms CatalanCore.Uniform.Decay.Spline.exists_seg_cover
#print axioms CatalanCore.Uniform.Decay.Spline.continuousOn_Unu_real
#print axioms CatalanCore.Uniform.Decay.Spline.exists_certCoreGs
#print axioms CatalanCore.Uniform.Decay.Spline.exists_certCoreGs_main
#print axioms CatalanCore.Uniform.Decay.Spline.exists_certCoreGs_poly
#print axioms CatalanCore.Uniform.Decay.Spline.exists_hybridDecayDataS
#print axioms CatalanCore.Uniform.Decay.Spline.Vp_le_sum
#print axioms CatalanCore.Uniform.Decay.Spline.ratPoly_abs_le
#print axioms CatalanCore.Uniform.Decay.Spline.integral_ratPoly
