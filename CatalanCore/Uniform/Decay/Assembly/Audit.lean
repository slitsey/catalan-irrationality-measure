import CatalanCore.Uniform.Decay.Assembly.LogModulus
import CatalanCore.Uniform.Decay.Assembly.LogModulusAbs
import CatalanCore.Uniform.Decay.Assembly.SegmentModulus
import CatalanCore.Uniform.Decay.Assembly.GlobalModulus
import CatalanCore.Uniform.Decay.Assembly.Normalize
import CatalanCore.Uniform.Decay.Assembly.Absorb
import CatalanCore.Uniform.Decay.Assembly.CornerPD

open CatalanCore.Uniform.Decay.Assembly
open CatalanCore.Uniform

#print axioms log_diff_far
#print axioms log_diff_near
#print axioms far_right
#print axioms far_left
#print axioms integral_abs_log_diff_le
#print axioms segment_abs_log_diff_le
#print axioms segment_log_modulus
#print axioms segment_log_modulus_paper
#print axioms U0_modulus_signed
#print axioms U0_sub_Urho_nonneg
#print axioms U0_modulus
#print axioms g_modulus
#print axioms Omega_g
#print axioms physPts_eq_scaled
#print axioms hShift_abs_le
#print axioms polygonRep_scaled
#print axioms growth_const_le
#print axioms xstar_div
#print axioms eventually_rlog_le
#print axioms NodeFamily.hasAllMinorDecay_of_bound
#print axioms NodeFamily.HasAllMinorDecay.mono
#print axioms BlockGeom.hasScaledDecay_of_energy_bound
#print axioms edge_vanish
#print axioms PD.Lq_bound
#print axioms tendsto_lower
#print axioms tendsto_G
#print axioms boundary_energy_corner
#print axioms PD.of_posdef
#print axioms boundary_energy_corner_posdef
