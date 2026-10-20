module
public import CatalanCore.Arith.Hybrid.CauchyKernelBasis
public import CatalanCore.Arith.Hybrid.CyclicCauchy
public import CatalanCore.Arith.Hybrid.PoleModel
public import CatalanCore.Arith.Hybrid.LoewnerMoment
public import CatalanCore.Arith.Hybrid.ReciprocalExpansion
public import CatalanCore.Linalg.FiniteCauchy
public import CatalanCore.Linalg.WeightedProjection
public import CatalanCore.Linalg.TwoLevelDet
public section

/- These are proved ingredients, not a proof of the non-clean next-Smith law.
The actual weighted-entry identity and free-long-residue geometry are open. -/
#print axioms CatalanCore.Arith.Hybrid.cauchy_residue_basis_unit
#print axioms CatalanCore.Arith.Hybrid.rational_cauchy_kernel_zero
#print axioms CatalanCore.Arith.Hybrid.cyclicPrefix_short_kernel
#print axioms CatalanCore.Arith.Hybrid.good_regularPrefix_difference
#print axioms CatalanCore.Arith.Hybrid.poleScaledEntry_second_order
#print axioms CatalanCore.Arith.Hybrid.poleScaledEntry_transport
#print axioms CatalanCore.Arith.Hybrid.polePrefix_nocut
#print axioms CatalanCore.Arith.Hybrid.poleSquarePrefix_nocut
#print axioms CatalanCore.Arith.Hybrid.cleared_loewner_source_moment
#print axioms CatalanCore.Arith.Hybrid.cleared_loewner_source_extra
#print axioms CatalanCore.Arith.Hybrid.bordered_response_zero
#print axioms CatalanCore.Arith.Hybrid.good_reciprocal_difference
#print axioms CatalanCore.Linalg.complete_cauchy_sum
#print axioms CatalanCore.Linalg.complementary_cauchy_kernel
#print axioms CatalanCore.Linalg.weighted_projection_rank
#print axioms CatalanCore.Linalg.two_level_dvd_det_of_primitive_changes
