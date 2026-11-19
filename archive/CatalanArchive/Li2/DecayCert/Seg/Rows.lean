module
public import CatalanArchive.Li2.DecayCert.Seg.Shift
public import CatalanArchive.Li2.DecayCert.Seg.Fused
public import CatalanArchive.Li2.DecayCert.Seg.Assembly
public import CatalanCore.Li2.DecayCert.Assembly
@[expose] public section
set_option Elab.async false

/-! C-BENT theorem-only public import facade. The canonical analytic rows are
reused, and the new interfaces consume computed results. No bent evaluator,
cell data, lattice data or model-literal equality is introduced here. -/

-- 1 SP; 2 derivative; 3 SC.
#check CatalanCore.Li2.DecayCert.segPot_closed
#check CatalanCore.Li2.DecayCert.segPot_closed_own
#check CatalanCore.Li2.DecayCert.segPot_hasDerivAt
#check CatalanCore.Li2.DecayCert.ySeries_rec
#check CatalanCore.Li2.DecayCert.segSeries_coeff
-- 4 computed Int Horner; 5 CT; 6 OW; 7 HE.
#check CatalanCore.Li2.DecayCert.Seg.taylorShiftF_computed_spec
#check CatalanCore.Li2.DecayCert.Seg.taylorShiftCF_computed_spec
#check CatalanCore.Li2.DecayCert.cauchyDisc_cell
#check CatalanCore.Li2.DecayCert.Seg.ownPoly_computed_spec
#check CatalanCore.Li2.DecayCert.holder_end_cell
-- 8 AC; 9 computed range; 10 V; 11 mass; 12 IU.
#check CatalanCore.Li2.DecayCert.fre_taylor_remainder
#check CatalanCore.Li2.DecayCert.Seg.computed_range_checked
#check CatalanCore.Li2.DecayCert.Vint_closed
#check CatalanCore.Li2.DecayCert.sigmaCell_mass
#check CatalanCore.Li2.DecayCert.energy_up_integral_lower
-- 13 LC'; 14 Dsum; 15 PF; 16 computed C1; 17 ZL; 18 reuse only.
#check CatalanCore.Li2.DecayCert.Seg.lineCell_of_eval
#check CatalanCore.Li2.DecayCert.Dsum_spec
#check CatalanCore.Li2.DecayCert.dens_pos_bernstein
#check CatalanCore.Li2.DecayCert.atomCapCheck_bound
#check CatalanCore.Li2.DecayCert.Seg.cellC1_of_eval
#check CatalanCore.Li2.DecayCert.Seg.bent_certificate_of_eval
#check CatalanCore.Li2.DecayCert.bentSegCert_D_ge
#check CatalanCore.Li2.DecayCert.latticeCover_D_ge
-- Rational Joukowski re-centering reused unchanged.
#check CatalanCore.Li2.DecayCert.rationalJoukowski_recenter

#print axioms CatalanCore.Li2.DecayCert.segPot_closed
#print axioms CatalanCore.Li2.DecayCert.segPot_hasDerivAt
#print axioms CatalanCore.Li2.DecayCert.ySeries_rec
#print axioms CatalanCore.Li2.DecayCert.segSeries_coeff
#print axioms CatalanCore.Li2.DecayCert.Seg.taylorShiftCF_computed_spec
#print axioms CatalanCore.Li2.DecayCert.cauchyDisc_cell
#print axioms CatalanCore.Li2.DecayCert.Seg.ownPoly_computed_spec
#print axioms CatalanCore.Li2.DecayCert.holder_end_cell
#print axioms CatalanCore.Li2.DecayCert.fre_taylor_remainder
#print axioms CatalanCore.Li2.DecayCert.Seg.computed_range_checked
#print axioms CatalanCore.Li2.DecayCert.Vint_closed
#print axioms CatalanCore.Li2.DecayCert.sigmaCell_mass
#print axioms CatalanCore.Li2.DecayCert.energy_up_integral_lower
#print axioms CatalanCore.Li2.DecayCert.Seg.lineCell_of_eval
#print axioms CatalanCore.Li2.DecayCert.Dsum_spec
#print axioms CatalanCore.Li2.DecayCert.dens_pos_bernstein
#print axioms CatalanCore.Li2.DecayCert.atomCapCheck_bound
#print axioms CatalanCore.Li2.DecayCert.Seg.cellC1_of_eval
#print axioms CatalanCore.Li2.DecayCert.Seg.bent_certificate_of_eval
#print axioms CatalanCore.Li2.DecayCert.latticeCover_D_ge
#print axioms CatalanCore.Li2.DecayCert.rationalJoukowski_recenter
