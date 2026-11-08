module

public import CatalanMeasure.GenD.Signed.RouteI.GasEnergy

@[expose] public section

/-!
# Kernel checks of the gas energies of `capSource`
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem pts_okP : ptsPos.all (fun u => ptOK u.1.natAbs) = true := by decide +kernel
-- kcost: 1 s measured with the next three, 6 Nov
theorem pts_okN : ptsNeg.all (fun u => ptOK u.1.natAbs) = true := by decide +kernel
-- kcost: as above
theorem tv_up : tvD Up * (PN * 12 ^ 256) < 2 ^ DW := by decide +kernel
-- kcost: as above
theorem tv_un : tvD Un * (PN * 12 ^ 256) < 2 ^ DW := by decide +kernel
-- kcost: as above

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem tv_bd : tvOf (ptsOf LPq) ≤ 8175 * 2 ^ 72 ∧ tvOf (ptsOf LNq) ≤ 2069544 * 2 ^ 72 ∧
    tvOf (ptsOf LCq) ≤ 5402 * 2 ^ 72 ∧ tvOf (ptsOf LDq) ≤ 5402 * 2 ^ 72 := by decide +kernel
-- kcost: 6 s measured with the small boxes, 6 Nov
theorem lens : gasPosT.length = 427 ∧ gasNegT.length = 277 ∧ col0.length = 628 := by decide +kernel
-- kcost: as above
theorem sums_eq : PsumZ paT = sumP paT ∧ PsumZ naT = sumP naT := by decide +kernel
-- kcost: as above
theorem box_scal : qBox (sumP gasPosT) (sumP row0) 63489562168082 = true ∧
    qBox (sumP gasNegT) (sumP row0) 36510437831917 = true ∧
    qBox cPn (sumP row0) 36510437831917 = true ∧
    qBox cNn (58 * sumP row0) 54868872512909 = true ∧
    qBox (cPn ^ 2 * SminZ paT) (cPd ^ 2 * 10 ^ 17) 6880564215755 = true ∧
    qBox (cNn ^ 2 * SmaxZ naT) (cNd ^ 2 * 10 ^ 17) 43657136919364 = true ∧
    qBox (cNn * SlinZ naT) (cNd * 10 ^ 17) 53351287497253 = true ∧
    qBox L2c (2 ^ 96) 69314718055994 = true := by decide +kernel
-- kcost: as above
theorem box_tail : ballBox tailB 1 1 788755782 2 = true ∧ 0 < (Bl.sub (Bl.ofZ 1) qB).1 ∧
    2 * (Bl.sub (Bl.ofZ 1) qB).2 ≤ (Bl.sub (Bl.ofZ 1) qB).1.toNat := by decide +kernel
-- kcost: as above

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem box_pos : boxPos (-853339519085) (-39541675682036) 23239004899126 (-3944317782559) 2 = true := by
  decide +kernel
-- kcost: 58 s measured, 8.3 GB, 6 Nov

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem box_neg : boxNeg 1357201154220 29512640381580 (-5869925662132) 2 = true := by decide +kernel
-- kcost: 56 s measured, 8.1 GB, 6 Nov

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem box_PP : pairBox rPP (qZ ptsPos ptsPos) 1 (-38127071179348) 5234518 = true := by decide +kernel
-- kcost: 33 s measured, 6 Nov

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem box_NN : pairBox rNN (qZ ptsNeg ptsNeg) 1 (-5279775549395) 3645099 = true := by decide +kernel
-- kcost: 25 s measured, 6 Nov

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem box_CC : pairBox rCC (qZ ptsC ptsC) 1 (-147373193052358) 7763421 = true := by decide +kernel
-- kcost: 44 s measured, 6 Nov

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem box_PN : pairBox rPN (qZ ptsPos ptsNeg) 1 40455650519392 186639 = true := by decide +kernel
-- kcost: 9 s measured, 6 Nov

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem box_PD : pairBox rPD (qZ ptsPos ptsDl) 2 (-5925935229269) 639216 = true := by decide +kernel
-- kcost: 21 s measured, 6 Nov

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy

namespace CatalanMeasure.GenD.Signed.RouteI.GasEnergy

open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

theorem box_ND : pairBox rND (qZ ptsNeg ptsDl) 2 51466727869246 90606 = true := by decide +kernel
-- kcost: 11 s measured, 6 Nov

end CatalanMeasure.GenD.Signed.RouteI.GasEnergy
