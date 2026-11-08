module

public import CatalanMeasure.GenD.Signed.RouteI.AngPos0
public import CatalanMeasure.GenD.Signed.RouteI.AngPos1
public import CatalanMeasure.GenD.Signed.RouteI.AngPos2
public import CatalanMeasure.GenD.Signed.RouteI.AngPos3
public import CatalanMeasure.GenD.Signed.RouteI.AngPos4
public import CatalanMeasure.GenD.Signed.RouteI.AngPos5
public import CatalanMeasure.GenD.Signed.RouteI.AngPos6
public import CatalanMeasure.GenD.Signed.RouteI.AngPos7
public import CatalanMeasure.GenD.Signed.RouteI.AngPos8
public import CatalanMeasure.GenD.Signed.RouteI.AngPos9
public import CatalanMeasure.GenD.Signed.RouteI.AngPos10
public import CatalanMeasure.GenD.Signed.RouteI.AngPos11
public import CatalanMeasure.GenD.Signed.RouteI.AngPos12
public import CatalanMeasure.GenD.Signed.RouteI.AngPos13
public import CatalanMeasure.GenD.Signed.RouteI.AngPos14
public import CatalanMeasure.GenD.Signed.RouteI.AngPos15
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg0
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg1
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg2
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg3
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg4
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg5
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg6
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg7
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg8
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg9
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg10
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg11
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg12
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg13
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg14
public import CatalanMeasure.GenD.Signed.RouteI.AngNeg15

@[expose] public section
set_option Elab.async false

/-!
# Route I `AngAll`: the angular radius certificates of both species at all 16 radii

Case analysis only: `certN` and `certP` are the hypotheses of `AngularCap.angCap_of_certs` (design-C caps).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.AngAll

open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MomentSource
open CatalanMeasure.GenD.Signed.RouteI.MomentInputs
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

noncomputable section

/-- The negative species at every radius index. -/
def certN : ∀ i, i < capSource.nRad →
    AngularCap.AngRadiusCert capSource Sign.neg i (5463909 / 100000000)
  | 0, _ => AngNeg0.angNeg0
  | 1, _ => AngNeg1.angNeg1
  | 2, _ => AngNeg2.angNeg2
  | 3, _ => AngNeg3.angNeg3
  | 4, _ => AngNeg4.angNeg4
  | 5, _ => AngNeg5.angNeg5
  | 6, _ => AngNeg6.angNeg6
  | 7, _ => AngNeg7.angNeg7
  | 8, _ => AngNeg8.angNeg8
  | 9, _ => AngNeg9.angNeg9
  | 10, _ => AngNeg10.angNeg10
  | 11, _ => AngNeg11.angNeg11
  | 12, _ => AngNeg12.angNeg12
  | 13, _ => AngNeg13.angNeg13
  | 14, _ => AngNeg14.angNeg14
  | 15, _ => AngNeg15.angNeg15
  | k + 16, h => absurd h (by change ¬ (k + 16 < 16); omega)

/-- The positive species at every radius index. -/
def certP : ∀ i, i < capSource.nRad →
    AngularCap.AngRadiusCert capSource Sign.pos i (14762657 / 100000000)
  | 0, _ => AngPos0.angPos0
  | 1, _ => AngPos1.angPos1
  | 2, _ => AngPos2.angPos2
  | 3, _ => AngPos3.angPos3
  | 4, _ => AngPos4.angPos4
  | 5, _ => AngPos5.angPos5
  | 6, _ => AngPos6.angPos6
  | 7, _ => AngPos7.angPos7
  | 8, _ => AngPos8.angPos8
  | 9, _ => AngPos9.angPos9
  | 10, _ => AngPos10.angPos10
  | 11, _ => AngPos11.angPos11
  | 12, _ => AngPos12.angPos12
  | 13, _ => AngPos13.angPos13
  | 14, _ => AngPos14.angPos14
  | 15, _ => AngPos15.angPos15
  | k + 16, h => absurd h (by change ¬ (k + 16 < 16); omega)

end

end CatalanMeasure.GenD.Signed.RouteI.AngAll
