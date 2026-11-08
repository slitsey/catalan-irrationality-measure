module

public import CatalanCore.Uniform.Bank.Plane1.Cover.Check
public import CatalanCore.Uniform.Bank.Plane1.Decay
public import CatalanCore.Uniform.Bank.Plane1.Bound

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # The plane 1 decay cover (wave P114; ledger P114, P111)

`TabP1`, `Dp1`: the generated decay cover of the 25-piece layout of `(altGeom (1/6))`, `epsilon_0 = 10^-6`, jet order 12,
checked through the folded rule record (`PolyWire3.TopFold`, CK4): `TabP1.check Dp1 PplyP1 = true` (`Plane1.Cover.Check`).
**One cover serves every plane frame, on both supports.**  `planeDecay_cover` is `PlaneDecay Dp1.Dt Dp1.ccert`, i.e. the
hypothesis (H) of `plane_point`, with no further input: the frame conditions are discharged in `Plane1.Decay`. -/

namespace CatalanCore.Uniform.Bank.Plane1
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Polygon
  CatalanCore.Uniform.Decay.AltDecay

/-- The table cover of the plane 1 decay (25 pieces, folded rule record). -/
abbrev TabP1 : PolyTablesF := Cover.TabC
/-- The spline data of the cover: `Dt` and `ccert` are its decay rate and constant. -/
abbrev Dp1 : SplineData := Cover.Dchi
/-- The polygon of the cover. -/
abbrev PplyP1 : RatPolygon := Cover.Pply

theorem cover_check : TabP1.check Dp1 PplyP1 = true := Cover.check_true

theorem tabP1_RP : TabP1.RP = altPieces planeC := by decide +kernel
theorem tabP1_CP : TabP1.CP = altPieces planeC := by decide +kernel
theorem tabP1_Mq : TabP1.Mq = 1 + planeC / 2 := by decide +kernel
theorem dp1_dim : Dp1.dim = 3 := by decide +kernel
theorem dp1_eps : 0 < Dp1.ε := by decide +kernel
theorem dp1_energy : energyCheck 30 (altPieces planeC) (altPieces planeC) Dp1.Inu = true := by
  -- kcost: 0.21 s measured (energy check at N = 30 on the P1N25 data)
  decide +kernel

/-- **The decay of the plane (hypothesis (H) of `plane_point`)**, from the generated cover: every plane frame, both supports. -/
theorem planeDecay_cover : PlaneDecay (Dp1.Dt : ℝ) (Dp1.ccert : ℝ) :=
  fun σ a b c h0 =>
    plane_decay_F σ a b c h0 TabP1 tabP1_RP tabP1_CP tabP1_Mq Dp1 PplyP1 cover_check dp1_dim 30 dp1_energy dp1_eps planeDepth

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.planeDecay_cover
