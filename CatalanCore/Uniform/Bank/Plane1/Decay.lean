module

public import CatalanCore.Uniform.Bank.Plane1.Frame
public import CatalanCore.Uniform.Decay.AltFold

@[expose] public section
set_option Elab.async false

/-! # The decay of the plane frames (wave H4; ledger P111)

`plane_decay` is `AltDecay.altGeom_hasScaledDecay` at `c = 1/6` for the plane frames: **one certificate serves
every weight triple of the support**.  The hypotheses on the cover (`T`, `D`, `P`, the three Boolean checks) do not
mention the weights, and every frame hypothesis of the generic theorem (contour separation, the floor condition
`hAR`, the norm, the smallest shift `1/3`, `D.dim = 3`) is discharged here once, from the support alone.

`plane_decay_F`, `plane_decay_FC` are the same with the folded rule records of `AltFold` (CK4, N8): the plane cover
of the 25-piece layout is checked through them.  The constants `D.Dt`, `D.ccert` are the cover's; the statement
holds for any cover that passes the checks. -/

namespace CatalanCore.Uniform.Bank.Plane1
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.PolyCells

section Decay

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

theorem planeFrame_mu_real (i : Fin (planeFrame σ a b c h0).d) :
    (1 / 3 : ℝ) ≤ (((planeFrame σ a b c h0).μ i : ℚ) : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).2 (planeFrame_mu_ge σ a b c h0 i)
  push_cast at h
  exact h

/-- **Decay of the plane family from its tables** (P111), for every plane frame. -/
theorem plane_decay (T : PolyTables3)
    (hRP : T.RP = altPieces planeC) (hCP : T.CP = altPieces planeC) (hMq : T.Mq = 1 + planeC / 2)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true) (hd : D.dim = 3)
    (N : ℕ) (hE : energyCheck N (altPieces planeC) (altPieces planeC) D.Inu = true)
    (hε : 0 < D.ε) (depth : ℕ) :
    HasScaledDecay ((altGeom planeC planeC_pos).family (planeFrame σ a b c h0) depth)
      (altGeom planeC planeC_pos).scale (D.Dt : ℝ) (D.ccert : ℝ) :=
  altGeom_hasScaledDecay planeC planeC_pos planeC_le_one (planeFrame_contourCheck σ a b c h0)
    (planeFrame_hAR σ a b c h0) (le_refl _) T hRP hCP hMq D P hT hd N hE (m0 := 1 / 3) (by norm_num)
    (planeFrame_mu_real σ a b c h0) hε depth

/-- The same through the folded rule record (CK4, N8), plain tube. -/
theorem plane_decay_F (T : PolyTablesF)
    (hRP : T.RP = altPieces planeC) (hCP : T.CP = altPieces planeC) (hMq : T.Mq = 1 + planeC / 2)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true) (hd : D.dim = 3)
    (N : ℕ) (hE : energyCheck N (altPieces planeC) (altPieces planeC) D.Inu = true)
    (hε : 0 < D.ε) (depth : ℕ) :
    HasScaledDecay ((altGeom planeC planeC_pos).family (planeFrame σ a b c h0) depth)
      (altGeom planeC planeC_pos).scale (D.Dt : ℝ) (D.ccert : ℝ) :=
  altGeom_hasScaledDecay_F planeC planeC_pos planeC_le_one (planeFrame_contourCheck σ a b c h0)
    (planeFrame_hAR σ a b c h0) (le_refl _) T hRP hCP hMq D P hT hd N hE (m0 := 1 / 3) (by norm_num)
    (planeFrame_mu_real σ a b c h0) hε depth

/-- The same through the folded rule record with cached blocks in the tube. -/
theorem plane_decay_FC (T : PolyTablesFC)
    (hRP : T.RP = altPieces planeC) (hCP : T.CP = altPieces planeC) (hMq : T.Mq = 1 + planeC / 2)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true) (hd : D.dim = 3)
    (N : ℕ) (hE : energyCheck N (altPieces planeC) (altPieces planeC) D.Inu = true)
    (hε : 0 < D.ε) (depth : ℕ) :
    HasScaledDecay ((altGeom planeC planeC_pos).family (planeFrame σ a b c h0) depth)
      (altGeom planeC planeC_pos).scale (D.Dt : ℝ) (D.ccert : ℝ) :=
  altGeom_hasScaledDecay_FC planeC planeC_pos planeC_le_one (planeFrame_contourCheck σ a b c h0)
    (planeFrame_hAR σ a b c h0) (le_refl _) T hRP hCP hMq D P hT hd N hE (m0 := 1 / 3) (by norm_num)
    (planeFrame_mu_real σ a b c h0) hε depth

end Decay

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.plane_decay
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_decay_F
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_decay_FC
