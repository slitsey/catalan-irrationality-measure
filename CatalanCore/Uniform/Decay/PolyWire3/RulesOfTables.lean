module

public import CatalanCore.Uniform.Decay.PolyWire3.Top

@[expose] public section
set_option Elab.async false

/-!
# The rule record of a `PolyTables3` cover (lane H, wave Z; ledger Z02)

`hasScaledDecay_of_tables3` builds the `PolyCellRulesB` record of the tables inside its proof and discharges
`checkPB` there.  A consumer that takes the record (`Support.Certificate`, the jet decay of a double-pole datum)
needs it as a term: `rulesOfTables3` is that record, and `checkPB_of_tables3` says that the table check
`T.check D P = true` makes `checkPB` hold for it.  Both are the lines of `hasScaledDecay_of_tables3`, unchanged.
-/

namespace CatalanCore.Uniform.Decay.PolyWire3

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.PolyChain CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
open CatalanCore.Uniform.Decay.FarField (MPData mpGlobalOk PLCell plLine plChain plSum plCapOkOf
  plCapOkOf_sound)

/-- The cap upper bound that is never used (the cap cells of the tables carry their own bounds). -/
def capUbNone (G₀ : BlockGeom) : CapUb G₀.nodePot := ⟨fun _ _ => false, fun _ _ _ h => by simp at h⟩

/-- **The rule record of the tables `T` over the geometry `G₀`.** -/
noncomputable def rulesOfTables3 (G₀ : BlockGeom) (T : PolyTables3)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) : PolyCellRulesB G₀.nodePot :=
  have hV : ∀ z, G₀.nodePot z = nuPot T.nu z := nodePot_eq_nuPot G₀ T.RP T.CP hrow hcol
  { tubeOk := fun D P => decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
      T.tubeG D.noRay P
    lineOk := fun D p => globalOk (cellPieces D.noRay T.nu) T.M &&
      T.line.any fun c => decide (c.ulo = p.1 ∧ c.uhi = p.2) &&
      lineCellOk T.nu T.M T.Rtwo T.eW T.eP D.noRay c
    capOk := fun D => plCapOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol (capUbNone G₀)) T.ubPL T.capCells T.G D.noRay
    energyOk := fun D => energyOkOf pairOracle T.E D.noRay
    tube_sound := fun D P hb h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq, PolyTables3.tubeG] at h
      obtain ⟨⟨hM, hf⟩, hg, ht⟩ := h
      have hbn := basicOk_noRay hb
      have hMq : D.noRay.Mq = G₀.totalMass := by
        show D.Mq = _
        rw [hM, hMq0]
      exact tubeCheck_sound T.nu T.M T.Rtwo T.eW T.eP hV (D := D.noRay) hbn
        (farHyp_of_tables G₀ T.RP T.CP hrow hcol (SplineData.basicOk_sound hbn) hMq hf) hg ht
    line_sound := fun D hb p h => by
      simp only [Bool.and_eq_true] at h
      obtain ⟨hg, h⟩ := h
      obtain ⟨c, _, hc⟩ := List.any_eq_true.1 h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨h1, h2⟩, hok⟩ := hc
      intro x hx1 hx2
      exact lineCellOk_sound T.nu T.M T.Rtwo T.eW T.eP hV D.noRay hg c hok x (by rw [h1]; exact hx1)
        (by rw [h2]; exact hx2)
    cap_sound := fun D hb h => plCapOkOf_sound (mkCapOracle G₀ T.RP T.CP hrow hcol (capUbNone G₀)) T.ubPL
      (ubPL_sound T hV) T.capCells T.G D.noRay (basicOk_noRay hb) h
    energy_sound := fun D hb h => energyOkOf_sound pairOracle T.E D.noRay (basicOk_noRay hb) h }

/-- **The table check gives `checkPB` of the record.** -/
theorem checkPB_of_tables3 (G₀ : BlockGeom) (T : PolyTables3)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) {D : SplineData} {P : RatPolygon} (hT : T.check D P = true) :
    checkPB (rulesOfTables3 G₀ T hrow hcol hMq0) D P = true := by
  have hV : ∀ z, G₀.nodePot z = nuPot T.nu z := nodePot_eq_nuPot G₀ T.RP T.CP hrow hcol
  have hT' := hT
  simp only [PolyTables3.check, Bool.and_eq_true, decide_eq_true_eq] at hT'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hT'
  have h7' : D.lineCells.all ((rulesOfTables3 G₀ T hrow hcol hMq0).lineOk D) = true := lineTest3_all T D.noRay h7
  have h8' : plCapOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol (capUbNone G₀)) T.ubPL T.capCells T.G D.noRay = true :=
    capCheck_imp T G₀ hV hrow hcol (capUbNone G₀) D.noRay h8
  have h9' : energyOkOf pairOracle T.E D.noRay = true := energyOk2_imp h9
  simp only [checkPB, Bool.and_eq_true, decide_eq_true_eq]
  simp only [rulesOfTables3, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h4, h5⟩, h6⟩⟩, h7'⟩, h8'⟩, h9'⟩

end CatalanCore.Uniform.Decay.PolyWire3

#print axioms CatalanCore.Uniform.Decay.PolyWire3.rulesOfTables3
#print axioms CatalanCore.Uniform.Decay.PolyWire3.checkPB_of_tables3
