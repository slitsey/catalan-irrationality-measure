module

public import CatalanCore.Uniform.Decay.AltDecay
public import CatalanCore.Uniform.Decay.PolyWire3.TopFold

@[expose] public section
set_option Elab.async false

/-!
# Decay of any alternating bank from its folded tables (lane H, wave H3; ledger N8)

`AltDecay.altGeom_hasScaledDecay` with the fold record: every geometry and frame hypothesis of
`hasScaledDecay_of_tablesF` for `altGeom c` is discharged by the lemmas of `AltDecay`, once.  The
statement differs from `altGeom_hasScaledDecay` only in the tables, `PolyTablesF` (plain tube) or
`PolyTablesFC` (tube with cached blocks), and the check `T.check D P = true` being the folded one.
The node energy is `hE : energyCheck N … D.Inu`, kept as it is; the fold replaces `energyOk2` inside
the check, not `D.Inu`.
-/

namespace CatalanCore.Uniform.Decay.AltDecay
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.PolyCells

/-- **Decay of an alternating bank from its folded tables.** -/
theorem altGeom_hasScaledDecay_F (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {Fr : Frame}
    (hC : Frame.contourCheck Fr = true)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTablesF)
    (hRP : T.RP = altPieces c) (hCP : T.CP = altPieces c) (hMq : T.Mq = 1 + c / 2)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true) (hd : D.dim = Fr.d)
    (N : ℕ) (hE : energyCheck N (altPieces c) (altPieces c) D.Inu = true)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i) (hε : 0 < D.ε) (depth : ℕ) :
    HasScaledDecay ((altGeom c hc).family Fr depth) (altGeom c hc).scale (D.Dt : ℝ)
      (D.ccert : ℝ) := by
  obtain ⟨hbc, hbr, hbq⟩ := altGeom_blocks_v c hc hc1
  have hε' : (0 : ℝ) < (D.ε : ℝ) := by exact_mod_cast hε
  exact hasScaledDecay_of_tablesF (altGeom c hc) (Frame.contourOK_of_check hC) hAR hnorm1 T
    (by rw [altGeom_rowPieces, hRP]) (by rw [altGeom_colPieces, hCP])
    (by rw [hMq, altGeom_totalMass]) D P hT hd
    (inu_le_nodeEnergy_of_check (altGeom_rowPieces c hc) (altGeom_colPieces c hc) hE)
    (altGeom_supp c hc) (Bd := 2) (by norm_num) hbc hbr hbq hm0 hm0μ
    (e := (D.ε : ℝ) / 2) (by linarith) (by linarith) depth

/-- The same with cached blocks in the tube. -/
theorem altGeom_hasScaledDecay_FC (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {Fr : Frame}
    (hC : Frame.contourCheck Fr = true)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTablesFC)
    (hRP : T.RP = altPieces c) (hCP : T.CP = altPieces c) (hMq : T.Mq = 1 + c / 2)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true) (hd : D.dim = Fr.d)
    (N : ℕ) (hE : energyCheck N (altPieces c) (altPieces c) D.Inu = true)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i) (hε : 0 < D.ε) (depth : ℕ) :
    HasScaledDecay ((altGeom c hc).family Fr depth) (altGeom c hc).scale (D.Dt : ℝ)
      (D.ccert : ℝ) := by
  obtain ⟨hbc, hbr, hbq⟩ := altGeom_blocks_v c hc hc1
  have hε' : (0 : ℝ) < (D.ε : ℝ) := by exact_mod_cast hε
  exact hasScaledDecay_of_tablesFC (altGeom c hc) (Frame.contourOK_of_check hC) hAR hnorm1 T
    (by rw [altGeom_rowPieces, hRP]) (by rw [altGeom_colPieces, hCP])
    (by rw [hMq, altGeom_totalMass]) D P hT hd
    (inu_le_nodeEnergy_of_check (altGeom_rowPieces c hc) (altGeom_colPieces c hc) hE)
    (altGeom_supp c hc) (Bd := 2) (by norm_num) hbc hbr hbq hm0 hm0μ
    (e := (D.ε : ℝ) / 2) (by linarith) (by linarith) depth

/-- The rule record of the alternating geometry and its check, for a consumer that takes the record. -/
theorem altGeom_checkPB_F (c : ℚ) (hc : 0 < c) (T : PolyTablesF)
    (hRP : T.RP = altPieces c) (hCP : T.CP = altPieces c) (hMq : T.Mq = 1 + c / 2)
    {D : SplineData} {P : RatPolygon} (hT : T.check D P = true) :
    checkPB (rulesOfTablesF (altGeom c hc) T (by rw [altGeom_rowPieces, hRP])
      (by rw [altGeom_colPieces, hCP]) (by rw [hMq, altGeom_totalMass])) D P = true :=
  checkPB_of_tablesF _ _ _ _ _ hT

theorem altGeom_checkPB_FC (c : ℚ) (hc : 0 < c) (T : PolyTablesFC)
    (hRP : T.RP = altPieces c) (hCP : T.CP = altPieces c) (hMq : T.Mq = 1 + c / 2)
    {D : SplineData} {P : RatPolygon} (hT : T.check D P = true) :
    checkPB (rulesOfTablesFC (altGeom c hc) T (by rw [altGeom_rowPieces, hRP])
      (by rw [altGeom_colPieces, hCP]) (by rw [hMq, altGeom_totalMass])) D P = true :=
  checkPB_of_tablesFC _ _ _ _ _ hT

end CatalanCore.Uniform.Decay.AltDecay

#print axioms CatalanCore.Uniform.Decay.AltDecay.altGeom_hasScaledDecay_F
#print axioms CatalanCore.Uniform.Decay.AltDecay.altGeom_hasScaledDecay_FC
