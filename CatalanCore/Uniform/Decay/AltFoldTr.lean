module

public import CatalanCore.Uniform.Decay.AltFold
public import CatalanCore.Uniform.Decay.PolyWire3.TopTr

@[expose] public section
set_option Elab.async false

/-!
# Decay of an alternating bank from its merged, truncated-logarithm tables (ledger B05a, B05b)

`AltFold.altGeom_hasScaledDecay_F` with `PolyTablesTr` (node pieces merged, tube cells with the
truncated-logarithm breakpoint rule) in place of `PolyTablesF`.  Same hypotheses and conclusion.
-/

namespace CatalanCore.Uniform.Decay.AltDecay
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.PolyCells

/-- **Decay of an alternating bank from its merged tables with the truncated-logarithm tube.** -/
theorem altGeom_hasScaledDecay_Tr (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {Fr : Frame}
    (hC : Frame.contourCheck Fr = true)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTablesTr)
    (hRP : T.RP = altPieces c) (hCP : T.CP = altPieces c) (hMq : T.Mq = 1 + c / 2)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true) (hd : D.dim = Fr.d)
    (N : ℕ) (hE : energyCheck N (altPieces c) (altPieces c) D.Inu = true)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i) (hε : 0 < D.ε) (depth : ℕ) :
    HasScaledDecay ((altGeom c hc).family Fr depth) (altGeom c hc).scale (D.Dt : ℝ)
      (D.ccert : ℝ) := by
  obtain ⟨hbc, hbr, hbq⟩ := altGeom_blocks_v c hc hc1
  have hε' : (0 : ℝ) < (D.ε : ℝ) := by exact_mod_cast hε
  exact hasScaledDecay_of_tablesTr (altGeom c hc) (Frame.contourOK_of_check hC) hAR hnorm1 T
    (by rw [altGeom_rowPieces, hRP]) (by rw [altGeom_colPieces, hCP])
    (by rw [hMq, altGeom_totalMass]) D P hT hd
    (inu_le_nodeEnergy_of_check (altGeom_rowPieces c hc) (altGeom_colPieces c hc) hE)
    (altGeom_supp c hc) (Bd := 2) (by norm_num) hbc hbr hbq hm0 hm0μ
    (e := (D.ε : ℝ) / 2) (by linarith) (by linarith) depth

end CatalanCore.Uniform.Decay.AltDecay
