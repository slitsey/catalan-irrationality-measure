import CatalanCore.Uniform.Bank.Sevenths.Cover.Check
set_option Elab.async false

/-! `HasScaledDecay` for the Sev1 bank from the verified tables (lane D, D17).  The frame and node
geometry hypotheses stay explicit. -/

namespace CatalanCore.Uniform.Bank.Sevenths.Cover
open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
  CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform
  CatalanCore.Uniform.Decay.PolyFull

theorem hasScaledDecay_bank (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm)
    (hrow : G₀.rowPieces = RP.map ratPiece) (hcol : G₀.colPieces = CP.map ratPiece)
    (hMq0 : ((13 / 12 : ℚ) : ℚ) = G₀.totalMass)
    (hd : Dchi.dim = Fr.d) (hInu : (Dchi.Inu : ℝ) ≤ G₀.nodeEnergy)
    (hsupp : ∀ r a : ℕ, a ∈ (G₀.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G₀.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G₀.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G₀.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (Dchi.ε : ℝ)) (depth : ℕ) :
    HasScaledDecay (G₀.family Fr depth) G₀.scale (Dchi.Dt : ℝ) (Dchi.ccert : ℝ) :=
  hasScaledDecay_of_tables3 G₀ hC hAR hnorm1 TabC hrow hcol hMq0 Dchi Pply check_true hd hInu hsupp
    hBd0 hBc hBr hBq hm0 hm0μ he0 heε depth

end CatalanCore.Uniform.Bank.Sevenths.Cover
