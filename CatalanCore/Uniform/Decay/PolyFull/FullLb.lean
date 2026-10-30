module

public import CatalanCore.Uniform.Decay.PolyFull.Full
public import CatalanCore.Uniform.Decay.PolyFull.CapLb

@[expose] public section
set_option Elab.async false

/-!
# The polygon theorem with the lower-bound cap rule (lane D, package D10)

`hasScaledDecay_poly_lb`: as `hasScaledDecay_poly_full`, with the cap checked by `capLbOkOf` (lower
bounds of `g` on cap cells, `CapLb`) instead of D6's Darboux rule (upper bounds and a pair-energy
lower bound of `∫ g`).  Then the only oracle hypotheses are the lower-bound near-cell oracles
`N` (tube cells), `Lo` (line cells), `Lb` (cap cells) and the far field `hfar`.
-/

namespace CatalanCore.Uniform.Decay.PolyFull

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform

/-- Polygon rules with an arbitrary sound cap test. -/
def mkPolyRulesG {Vnu : ℂ → ℝ} (F : FarData)
    (hfar : ∀ D : SplineData, D.basicOk = true → FarHyp D Vnu F)
    (N : SegNearOracle Vnu) (tmax : ℚ) (tcells : List (List (ℚ × ℚ))) (Lo : LineOracle Vnu)
    (capOk : SplineData → Bool)
    (cap_sound : ∀ D : SplineData, D.basicOk = true → capOk D = true →
      IntervalIntegrable
        (fun x : ℝ => min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0)
        MeasureTheory.volume (-(D.r0 : ℝ)) 0 ∧
      (D.Scap : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0,
        min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0)
    (PO : PairOracle) (E : List (List ℚ)) : PolyCellRulesB Vnu where
  tubeOk D P := tubeCheck N F tmax tcells D.noRay P
  lineOk D p := Lo.lineOk D.noRay p
  capOk D := capOk D.noRay
  energyOk D := energyOkOf PO E D.noRay
  tube_sound D P hb h := tubeCheck_sound (D := D.noRay) N (basicOk_noRay hb) (hfar _ (basicOk_noRay hb)) h
  line_sound D hb p h := Lo.line_sound D.noRay (basicOk_noRay hb) p h
  cap_sound D hb h := cap_sound D.noRay (basicOk_noRay hb) h
  energy_sound D hb h := energyOkOf_sound PO E D.noRay (basicOk_noRay hb) h

/-- **End to end for the polygon family, lower-bound cap rule.** -/
theorem hasScaledDecay_poly_lb (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm)
    {F : FarData} (hfar : ∀ D : SplineData, D.basicOk = true → FarHyp D G₀.nodePot F)
    (N : SegNearOracle G₀.nodePot) (tmax : ℚ) (tcells : List (List (ℚ × ℚ)))
    (Lo : LineOracle G₀.nodePot) (Lb : CapLb G₀.nodePot) (cells : List CapCell)
    (E : List (List ℚ))
    (D : SplineData) (P : RatPolygon)
    (hb : D.basicOkP = true) (hP : P.okB = true) (hr0 : D.r0 = P.r0)
    (htube : tubeCheck N F tmax tcells D.noRay P = true)
    (hline : D.lineCells.all (Lo.lineOk D.noRay) = true)
    (hcap : capLbOkOf Lb cells D.noRay = true)
    (hen : energyOkOf pairOracle E D.noRay = true)
    (hMq : D.Mq = G₀.totalMass)
    (hd : D.dim = Fr.d) (hInu : (D.Inu : ℝ) ≤ G₀.nodeEnergy)
    (hsupp : ∀ r a : ℕ, a ∈ (G₀.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G₀.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G₀.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G₀.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (D.ε : ℝ)) (depth : ℕ) :
    HasScaledDecay (G₀.family Fr depth) G₀.scale (D.Dt : ℝ) (D.ccert : ℝ) := by
  let R := mkPolyRulesG F hfar N tmax tcells Lo (capLbOkOf Lb cells)
    (fun D hb h => capLbOkOf_sound Lb cells D hb ((nodePot_real_continuous G₀).continuousOn) h)
    pairOracle E
  have hchk : checkPB R D P = true := by
    simp only [checkPB, R, mkPolyRulesG, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨hb, hP⟩, hr0⟩, htube⟩, hline⟩, hcap⟩, hen⟩
  exact hasScaledDecay_of_check_poly G₀ hC hAR hnorm1 R.toRules D P (checkP_of_checkPB hchk) hMq hd
    hInu (nodePot_conj G₀) ((nodePot_real_continuous G₀).continuousOn) hsupp hBd0 hBc hBr hBq hm0 hm0μ
    he0 heε depth

end CatalanCore.Uniform.Decay.PolyFull
