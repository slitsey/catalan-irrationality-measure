module

public import CatalanCore.Uniform.Decay.PolyFull.CapG

@[expose] public section
set_option Elab.async false

/-!
# The full polygon cell rules and the end-to-end theorem (lane D, package D10)

* `CapUb`: the one remaining cap oracle (upper bounds of `g` on cap cells).
* `mkCapOracle`: D6's `CapOracle` for the node potential `G₀.nodePot`, with `cont` and `G_sound`
  proved here (`nodePot_real_continuous`, `capGokOf_sound`).
* `nodePot_conj`: the node potential is symmetric under conjugation (so `hVc` is discharged).
* `hasScaledDecay_poly_full`: D9's `hasScaledDecay_of_checks_poly` with the cap oracle built from
  `mkCapOracle`, the pair-energy oracle `pairOracle` (D6c, on the current D6b evaluators), the
  continuity and symmetry hypotheses on `nodePot` proved.  Remaining oracle hypotheses: `N`
  (near tube cells, D6b), `Lo` (near line cells, D6b), `U` (cap upper bounds), `hfar` (far field of
  the node potential).
-/

namespace CatalanCore.Uniform.Decay.PolyFull

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform

/-- Oracle for the cap cells: upper bounds of `g` on `[a, b] ⊆ [-r0, 0]`. -/
structure CapUb (Vnu : ℂ → ℝ) where
  ubOk : SplineData → CapCell → Bool
  ub_sound : ∀ D : SplineData, D.basicOk = true → ∀ c, ubOk D c = true → ∀ x : ℝ, (c.1 : ℝ) ≤ x →
    x ≤ c.2.1 → gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ c.2.2

/-- D6's cap oracle for the node potential, from rational node pieces and cap upper bounds. -/
def mkCapOracle (G₀ : BlockGeom) (RP CP : List (ℚ × ℚ × ℚ))
    (hrow : G₀.rowPieces = RP.map ratPiece) (hcol : G₀.colPieces = CP.map ratPiece)
    (U : CapUb G₀.nodePot) : CapOracle G₀.nodePot where
  ubOk := U.ubOk
  Gok := capGokOf RP CP
  cont D _ := (nodePot_real_continuous G₀).continuousOn
  ub_sound := U.ub_sound
  G_sound D hb G h := capGokOf_sound G₀ RP CP hrow hcol D hb G h

theorem nodePot_conj (G : BlockGeom) (s : ℂ) :
    G.nodePot ((starRingEnd ℂ) s) = G.nodePot s := by
  have h : ∀ (ps : List Piece), ppotC ps ((starRingEnd ℂ) s) = ppotC ps s := by
    intro ps
    unfold ppotC
    congr 1
    refine List.map_congr_left fun P _ => ?_
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [← kern_eq_elog, ← kern_eq_elog]
    unfold kern
    simp
  unfold BlockGeom.nodePot
  rw [h, h]

/-- **End to end for the polygon family.**  From the Boolean checks (`basicOkP`, `P.okB`, the tube
test with its near-cell oracle, the line test with its oracle, the cap test, the pair-energy test)
conclude `HasScaledDecay`. -/
theorem hasScaledDecay_poly_full (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm)
    {F : FarData} (hfar : ∀ D : SplineData, D.basicOk = true → FarHyp D G₀.nodePot F)
    (N : SegNearOracle G₀.nodePot) (tmax : ℚ) (tcells : List (List (ℚ × ℚ)))
    (Lo : LineOracle G₀.nodePot) (RP CP : List (ℚ × ℚ × ℚ))
    (hrow : G₀.rowPieces = RP.map ratPiece) (hcol : G₀.colPieces = CP.map ratPiece)
    (U : CapUb G₀.nodePot) (cells : List CapCell) (G : ℚ) (E : List (List ℚ))
    (D : SplineData) (P : RatPolygon)
    (hb : D.basicOkP = true) (hP : P.okB = true) (hr0 : D.r0 = P.r0)
    (htube : tubeCheck N F tmax tcells D.noRay P = true)
    (hline : D.lineCells.all (Lo.lineOk D.noRay) = true)
    (hcap : capOkOf (mkCapOracle G₀ RP CP hrow hcol U) cells G D.noRay = true)
    (hen : energyOkOf pairOracle E D.noRay = true)
    (hMq : D.Mq = G₀.totalMass)
    (hd : D.dim = Fr.d) (hInu : (D.Inu : ℝ) ≤ G₀.nodeEnergy)
    (hsupp : ∀ r a : ℕ, a ∈ (G₀.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G₀.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G₀.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G₀.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (D.ε : ℝ)) (depth : ℕ) :
    HasScaledDecay (G₀.family Fr depth) G₀.scale (D.Dt : ℝ) (D.ccert : ℝ) :=
  hasScaledDecay_of_checks_poly G₀ hC hAR hnorm1 hfar N tmax tcells Lo
    (mkCapOracle G₀ RP CP hrow hcol U) cells G pairOracle E D P hb hP hr0 htube hline hcap hen hMq hd
    hInu (nodePot_conj G₀) ((nodePot_real_continuous G₀).continuousOn) hsupp hBd0 hBc hBr hBq hm0 hm0μ
    he0 heε depth

end CatalanCore.Uniform.Decay.PolyFull
