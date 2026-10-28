module

public import CatalanCore.Uniform.Decay.PolyCells.Tube
public import CatalanCore.Uniform.Decay.PolyChain.CheckMain

@[expose] public section

/-!
# `mkPolyRules` and the end-to-end polygon theorem (lane D, package D9)

D7's `PolyCellRules` states soundness unconditionally, so a concrete rule would have to re-run
`basicOkP` inside every cell.  `PolyCellRulesB` states soundness *under* `D.basicOkP = true`
(as D6's `CellRulesB`), with the checker `checkPB` running `basicOkP` once.  `toRules` embeds it
into `PolyCellRules` by guarding each field with `basicOkP`, and `checkP_of_checkPB` shows that
`checkPB` implies D7's `checkP` (logically; `checkP` itself is never evaluated), so
`hasScaledDecay_of_check_poly` applies.

`mkPolyRules` builds a `PolyCellRulesB` from
* the per-edge tube rule `tubeCheck` (far cells proved here; near cells: `SegNearOracle`);
* the line rule (`LineOracle`; D6's `NearOracle` gives one via `LineOracle.ofNear`);
* D6's cap rule `capOkOf` (oracle `CapOracle`);
* D6's energy rule `energyOkOf` (oracle `PairOracle`; decomposition `I0_eq_sum_pairE`).
All of D6's rules and oracles are evaluated at `D.noRay`, whose `basicOk` is `D.basicOkP`.
-/

namespace CatalanCore.Uniform.Decay.PolyCells

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyChain

/-- Polygon cell rules whose soundness may assume `D.basicOkP = true`. -/
structure PolyCellRulesB (Vnu : ℂ → ℝ) where
  tubeOk : SplineData → RatPolygon → Bool
  lineOk : SplineData → ℚ × ℚ → Bool
  capOk : SplineData → Bool
  energyOk : SplineData → Bool
  tube_sound : ∀ D P, D.basicOkP = true → tubeOk D P = true → ∀ w ∈ normSet P, ∀ δ : ℝ,
    |δ| ≤ (D.W : ℝ) → (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + δ)
  line_sound : ∀ D, D.basicOkP = true → ∀ p, lineOk D p = true → ∀ x : ℝ, (p.1 : ℝ) ≤ x →
    x ≤ p.2 → (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩
  cap_sound : ∀ D, D.basicOkP = true → capOk D = true →
    IntervalIntegrable
      (fun x : ℝ => min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0)
      MeasureTheory.volume (-(D.r0 : ℝ)) 0 ∧
    (D.Scap : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0,
      min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0
  energy_sound : ∀ D, D.basicOkP = true → energyOk D = true → I0 D.A D.B D.f ≤ D.Ibound

/-- Guard every field with `basicOkP`: D7's `PolyCellRules`. -/
def PolyCellRulesB.toRules {Vnu : ℂ → ℝ} (R : PolyCellRulesB Vnu) : PolyCellRules Vnu where
  tubeOk D P := D.basicOkP && R.tubeOk D P
  lineOk D p := D.basicOkP && R.lineOk D p
  capOk D := D.basicOkP && R.capOk D
  energyOk D := D.basicOkP && R.energyOk D
  tube_sound D P h := by
    simp only [Bool.and_eq_true] at h
    exact R.tube_sound D P h.1 h.2
  line_sound D p h := by
    simp only [Bool.and_eq_true] at h
    exact R.line_sound D h.1 p h.2
  cap_sound D h := by
    simp only [Bool.and_eq_true] at h
    exact R.cap_sound D h.1 h.2
  energy_sound D h := by
    simp only [Bool.and_eq_true] at h
    exact R.energy_sound D h.1 h.2

/-- **The polygon finite checker** (`basicOkP` is run once). -/
def checkPB {Vnu : ℂ → ℝ} (R : PolyCellRulesB Vnu) (D : SplineData) (P : RatPolygon) : Bool :=
  D.basicOkP && P.okB && decide (D.r0 = P.r0) && R.tubeOk D P && D.lineCells.all (R.lineOk D) &&
    R.capOk D && R.energyOk D

theorem checkP_of_checkPB {Vnu : ℂ → ℝ} {R : PolyCellRulesB Vnu} {D : SplineData} {P : RatPolygon}
    (h : checkPB R D P = true) : D.checkP R.toRules P = true := by
  simp only [checkPB, Bool.and_assoc, Bool.and_eq_true] at h
  obtain ⟨hb, hok, hr0, ht, hl, hc, he⟩ := h
  simp [SplineData.checkP, PolyCellRulesB.toRules, hb, hok, hr0, ht, hc, he, hl]

/-- Oracle for the line cells `[p.1, p.2] ⊆ [0,1]`. -/
structure LineOracle (Vnu : ℂ → ℝ) where
  lineOk : SplineData → ℚ × ℚ → Bool
  line_sound : ∀ D : SplineData, D.basicOk = true → ∀ p, lineOk D p = true → ∀ x : ℝ,
    (p.1 : ℝ) ≤ x → x ≤ p.2 → (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩

/-- D6's near oracle gives a line oracle (its ray cells are not used by the polygon chain). -/
def LineOracle.ofNear {Vnu : ℂ → ℝ} (N : NearOracle Vnu) : LineOracle Vnu :=
  ⟨N.lineOk, N.line_sound⟩

/-- **The concrete polygon cell rules.**  `F`: far constants; `hfar`: mass cancellation of the
node potential (`farHyp_of_nu` of D6); `tmax`, `tcells`: finite tail length and the cell lists of
the edges `edgesAll P tmax`. -/
def mkPolyRules {Vnu : ℂ → ℝ} (F : FarData)
    (hfar : ∀ D : SplineData, D.basicOk = true → FarHyp D Vnu F)
    (N : SegNearOracle Vnu) (tmax : ℚ) (tcells : List (List (ℚ × ℚ))) (Lo : LineOracle Vnu)
    (O : CapOracle Vnu) (cells : List CapCell) (G : ℚ) (PO : PairOracle) (E : List (List ℚ)) :
    PolyCellRulesB Vnu where
  tubeOk D P := tubeCheck N F tmax tcells D.noRay P
  lineOk D p := Lo.lineOk D.noRay p
  capOk D := capOkOf O cells G D.noRay
  energyOk D := energyOkOf PO E D.noRay
  tube_sound D P hb h := tubeCheck_sound (D := D.noRay) N (basicOk_noRay hb) (hfar _ (basicOk_noRay hb)) h
  line_sound D hb p h := Lo.line_sound D.noRay (basicOk_noRay hb) p h
  cap_sound D hb h := capOkOf_sound O cells G D.noRay (basicOk_noRay hb) h
  energy_sound D hb h := energyOkOf_sound PO E D.noRay (basicOk_noRay hb) h

/-- **End to end.**  From `basicOkP`, `P.okB`, `D.r0 = P.r0`, the tube test (far cells, tail,
oracle near cells), the line test, the cap test and the energy test, conclude `HasScaledDecay`.
Hypotheses on the frame/node geometry as in `hasScaledDecay_of_check_poly`. -/
theorem hasScaledDecay_of_checks_poly (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm)
    {F : FarData} (hfar : ∀ D : SplineData, D.basicOk = true → FarHyp D G₀.nodePot F)
    (N : SegNearOracle G₀.nodePot) (tmax : ℚ) (tcells : List (List (ℚ × ℚ)))
    (Lo : LineOracle G₀.nodePot) (O : CapOracle G₀.nodePot) (cells : List CapCell) (G : ℚ)
    (PO : PairOracle) (E : List (List ℚ))
    (D : SplineData) (P : RatPolygon)
    (hb : D.basicOkP = true) (hP : P.okB = true) (hr0 : D.r0 = P.r0)
    (htube : tubeCheck N F tmax tcells D.noRay P = true)
    (hline : D.lineCells.all (Lo.lineOk D.noRay) = true)
    (hcap : capOkOf O cells G D.noRay = true) (hen : energyOkOf PO E D.noRay = true)
    (hMq : D.Mq = G₀.totalMass)
    (hd : D.dim = Fr.d) (hInu : (D.Inu : ℝ) ≤ G₀.nodeEnergy)
    (hVc : ∀ s, G₀.nodePot ((starRingEnd ℂ) s) = G₀.nodePot s)
    (hUc : ContinuousOn (fun x : ℝ => G₀.nodePot (x : ℂ)) (Set.Icc (-(P.r0 : ℝ)) 0))
    (hsupp : ∀ r a : ℕ, a ∈ (G₀.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G₀.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G₀.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G₀.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (D.ε : ℝ)) (depth : ℕ) :
    HasScaledDecay (G₀.family Fr depth) G₀.scale (D.Dt : ℝ) (D.ccert : ℝ) := by
  have hchk : checkPB (mkPolyRules F hfar N tmax tcells Lo O cells G PO E) D P = true := by
    simp only [checkPB, mkPolyRules, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨hb, hP⟩, hr0⟩, htube⟩, hline⟩, hcap⟩, hen⟩
  exact hasScaledDecay_of_check_poly G₀ hC hAR hnorm1
    (mkPolyRules F hfar N tmax tcells Lo O cells G PO E).toRules D P
    (checkP_of_checkPB hchk) hMq hd hInu hVc hUc hsupp hBd0 hBc hBr hBq hm0 hm0μ he0 heε depth

end CatalanCore.Uniform.Decay.PolyCells
