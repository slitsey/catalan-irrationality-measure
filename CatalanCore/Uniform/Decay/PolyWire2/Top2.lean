import CatalanCore.Uniform.Decay.PolyWire2.Kinds
import CatalanCore.Uniform.Decay.PolyWire2.Energy2
import CatalanCore.Uniform.Decay.PolyWire.Top
set_option Elab.async false

/-!
# `hasScaledDecay_of_tables2` (lane B, package B3b)

`hasScaledDecay_of_tables` of D11 with the per-cell tables of `Kinds` (fast rules `cellOkF` /
`mixOkF`, order per cell) and the cons-form energy test.  Statement and hypotheses are those of
D11's theorem, with `PolyTables2.check` in place of `PolyTables.check`.
-/

namespace CatalanCore.Uniform.Decay.PolyWire2

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.PolyChain CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform
  CatalanCore.Uniform.Decay.PolyWire

/-- The whole input: node pieces, far data, near tuning, per-cell tables, cap cells, energy table. -/
structure PolyTables2 where
  Mq : ℚ
  RP : List (ℚ × ℚ × ℚ)
  CP : List (ℚ × ℚ × ℚ)
  Rn : ℚ
  F : FarData
  Rtwo : ℚ
  eW : ℕ
  eP : ℕ
  tmax : ℚ
  tube : List (List TCell2)
  line : List TCell2
  cap : List (TCell2 × ℚ)
  G : ℚ
  E : List (List ℚ)

namespace PolyTables2

def nu (T : PolyTables2) : List Seg := nodeSegs T.RP T.CP

def capCells (T : PolyTables2) : List CapCell := T.cap.map fun c => (c.1.ulo, c.1.uhi, c.2)

def lineTest (T : PolyTables2) (D : SplineData) : Bool :=
  decide (D.lineCells = T.line.map fun c => (c.ulo, c.uhi)) &&
    T.line.all (lineCellOk2 T.nu T.Rtwo T.eW T.eP D)

def capCheck2 (T : PolyTables2) (D : SplineData) : Bool :=
  capChain (-D.r0) T.capCells 0 && T.cap.all (ubCellOk2 T.nu T.Rtwo T.eW T.eP D) &&
    capGokOf T.RP T.CP D T.G &&
    decide (D.Scap + capSum D.mprime T.capCells ≤ T.G - D.mprime * D.r0)

/-- **The Boolean check** (everything is `= true` data). -/
def check (T : PolyTables2) (D : SplineData) (P : RatPolygon) : Bool :=
  D.basicOkP && P.okB && decide (D.r0 = P.r0) &&
    decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
    tubeCheck2 T.nu T.Rtwo T.eW T.eP T.F T.tmax T.tube D.noRay P &&
    T.lineTest D.noRay && T.capCheck2 D.noRay && energyOk2 T.E D.noRay

end PolyTables2

theorem lineTest_all (T : PolyTables2) (D : SplineData) (h : T.lineTest D = true) :
    D.lineCells.all (fun p => T.line.any fun c => decide (c.ulo = p.1 ∧ c.uhi = p.2) &&
      lineCellOk2 T.nu T.Rtwo T.eW T.eP D c) = true := by
  simp only [PolyTables2.lineTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1, List.all_map]
  rw [List.all_eq_true]
  intro c hc
  simp only [Function.comp, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨c, hc, ⟨rfl, rfl⟩, List.all_eq_true.1 h2 c hc⟩

/-- The cap upper-bound oracle of the tables. -/
def capOracle2 (T : PolyTables2) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot T.nu z) : CapUb Vnu where
  ubOk D c := T.cap.any fun x => decide (x.1.ulo = c.1 ∧ x.1.uhi = c.2.1 ∧ x.2 = c.2.2) &&
    ubCellOk2 T.nu T.Rtwo T.eW T.eP D x
  ub_sound D _ c h := by
    obtain ⟨x, _, hx⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, hok⟩ := hx
    intro y hy1 hy2
    have := ubCellOk2_sound T.nu T.Rtwo T.eW T.eP hV D x hok y (by rw [h1]; exact hy1)
      (by rw [h2]; exact hy2)
    rw [h3] at this
    exact this

theorem capCheck2_imp (T : PolyTables2) (G₀ : BlockGeom) (hV : ∀ z, G₀.nodePot z = nuPot T.nu z)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (D : SplineData) (h : T.capCheck2 D = true) :
    capOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol (capOracle2 T hV)) T.capCells T.G D = true := by
  simp only [PolyTables2.capCheck2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hch, hall⟩, hG⟩, hsum⟩ := h
  simp only [capOkOf, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hch, ?_⟩, ?_⟩, hsum⟩
  · rw [List.all_eq_true]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    show (capOracle2 T hV).ubOk D _ = true
    simp only [capOracle2, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨x, hx, ⟨rfl, rfl, rfl⟩, List.all_eq_true.1 hall x hx⟩
  · exact hG

/-- **`hasScaledDecay_of_tables2`**: from the table check conclude `HasScaledDecay`. -/
theorem hasScaledDecay_of_tables2 (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTables2)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true)
    (hd : D.dim = Fr.d) (hInu : (D.Inu : ℝ) ≤ G₀.nodeEnergy)
    (hsupp : ∀ r a : ℕ, a ∈ (G₀.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G₀.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G₀.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G₀.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (D.ε : ℝ)) (depth : ℕ) :
    HasScaledDecay (G₀.family Fr depth) G₀.scale (D.Dt : ℝ) (D.ccert : ℝ) := by
  have hV : ∀ z, G₀.nodePot z = nuPot T.nu z := nodePot_eq_nuPot G₀ T.RP T.CP hrow hcol
  let U := capOracle2 T hV
  let R : PolyCellRulesB G₀.nodePot :=
    { tubeOk := fun D P => decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
        tubeCheck2 T.nu T.Rtwo T.eW T.eP T.F T.tmax T.tube D.noRay P
      lineOk := fun D p => T.line.any fun c => decide (c.ulo = p.1 ∧ c.uhi = p.2) &&
        lineCellOk2 T.nu T.Rtwo T.eW T.eP D.noRay c
      capOk := fun D => capOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.capCells T.G D.noRay
      energyOk := fun D => energyOkOf pairOracle T.E D.noRay
      tube_sound := fun D P hb h => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hM, hf⟩, ht⟩ := h
        have hbn := basicOk_noRay hb
        have hMq : D.noRay.Mq = G₀.totalMass := by
          show D.Mq = _
          rw [hM, hMq0]
        exact tubeCheck2_sound T.nu T.Rtwo T.eW T.eP hV (D := D.noRay) hbn
          (farHyp_of_tables G₀ T.RP T.CP hrow hcol (SplineData.basicOk_sound hbn) hMq hf) ht
      line_sound := fun D hb p h => by
        obtain ⟨c, _, hc⟩ := List.any_eq_true.1 h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨h1, h2⟩, hok⟩ := hc
        intro x hx1 hx2
        exact lineCellOk2_sound T.nu T.Rtwo T.eW T.eP hV D.noRay c hok x (by rw [h1]; exact hx1)
          (by rw [h2]; exact hx2)
      cap_sound := fun D hb h => capOkOf_sound (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.capCells T.G
        D.noRay (basicOk_noRay hb) h
      energy_sound := fun D hb h => energyOkOf_sound pairOracle T.E D.noRay (basicOk_noRay hb) h }
  have hchk : checkPB R D P = true := by
    have hT' := hT
    simp only [PolyTables2.check, Bool.and_eq_true, decide_eq_true_eq] at hT'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hT'
    have h7' : D.lineCells.all (R.lineOk D) = true := lineTest_all T D.noRay h7
    have h8' : capOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.capCells T.G D.noRay = true :=
      capCheck2_imp T G₀ hV hrow hcol D.noRay h8
    have h9' : energyOkOf pairOracle T.E D.noRay = true := energyOk2_imp h9
    simp only [checkPB, Bool.and_eq_true, decide_eq_true_eq]
    simp only [R, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h4, h5⟩, h6⟩⟩, h7'⟩, h8'⟩, h9'⟩
  have hMq : D.Mq = G₀.totalMass := by
    simp only [PolyTables2.check, Bool.and_eq_true, decide_eq_true_eq] at hT
    rw [hT.1.1.1.1.1.2, hMq0]
  exact hasScaledDecay_of_check_poly G₀ hC hAR hnorm1 R.toRules D P (checkP_of_checkPB hchk) hMq hd
    hInu (nodePot_conj G₀) ((nodePot_real_continuous G₀).continuousOn) hsupp hBd0 hBc hBr hBq hm0 hm0μ
    he0 heε depth

end CatalanCore.Uniform.Decay.PolyWire2
