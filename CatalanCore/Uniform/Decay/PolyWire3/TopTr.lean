module

public import CatalanCore.Uniform.Decay.PolyWire3.TopFold
public import CatalanCore.Uniform.Decay.PolyWire3.KindsTr
public import CatalanCore.Uniform.Decay.PolyWire3.NuMerge

@[expose] public section
set_option Elab.async false

/-!
# Tables with merged node pieces and the truncated-logarithm tube (ledger B05a, B05b; sibling of `TopFold`)

For banks with `CP = RP` (the alternating banks: sevenths, thirds, ...) the node measure
`nodeSegs RP RP` lists every node piece twice.  `nuMerge RP` lists it once, with the doubled weight:

* `nuPot_nuMerge` (**B05b**): `nuPot (nuMerge RP) z = nuPot (nodeSegs RP RP) z`, by linearity of the
  segment integral in the weight (`PolyWire.piece_seg_int`).  Every cell list `cellPieces D (nuMerge RP)` is
  shorter by `|RP|` pieces than `cellPieces D (nodeSegs RP RP)`, and a cell costs time linear in its list.
* `FoldPartsM`, `PolyTablesTr`: the line, cap, energy parts of `TopFold.PolyTablesF` and a plain tube, on
  the merged list; the tube cells are checked by `tubeCheckTr` (truncated-logarithm breakpoint rule, **B05a**).
  The check includes `CP = RP`.  `hasScaledDecay_of_tablesTr` has the hypotheses and conclusion of
  `hasScaledDecay_of_tablesF`.

Nothing in `PolyWire3.Top`, `Fold`, `TopFold` or `Kinds` is changed.
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

/-! ### Line, cap and energy parts on the merged list -/

/-- As `FoldParts`, but the node list is `nuMerge RP` (the check requires `CP = RP`). -/
structure FoldPartsM where
  RP : List (ℚ × ℚ × ℚ)
  CP : List (ℚ × ℚ × ℚ)
  Rtwo : ℚ
  eW : ℕ
  eP : ℕ
  MF : Option MPData
  Mn : Option MPData
  line : List TCell
  cap : List PLCap
  G : ℚ
  E : List (List ℚ)
  cn : List (List (ℕ × ℕ))

namespace FoldPartsM

def nu (Q : FoldPartsM) : List Seg := nuMerge Q.RP

def capCells (Q : FoldPartsM) : List PLCell := Q.cap.map (·.cell)

def cnFun (Q : FoldPartsM) : ℕ → ℕ → ℕ × ℕ := fun i j => (Q.cn.getD i []).getD j (i, j)

def qs (Q : FoldPartsM) (D : SplineData) : List WP := foldL (foldRof D Q.nu) (foldUof D Q.nu)

def lineTest (Q : FoldPartsM) (D : SplineData) : Bool :=
  (foldOk (foldRof D Q.nu) (foldUof D Q.nu) (cellPieces D Q.nu) && globalOk (Q.qs D) Q.MF) &&
    decide (D.lineCells = Q.line.map fun c => (c.ulo, c.uhi)) &&
    Q.line.all (lineFoldOk (Q.qs D) Q.MF D.W Q.Rtwo Q.eW Q.eP D)

def capTest (Q : FoldPartsM) (D : SplineData) : Bool :=
  (foldOk (foldRof D Q.nu) (foldUof D Q.nu) (cellPieces D Q.nu) &&
      globalOk ((Q.qs D).map negW) Q.Mn) &&
    plChain (-D.r0) Q.capCells 0 && Q.cap.all (plUbFoldOk (Q.qs D) D.W Q.Rtwo Q.eW Q.eP D) &&
    capGokOf Q.RP Q.CP D Q.G &&
    decide (D.Scap + plSum D.mprime Q.capCells ≤ Q.G - D.mprime * D.r0)

def energyTest (Q : FoldPartsM) (D : SplineData) : Bool := energyFoldOk D Q.cnFun Q.E

/-- The upper-bound oracle of the cap cells. -/
def ubPL (Q : FoldPartsM) (D : SplineData) (c : PLCell) : Bool :=
  foldOk (foldRof D Q.nu) (foldUof D Q.nu) (cellPieces D Q.nu) &&
    Q.cap.any fun x => decide (x.cell = c) && plUbFoldOk (Q.qs D) D.W Q.Rtwo Q.eW Q.eP D x

theorem lineTest_all (Q : FoldPartsM) (D : SplineData) (h : Q.lineTest D = true) :
    D.lineCells.all (fun p => foldOk (foldRof D Q.nu) (foldUof D Q.nu) (cellPieces D Q.nu) &&
      globalOk (Q.qs D) Q.MF &&
      Q.line.any fun c => decide (c.ulo = p.1 ∧ c.uhi = p.2) &&
      lineFoldOk (Q.qs D) Q.MF D.W Q.Rtwo Q.eW Q.eP D c) = true := by
  simp only [lineTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hf, hg⟩, h1⟩, h2⟩ := h
  rw [h1, List.all_map]
  rw [List.all_eq_true]
  intro c hc
  simp only [Function.comp, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hf, hg⟩, c, hc, ⟨rfl, rfl⟩, List.all_eq_true.1 h2 c hc⟩

theorem capTest_imp (Q : FoldPartsM) (G₀ : BlockGeom)
    (hrow : G₀.rowPieces = Q.RP.map ratPiece) (hcol : G₀.colPieces = Q.CP.map ratPiece)
    (U : CapUb G₀.nodePot) (D : SplineData) (h : Q.capTest D = true) :
    plCapOkOf (mkCapOracle G₀ Q.RP Q.CP hrow hcol U) Q.ubPL Q.capCells Q.G D = true := by
  simp only [capTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hf, hgn⟩, hch⟩, hall⟩, hG⟩, hsum⟩ := h
  simp only [plCapOkOf, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hch, ?_⟩, ?_⟩, hsum⟩
  · rw [List.all_eq_true]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    simp only [ubPL, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact ⟨hf, x, hx, rfl, List.all_eq_true.1 hall x hx⟩
  · exact hG

theorem ubPL_sound (Q : FoldPartsM) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot Q.nu z) :
    ∀ D : SplineData, D.basicOk = true → ∀ c, Q.ubPL D c = true → ∀ x : ℝ, (c.1 : ℝ) ≤ x →
      x ≤ c.2.1 → gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ plLine c x := by
  intro D _ c h
  simp only [ubPL, Bool.and_eq_true] at h
  obtain ⟨hf, h⟩ := h
  obtain ⟨x, _, hx⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨hc, hok⟩ := hx
  subst hc
  exact plUbFoldOk_sound Q.nu D.W Q.Rtwo Q.eW Q.eP hV D hf x hok

end FoldPartsM

/-- The rule record from the merged parts and a tube rule (`rulesOfParts` with the node list `nuMerge RP`);
`hcp : CP = RP` is the hypothesis of the merge. -/
noncomputable def rulesOfPartsM (G₀ : BlockGeom) (Q : FoldPartsM) (hcp : Q.CP = Q.RP)
    (hrow : G₀.rowPieces = Q.RP.map ratPiece) (hcol : G₀.colPieces = Q.CP.map ratPiece)
    (tubeOk : SplineData → RatPolygon → Bool)
    (tube_sound : ∀ D P, D.basicOkP = true → tubeOk D P = true → ∀ w ∈ normSet P, ∀ δ : ℝ,
      |δ| ≤ (D.W : ℝ) → (D.mprime : ℝ) ≤ gNu D.Mq G₀.nodePot (D.ε : ℝ) D.A D.B D.f (w + δ)) :
    PolyCellRulesB G₀.nodePot :=
  have hV : ∀ z, G₀.nodePot z = nuPot Q.nu z := fun z => by
    rw [nodePot_eq_nuPot G₀ Q.RP Q.CP hrow hcol, hcp, FoldPartsM.nu, nuPot_nuMerge]
  let U : CapUb G₀.nodePot := ⟨fun _ _ => false, fun _ _ _ h => by simp at h⟩
  { tubeOk := tubeOk
    lineOk := fun D p =>
      foldOk (foldRof D.noRay Q.nu) (foldUof D.noRay Q.nu) (cellPieces D.noRay Q.nu) &&
        globalOk (Q.qs D.noRay) Q.MF &&
        Q.line.any fun c => decide (c.ulo = p.1 ∧ c.uhi = p.2) &&
          lineFoldOk (Q.qs D.noRay) Q.MF D.noRay.W Q.Rtwo Q.eW Q.eP D.noRay c
    capOk := fun D => plCapOkOf (mkCapOracle G₀ Q.RP Q.CP hrow hcol U) Q.ubPL Q.capCells Q.G D.noRay
    energyOk := fun D => Q.energyTest D.noRay
    tube_sound := tube_sound
    line_sound := fun D hb p h => by
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hf, hg⟩, h⟩ := h
      obtain ⟨c, _, hc⟩ := List.any_eq_true.1 h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨h1, h2⟩, hok⟩ := hc
      intro x hx1 hx2
      exact lineFoldOk_sound Q.nu Q.MF D.noRay.W Q.Rtwo Q.eW Q.eP hV D.noRay hf hg c hok x
        (by rw [h1]; exact hx1) (by rw [h2]; exact hx2)
    cap_sound := fun D hb h => plCapOkOf_sound (mkCapOracle G₀ Q.RP Q.CP hrow hcol U) Q.ubPL
      (FoldPartsM.ubPL_sound Q hV) Q.capCells Q.G D.noRay (basicOk_noRay hb) h
    energy_sound := fun D hb h => energyFoldOk_sound hb Q.cnFun Q.E h }

/-- `checkPB` of the record from the tests. -/
theorem checkPB_of_partsM (G₀ : BlockGeom) (Q : FoldPartsM) (hcp : Q.CP = Q.RP)
    (hrow : G₀.rowPieces = Q.RP.map ratPiece) (hcol : G₀.colPieces = Q.CP.map ratPiece)
    (tubeOk : SplineData → RatPolygon → Bool) {tube_sound} {D : SplineData} {P : RatPolygon}
    (hb : D.basicOkP = true) (hp : P.okB = true) (hr : decide (D.r0 = P.r0) = true)
    (ht : tubeOk D P = true) (hl : Q.lineTest D.noRay = true) (hc : Q.capTest D.noRay = true)
    (he : Q.energyTest D.noRay = true) :
    checkPB (rulesOfPartsM G₀ Q hcp hrow hcol tubeOk tube_sound) D P = true := by
  have h7 := FoldPartsM.lineTest_all Q D.noRay hl
  have h8 := FoldPartsM.capTest_imp Q G₀ hrow hcol
    ⟨fun _ _ => false, fun _ _ _ h => by simp at h⟩ D.noRay hc
  simp only [checkPB, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨hb, hp⟩, hr⟩, ht⟩, h7⟩, h8⟩, he⟩

/-! ### The tables -/

/-- The whole input, as `PolyTablesF`; the node list of every cell is `nuMerge RP` and the tube cells use the
truncated-logarithm breakpoint rule. -/
structure PolyTablesTr where
  Mq : ℚ
  RP : List (ℚ × ℚ × ℚ)
  CP : List (ℚ × ℚ × ℚ)
  Rn : ℚ
  F : FarData
  Rtwo : ℚ
  eW : ℕ
  eP : ℕ
  tmax : ℚ
  M : Option MPData
  Mn : Option MPData
  tube : List (List TCell)
  line : List TCell
  cap : List PLCap
  G : ℚ
  E : List (List ℚ)
  MF : Option MPData
  cn : List (List (ℕ × ℕ))

namespace PolyTablesTr

def nu (T : PolyTablesTr) : List Seg := nuMerge T.RP

def capCells (T : PolyTablesTr) : List PLCell := T.cap.map (·.cell)

def cnFun (T : PolyTablesTr) : ℕ → ℕ → ℕ × ℕ := fun i j => (T.cn.getD i []).getD j (i, j)

/-- The line, cap and energy data. -/
def parts (T : PolyTablesTr) : FoldPartsM :=
  ⟨T.RP, T.CP, T.Rtwo, T.eW, T.eP, T.MF, T.Mn, T.line, T.cap, T.G, T.E, T.cn⟩

def tubeG (T : PolyTablesTr) (D : SplineData) (P : RatPolygon) : Bool :=
  globalOk (cellPieces D T.nu) T.M &&
    tubeCheckTr T.nu T.M T.Rtwo T.eW T.eP T.F T.tmax T.tube D P

def lineTestF (T : PolyTablesTr) (D : SplineData) : Bool :=
  (foldOk (foldRof D T.nu) (foldUof D T.nu) (cellPieces D T.nu) &&
      globalOk (foldL (foldRof D T.nu) (foldUof D T.nu)) T.MF) &&
    decide (D.lineCells = T.line.map fun c => (c.ulo, c.uhi)) &&
    T.line.all (lineFoldOk (foldL (foldRof D T.nu) (foldUof D T.nu)) T.MF D.W T.Rtwo T.eW T.eP D)

def capCheckF (T : PolyTablesTr) (D : SplineData) : Bool :=
  (foldOk (foldRof D T.nu) (foldUof D T.nu) (cellPieces D T.nu) &&
      globalOk ((foldL (foldRof D T.nu) (foldUof D T.nu)).map negW) T.Mn) &&
    plChain (-D.r0) T.capCells 0 &&
    T.cap.all (plUbFoldOk (foldL (foldRof D T.nu) (foldUof D T.nu)) D.W T.Rtwo T.eW T.eP D) &&
    capGokOf T.RP T.CP D T.G &&
    decide (D.Scap + plSum D.mprime T.capCells ≤ T.G - D.mprime * D.r0)

/-- **The Boolean check** (everything is `= true` data). -/
def check (T : PolyTablesTr) (D : SplineData) (P : RatPolygon) : Bool :=
  D.basicOkP && P.okB && decide (D.r0 = P.r0) &&
    decide (D.Mq = T.Mq) && decide (T.CP = T.RP) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
    T.tubeG D.noRay P &&
    T.lineTestF D.noRay && T.capCheckF D.noRay &&
    energyFoldOk D.noRay (fun i j => (T.cn.getD i []).getD j (i, j)) T.E

theorem lineTestF_eq (T : PolyTablesTr) (D : SplineData) : T.lineTestF D = T.parts.lineTest D := rfl

theorem capCheckF_eq (T : PolyTablesTr) (D : SplineData) : T.capCheckF D = T.parts.capTest D := rfl

/-- The tube rule. -/
def tubeOk (T : PolyTablesTr) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay && T.tubeG D.noRay P

theorem tubeOk_sound (G₀ : BlockGeom) (T : PolyTablesTr) (hcp : T.CP = T.RP)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) :
    ∀ D P, D.basicOkP = true → T.tubeOk D P = true → ∀ w ∈ normSet P, ∀ δ : ℝ,
      |δ| ≤ (D.W : ℝ) → (D.mprime : ℝ) ≤ gNu D.Mq G₀.nodePot (D.ε : ℝ) D.A D.B D.f (w + δ) := by
  intro D P hb h
  have hV : ∀ z, G₀.nodePot z = nuPot T.nu z := fun z => by
    rw [nodePot_eq_nuPot G₀ T.RP T.CP hrow hcol, hcp, nu, nuPot_nuMerge]
  simp only [tubeOk, Bool.and_eq_true, decide_eq_true_eq, tubeG] at h
  obtain ⟨⟨hM, hf⟩, hg, ht⟩ := h
  have hbn := basicOk_noRay hb
  have hMq : D.noRay.Mq = G₀.totalMass := by
    show D.Mq = _
    rw [hM, hMq0]
  exact tubeCheckTr_sound T.nu T.M T.Rtwo T.eW T.eP hV (D := D.noRay) hbn
    (farHyp_of_tables G₀ T.RP T.CP hrow hcol (SplineData.basicOk_sound hbn) hMq hf) hg ht

end PolyTablesTr

/-- **The rule record of the tables.** -/
noncomputable def rulesOfTablesTr (G₀ : BlockGeom) (T : PolyTablesTr) (hcp : T.CP = T.RP)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) : PolyCellRulesB G₀.nodePot :=
  rulesOfPartsM G₀ T.parts hcp hrow hcol T.tubeOk (T.tubeOk_sound G₀ hcp hrow hcol hMq0)

/-- **The check implies the check of the record.** -/
theorem checkPB_of_tablesTr (G₀ : BlockGeom) (T : PolyTablesTr) (hcp : T.CP = T.RP)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) {D : SplineData} {P : RatPolygon} (hT : T.check D P = true) :
    checkPB (rulesOfTablesTr G₀ T hcp hrow hcol hMq0) D P = true := by
  simp only [PolyTablesTr.check, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hp⟩, hr⟩, hm⟩, _⟩, hf⟩, ht⟩, hl⟩, hc⟩, he⟩ := hT
  refine checkPB_of_partsM G₀ T.parts hcp hrow hcol T.tubeOk hb hp (by simpa using hr) ?_ hl hc he
  simp only [PolyTablesTr.tubeOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hm, hf⟩, ht⟩

/-- **`hasScaledDecay_of_tablesTr`**: as `hasScaledDecay_of_tablesF`, with the merged node list and the
truncated-logarithm tube. -/
theorem hasScaledDecay_of_tablesTr (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTablesTr)
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
  have hcp : T.CP = T.RP := by
    simp only [PolyTablesTr.check, Bool.and_eq_true, decide_eq_true_eq] at hT
    exact hT.1.1.1.1.1.2
  have hMq : D.Mq = G₀.totalMass := by
    simp only [PolyTablesTr.check, Bool.and_eq_true, decide_eq_true_eq] at hT
    rw [hT.1.1.1.1.1.1.2, hMq0]
  exact hasScaledDecay_of_rules G₀ hC hAR hnorm1 (rulesOfTablesTr G₀ T hcp hrow hcol hMq0) D P
    (checkPB_of_tablesTr G₀ T hcp hrow hcol hMq0 hT) hMq hd hInu hsupp hBd0 hBc hBr hBq hm0 hm0μ he0 heε
    depth

end CatalanCore.Uniform.Decay.PolyWire3
