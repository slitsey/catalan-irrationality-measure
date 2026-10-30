module

public import CatalanCore.Uniform.Decay.PolyWire3.Kinds
public import CatalanCore.Uniform.Decay.PolyWire2.Top2

@[expose] public section
set_option Elab.async false

/-!
# `hasScaledDecay_of_tables3` (lane D, package D17)

`hasScaledDecay_of_tables2` of `PolyWire2.Top2` with the tube and line cells of the single kind
`CellKind` (`PolyWire2` kinds, breakpoint cell, multipole cell, any of these on the pieces with a
per-cell set reversed) and the cap cells of kind `PLKind`
(constant upper bounds of any cell kind, or a piecewise-linear majorant).  Same statement and
hypotheses as `Top2`, `PolyTables3.check` in place of `PolyTables2.check`; the energy table is
unchanged.
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

/-- The whole input: as `PolyTables2`, with `CellKind` cells; `M` (resp. `Mn`) is the optional
multipole data of the pieces (resp. of the negated pieces, for the cap upper bounds). -/
structure PolyTables3 where
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

namespace PolyTables3

def nu (T : PolyTables3) : List Seg := nodeSegs T.RP T.CP

/-- The PL cells of the cap. -/
def capCells (T : PolyTables3) : List PLCell := T.cap.map (·.cell)

/-- The PL upper-bound oracle of the tables. -/
def ubPL (T : PolyTables3) (D : SplineData) (c : PLCell) : Bool :=
  globalOk ((cellPieces D T.nu).map negW) T.Mn &&
    T.cap.any fun x => decide (x.cell = c) && plUbOk T.nu T.Mn T.Rtwo T.eW T.eP D x

def capCheck (T : PolyTables3) (D : SplineData) : Bool :=
  globalOk ((cellPieces D T.nu).map negW) T.Mn &&
    plChain (-D.r0) T.capCells 0 && T.cap.all (plUbOk T.nu T.Mn T.Rtwo T.eW T.eP D) &&
    capGokOf T.RP T.CP D T.G &&
    decide (D.Scap + plSum D.mprime T.capCells ≤ T.G - D.mprime * D.r0)

def tubeG (T : PolyTables3) (D : SplineData) (P : RatPolygon) : Bool :=
  globalOk (cellPieces D T.nu) T.M &&
    tubeCheck T.nu T.M T.Rtwo T.eW T.eP T.F T.tmax T.tube D P

def lineTest (T : PolyTables3) (D : SplineData) : Bool :=
  globalOk (cellPieces D T.nu) T.M &&
    (decide (D.lineCells = T.line.map fun c => (c.ulo, c.uhi)) &&
      T.line.all (lineCellOk T.nu T.M T.Rtwo T.eW T.eP D))

/-- **The Boolean check** (everything is `= true` data). -/
def check (T : PolyTables3) (D : SplineData) (P : RatPolygon) : Bool :=
  D.basicOkP && P.okB && decide (D.r0 = P.r0) &&
    decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
    T.tubeG D.noRay P &&
    T.lineTest D.noRay && T.capCheck D.noRay && energyOk2 T.E D.noRay

end PolyTables3

theorem lineTest3_all (T : PolyTables3) (D : SplineData) (h : T.lineTest D = true) :
    D.lineCells.all (fun p => globalOk (cellPieces D T.nu) T.M &&
      T.line.any fun c => decide (c.ulo = p.1 ∧ c.uhi = p.2) &&
      lineCellOk T.nu T.M T.Rtwo T.eW T.eP D c) = true := by
  simp only [PolyTables3.lineTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hg, h1, h2⟩ := h
  rw [h1, List.all_map]
  rw [List.all_eq_true]
  intro c hc
  simp only [Function.comp, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hg, c, hc, ⟨rfl, rfl⟩, List.all_eq_true.1 h2 c hc⟩

theorem capCheck_imp (T : PolyTables3) (G₀ : BlockGeom) (hV : ∀ z, G₀.nodePot z = nuPot T.nu z)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (U : CapUb G₀.nodePot) (D : SplineData) (h : T.capCheck D = true) :
    plCapOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.ubPL T.capCells T.G D = true := by
  simp only [PolyTables3.capCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hgn, hch⟩, hall⟩, hG⟩, hsum⟩ := h
  simp only [plCapOkOf, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hch, ?_⟩, ?_⟩, hsum⟩
  · rw [List.all_eq_true]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    simp only [PolyTables3.ubPL, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hgn, x, hx, rfl, List.all_eq_true.1 hall x hx⟩
  · exact hG

theorem ubPL_sound (T : PolyTables3) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot T.nu z) :
    ∀ D : SplineData, D.basicOk = true → ∀ c, T.ubPL D c = true → ∀ x : ℝ, (c.1 : ℝ) ≤ x →
      x ≤ c.2.1 → gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ plLine c x := by
  intro D _ c h
  simp only [PolyTables3.ubPL, Bool.and_eq_true] at h
  obtain ⟨hg, h⟩ := h
  obtain ⟨x, _, hx⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨hc, hok⟩ := hx
  subst hc
  exact plUbOk_sound T.nu T.Mn T.Rtwo T.eW T.eP hV D hg x hok

/-- **`hasScaledDecay_of_tables3`**: from the table check conclude `HasScaledDecay`. -/
theorem hasScaledDecay_of_tables3 (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTables3)
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
  let U : CapUb G₀.nodePot := ⟨fun _ _ => false, fun _ _ _ h => by simp at h⟩
  let R : PolyCellRulesB G₀.nodePot :=
    { tubeOk := fun D P => decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
        T.tubeG D.noRay P
      lineOk := fun D p => globalOk (cellPieces D.noRay T.nu) T.M &&
        T.line.any fun c => decide (c.ulo = p.1 ∧ c.uhi = p.2) &&
        lineCellOk T.nu T.M T.Rtwo T.eW T.eP D.noRay c
      capOk := fun D => plCapOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.ubPL T.capCells T.G D.noRay
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
      cap_sound := fun D hb h => plCapOkOf_sound (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.ubPL
        (ubPL_sound T hV) T.capCells T.G D.noRay (basicOk_noRay hb) h
      energy_sound := fun D hb h => energyOkOf_sound pairOracle T.E D.noRay (basicOk_noRay hb) h }
  have hchk : checkPB R D P = true := by
    have hT' := hT
    simp only [PolyTables3.check, Bool.and_eq_true, decide_eq_true_eq] at hT'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hT'
    have h7' : D.lineCells.all (R.lineOk D) = true := lineTest3_all T D.noRay h7
    have h8' : plCapOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.ubPL T.capCells T.G D.noRay = true :=
      capCheck_imp T G₀ hV hrow hcol U D.noRay h8
    have h9' : energyOkOf pairOracle T.E D.noRay = true := energyOk2_imp h9
    simp only [checkPB, Bool.and_eq_true, decide_eq_true_eq]
    simp only [R, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h4, h5⟩, h6⟩⟩, h7'⟩, h8'⟩, h9'⟩
  have hMq : D.Mq = G₀.totalMass := by
    simp only [PolyTables3.check, Bool.and_eq_true, decide_eq_true_eq] at hT
    rw [hT.1.1.1.1.1.2, hMq0]
  exact hasScaledDecay_of_check_poly G₀ hC hAR hnorm1 R.toRules D P (checkP_of_checkPB hchk) hMq hd
    hInu (nodePot_conj G₀) ((nodePot_real_continuous G₀).continuousOn) hsupp hBd0 hBc hBr hBq hm0 hm0μ
    he0 heε depth

end CatalanCore.Uniform.Decay.PolyWire3
