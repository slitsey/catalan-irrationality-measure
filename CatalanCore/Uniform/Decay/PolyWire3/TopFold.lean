module

public import CatalanCore.Uniform.Decay.PolyWire3.Top
public import CatalanCore.Uniform.Decay.PolyWire3.Fold
public import CatalanCore.Uniform.Decay.PolyWire3.Cache

@[expose] public section
set_option Elab.async false

/-!
# `hasScaledDecay_of_tablesF`: the rule record with the folds and cached cells (lane H, wave H3; ledger CK4)

A sibling of `PolyWire3.Top`.  `PolyTablesF` has the fields of `PolyTables3`, plus `MF` (the
multipole data of the folded line and cap list) and `cn` (the class representative of each energy
pair), and its line, cap and energy tests are the folded ones of `PolyWire3.Fold`:

* `lineTestF`, `capCheckF`: the line and cap cells run on `foldL (foldRof D nu) (foldUof D nu)` after
  one `foldOk` test per cover;
* `energyFoldOk` in place of `energyOk2`.

`PolyTablesFC` is the same with a tube of items (`TItem`: plain cells and cached blocks of `Cache`),
the modulus sum `MS` of the piece list being checked once in `tubeCheckC`.

Both export the rule record itself (`rulesOfTablesF`, `rulesOfTablesFC`), the `checkPB` equality
(`checkPB_of_tablesF`, `checkPB_of_tablesFC`) and, composed with `hasScaledDecay_of_check_poly`,
`hasScaledDecay_of_tablesF`, `hasScaledDecay_of_tablesFC`, whose hypotheses are those of
`hasScaledDecay_of_tables3`.  The record is stated for any `BlockGeom`, so a consumer that is not a
`Frame` (the plane-2 reference) takes the record and `checkPB`.
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

/-! ### The folded piece lists -/

/-- The pieces equal to their conjugate. -/
def foldRof (D : SplineData) (nu : List Seg) : List WP :=
  (cellPieces D nu).filter fun P => decide (conjWP P = P)

/-- The pieces in the upper half plane (one of each conjugate pair). -/
def foldUof (D : SplineData) (nu : List Seg) : List WP :=
  (cellPieces D nu).filter fun P => decide (0 < P.A.im + P.B.im)

/-- The folded cap cell test: a constant bound through `ubFoldOk`, a chord through `linFoldOk`. -/
def plUbFoldOk (qs : List WP) (Wl Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (x : PLCap) : Bool :=
  match x.kind with
  | .const k =>
      decide (x.cell = (k.1.ulo, k.1.uhi, k.2, k.2)) && ubFoldOk qs none Wl Rtwo eW eP D k
  | .lin n lo C Fs =>
      linFoldOk qs Wl Rtwo eW eP D n lo C Fs x.cell.1 x.cell.2.1 x.cell.2.2.1 x.cell.2.2.2

theorem plUbFoldOk_sound {R U : List WP} (nu : List Seg) (Wl Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData)
    (hf : foldOk R U (cellPieces D nu) = true) (x : PLCap)
    (h : plUbFoldOk (foldL R U) Wl Rtwo eW eP D x = true) :
    ∀ y : ℝ, (x.cell.1 : ℝ) ≤ y → y ≤ x.cell.2.1 →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨y, 0⟩ ≤ plLine x.cell y := by
  intro y hy1 hy2
  unfold plUbFoldOk at h
  rcases x with ⟨⟨a, b, ua, ub⟩, k⟩
  cases k with
  | const k =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hcell, hok⟩ := h
    simp only [Prod.mk.injEq] at hcell
    obtain ⟨h1, h2, h3, h4⟩ := hcell
    have := ubFoldOk_sound nu none Wl Rtwo eW eP hV D hf rfl k hok y
      (by simp only at hy1; rw [← h1]; exact hy1) (by simp only at hy2; rw [← h2]; exact hy2)
    unfold plLine
    simp only
    subst h3; subst h4
    simpa using this
  | lin n lo C Fs =>
    exact linFoldOk_sound nu Wl Rtwo eW eP hV D hf h y hy1 hy2

/-! ### The part of the tables that does not depend on the tube -/

/-- Line, cap and energy data, with the node pieces. -/
structure FoldParts where
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

namespace FoldParts

def nu (Q : FoldParts) : List Seg := nodeSegs Q.RP Q.CP

def capCells (Q : FoldParts) : List PLCell := Q.cap.map (·.cell)

/-- The class representative function of the energy table. -/
def cnFun (Q : FoldParts) : ℕ → ℕ → ℕ × ℕ := fun i j => (Q.cn.getD i []).getD j (i, j)

def qs (Q : FoldParts) (D : SplineData) : List WP := foldL (foldRof D Q.nu) (foldUof D Q.nu)

def lineTest (Q : FoldParts) (D : SplineData) : Bool :=
  (foldOk (foldRof D Q.nu) (foldUof D Q.nu) (cellPieces D Q.nu) && globalOk (Q.qs D) Q.MF) &&
    decide (D.lineCells = Q.line.map fun c => (c.ulo, c.uhi)) &&
    Q.line.all (lineFoldOk (Q.qs D) Q.MF D.W Q.Rtwo Q.eW Q.eP D)

def capTest (Q : FoldParts) (D : SplineData) : Bool :=
  (foldOk (foldRof D Q.nu) (foldUof D Q.nu) (cellPieces D Q.nu) &&
      globalOk ((Q.qs D).map negW) Q.Mn) &&
    plChain (-D.r0) Q.capCells 0 && Q.cap.all (plUbFoldOk (Q.qs D) D.W Q.Rtwo Q.eW Q.eP D) &&
    capGokOf Q.RP Q.CP D Q.G &&
    decide (D.Scap + plSum D.mprime Q.capCells ≤ Q.G - D.mprime * D.r0)

def energyTest (Q : FoldParts) (D : SplineData) : Bool := energyFoldOk D Q.cnFun Q.E

/-- The upper-bound oracle of the cap cells. -/
def ubPL (Q : FoldParts) (D : SplineData) (c : PLCell) : Bool :=
  foldOk (foldRof D Q.nu) (foldUof D Q.nu) (cellPieces D Q.nu) &&
    Q.cap.any fun x => decide (x.cell = c) && plUbFoldOk (Q.qs D) D.W Q.Rtwo Q.eW Q.eP D x

theorem lineTest_all (Q : FoldParts) (D : SplineData) (h : Q.lineTest D = true) :
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

theorem capTest_imp (Q : FoldParts) (G₀ : BlockGeom)
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

theorem ubPL_sound (Q : FoldParts) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot Q.nu z) :
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

end FoldParts

/-- **The rule record from the parts and a tube rule.**  `tubeOk` is the tube test and `tube_sound`
its soundness, both stated as the record states them. -/
noncomputable def rulesOfParts (G₀ : BlockGeom) (Q : FoldParts)
    (hrow : G₀.rowPieces = Q.RP.map ratPiece) (hcol : G₀.colPieces = Q.CP.map ratPiece)
    (tubeOk : SplineData → RatPolygon → Bool)
    (tube_sound : ∀ D P, D.basicOkP = true → tubeOk D P = true → ∀ w ∈ normSet P, ∀ δ : ℝ,
      |δ| ≤ (D.W : ℝ) → (D.mprime : ℝ) ≤ gNu D.Mq G₀.nodePot (D.ε : ℝ) D.A D.B D.f (w + δ)) :
    PolyCellRulesB G₀.nodePot :=
  have hV : ∀ z, G₀.nodePot z = nuPot Q.nu z := nodePot_eq_nuPot G₀ Q.RP Q.CP hrow hcol
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
      (FoldParts.ubPL_sound Q hV) Q.capCells Q.G D.noRay (basicOk_noRay hb) h
    energy_sound := fun D hb h => energyFoldOk_sound hb Q.cnFun Q.E h }

/-- `checkPB` of the record from the tests. -/
theorem checkPB_of_parts (G₀ : BlockGeom) (Q : FoldParts)
    (hrow : G₀.rowPieces = Q.RP.map ratPiece) (hcol : G₀.colPieces = Q.CP.map ratPiece)
    (tubeOk : SplineData → RatPolygon → Bool) {tube_sound} {D : SplineData} {P : RatPolygon}
    (hb : D.basicOkP = true) (hp : P.okB = true) (hr : decide (D.r0 = P.r0) = true)
    (ht : tubeOk D P = true) (hl : Q.lineTest D.noRay = true) (hc : Q.capTest D.noRay = true)
    (he : Q.energyTest D.noRay = true) :
    checkPB (rulesOfParts G₀ Q hrow hcol tubeOk tube_sound) D P = true := by
  have h7 := FoldParts.lineTest_all Q D.noRay hl
  have h8 := FoldParts.capTest_imp Q G₀ hrow hcol
    ⟨fun _ _ => false, fun _ _ _ h => by simp at h⟩ D.noRay hc
  simp only [checkPB, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨hb, hp⟩, hr⟩, ht⟩, h7⟩, h8⟩, he⟩

/-- **`HasScaledDecay` from a rule record whose check passes** (the tail of `hasScaledDecay_of_tables3`). -/
theorem hasScaledDecay_of_rules (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (R : PolyCellRulesB G₀.nodePot)
    (D : SplineData) (P : RatPolygon) (hchk : checkPB R D P = true)
    (hMq : D.Mq = G₀.totalMass)
    (hd : D.dim = Fr.d) (hInu : (D.Inu : ℝ) ≤ G₀.nodeEnergy)
    (hsupp : ∀ r a : ℕ, a ∈ (G₀.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G₀.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G₀.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G₀.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (D.ε : ℝ)) (depth : ℕ) :
    HasScaledDecay (G₀.family Fr depth) G₀.scale (D.Dt : ℝ) (D.ccert : ℝ) :=
  hasScaledDecay_of_check_poly G₀ hC hAR hnorm1 R.toRules D P (checkP_of_checkPB hchk) hMq hd
    hInu (nodePot_conj G₀) ((nodePot_real_continuous G₀).continuousOn) hsupp hBd0 hBc hBr hBq hm0 hm0μ
    he0 heε depth

/-! ### The tables with a plain tube: `PolyTablesF` -/

/-- The whole input, as `PolyTables3`, plus `MF` (multipole data of the folded list) and `cn`
(class representatives of the energy table). -/
structure PolyTablesF where
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

namespace PolyTablesF

def nu (T : PolyTablesF) : List Seg := nodeSegs T.RP T.CP

def capCells (T : PolyTablesF) : List PLCell := T.cap.map (·.cell)

/-- The class representative function. -/
def cnFun (T : PolyTablesF) : ℕ → ℕ → ℕ × ℕ := fun i j => (T.cn.getD i []).getD j (i, j)

/-- The line, cap and energy data. -/
def parts (T : PolyTablesF) : FoldParts :=
  ⟨T.RP, T.CP, T.Rtwo, T.eW, T.eP, T.MF, T.Mn, T.line, T.cap, T.G, T.E, T.cn⟩

def tubeG (T : PolyTablesF) (D : SplineData) (P : RatPolygon) : Bool :=
  globalOk (cellPieces D T.nu) T.M &&
    tubeCheck T.nu T.M T.Rtwo T.eW T.eP T.F T.tmax T.tube D P

def lineTestF (T : PolyTablesF) (D : SplineData) : Bool :=
  (foldOk (foldRof D T.nu) (foldUof D T.nu) (cellPieces D T.nu) &&
      globalOk (foldL (foldRof D T.nu) (foldUof D T.nu)) T.MF) &&
    decide (D.lineCells = T.line.map fun c => (c.ulo, c.uhi)) &&
    T.line.all (lineFoldOk (foldL (foldRof D T.nu) (foldUof D T.nu)) T.MF D.W T.Rtwo T.eW T.eP D)

def capCheckF (T : PolyTablesF) (D : SplineData) : Bool :=
  (foldOk (foldRof D T.nu) (foldUof D T.nu) (cellPieces D T.nu) &&
      globalOk ((foldL (foldRof D T.nu) (foldUof D T.nu)).map negW) T.Mn) &&
    plChain (-D.r0) T.capCells 0 &&
    T.cap.all (plUbFoldOk (foldL (foldRof D T.nu) (foldUof D T.nu)) D.W T.Rtwo T.eW T.eP D) &&
    capGokOf T.RP T.CP D T.G &&
    decide (D.Scap + plSum D.mprime T.capCells ≤ T.G - D.mprime * D.r0)

/-- **The Boolean check** (everything is `= true` data). -/
def check (T : PolyTablesF) (D : SplineData) (P : RatPolygon) : Bool :=
  D.basicOkP && P.okB && decide (D.r0 = P.r0) &&
    decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
    T.tubeG D.noRay P &&
    T.lineTestF D.noRay && T.capCheckF D.noRay &&
    energyFoldOk D.noRay (fun i j => (T.cn.getD i []).getD j (i, j)) T.E

theorem lineTestF_eq (T : PolyTablesF) (D : SplineData) : T.lineTestF D = T.parts.lineTest D := rfl

theorem capCheckF_eq (T : PolyTablesF) (D : SplineData) : T.capCheckF D = T.parts.capTest D := rfl

/-- The tube rule. -/
def tubeOk (T : PolyTablesF) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay && T.tubeG D.noRay P

theorem tubeOk_sound (G₀ : BlockGeom) (T : PolyTablesF)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) :
    ∀ D P, D.basicOkP = true → T.tubeOk D P = true → ∀ w ∈ normSet P, ∀ δ : ℝ,
      |δ| ≤ (D.W : ℝ) → (D.mprime : ℝ) ≤ gNu D.Mq G₀.nodePot (D.ε : ℝ) D.A D.B D.f (w + δ) := by
  intro D P hb h
  have hV : ∀ z, G₀.nodePot z = nuPot T.nu z := nodePot_eq_nuPot G₀ T.RP T.CP hrow hcol
  simp only [tubeOk, Bool.and_eq_true, decide_eq_true_eq, tubeG] at h
  obtain ⟨⟨hM, hf⟩, hg, ht⟩ := h
  have hbn := basicOk_noRay hb
  have hMq : D.noRay.Mq = G₀.totalMass := by
    show D.Mq = _
    rw [hM, hMq0]
  exact tubeCheck_sound T.nu T.M T.Rtwo T.eW T.eP hV (D := D.noRay) hbn
    (farHyp_of_tables G₀ T.RP T.CP hrow hcol (SplineData.basicOk_sound hbn) hMq hf) hg ht

end PolyTablesF

/-- **The rule record of the tables** (consumed by plane 2 as it is, and by
`hasScaledDecay_of_tablesF`). -/
noncomputable def rulesOfTablesF (G₀ : BlockGeom) (T : PolyTablesF)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) : PolyCellRulesB G₀.nodePot :=
  rulesOfParts G₀ T.parts hrow hcol T.tubeOk (T.tubeOk_sound G₀ hrow hcol hMq0)

/-- **The check implies the check of the record.** -/
theorem checkPB_of_tablesF (G₀ : BlockGeom) (T : PolyTablesF)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) {D : SplineData} {P : RatPolygon} (hT : T.check D P = true) :
    checkPB (rulesOfTablesF G₀ T hrow hcol hMq0) D P = true := by
  simp only [PolyTablesF.check, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hb, hp⟩, hr⟩, hm⟩, hf⟩, ht⟩, hl⟩, hc⟩, he⟩ := hT
  refine checkPB_of_parts G₀ T.parts hrow hcol T.tubeOk hb hp (by simpa using hr) ?_ hl hc he
  simp only [PolyTablesF.tubeOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hm, hf⟩, ht⟩

/-- **`hasScaledDecay_of_tablesF`**: as `hasScaledDecay_of_tables3`, with the folded tests. -/
theorem hasScaledDecay_of_tablesF (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTablesF)
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
  have hMq : D.Mq = G₀.totalMass := by
    simp only [PolyTablesF.check, Bool.and_eq_true, decide_eq_true_eq] at hT
    rw [hT.1.1.1.1.1.2, hMq0]
  exact hasScaledDecay_of_rules G₀ hC hAR hnorm1 (rulesOfTablesF G₀ T hrow hcol hMq0) D P
    (checkPB_of_tablesF G₀ T hrow hcol hMq0 hT) hMq hd hInu hsupp hBd0 hBc hBr hBq hm0 hm0μ he0 heε
    depth

/-! ### The tables with cached blocks in the tube: `PolyTablesFC` -/

/-- As `PolyTablesF`, with the tube made of items (cells and cached blocks) and the modulus sum
`MS` of the piece list, checked once. -/
structure PolyTablesFC where
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
  tube : List (List TItem)
  MS : ℚ
  line : List TCell
  cap : List PLCap
  G : ℚ
  E : List (List ℚ)
  MF : Option MPData
  cn : List (List (ℕ × ℕ))

namespace PolyTablesFC

def nu (T : PolyTablesFC) : List Seg := nodeSegs T.RP T.CP

def capCells (T : PolyTablesFC) : List PLCell := T.cap.map (·.cell)

def cnFun (T : PolyTablesFC) : ℕ → ℕ → ℕ × ℕ := fun i j => (T.cn.getD i []).getD j (i, j)

def parts (T : PolyTablesFC) : FoldParts :=
  ⟨T.RP, T.CP, T.Rtwo, T.eW, T.eP, T.MF, T.Mn, T.line, T.cap, T.G, T.E, T.cn⟩

def tubeG (T : PolyTablesFC) (D : SplineData) (P : RatPolygon) : Bool :=
  globalOk (cellPieces D T.nu) T.M &&
    tubeCheckC T.nu T.M T.Rtwo T.eW T.eP T.F T.tmax T.MS T.tube D P

def lineTestF (T : PolyTablesFC) (D : SplineData) : Bool :=
  (foldOk (foldRof D T.nu) (foldUof D T.nu) (cellPieces D T.nu) &&
      globalOk (foldL (foldRof D T.nu) (foldUof D T.nu)) T.MF) &&
    decide (D.lineCells = T.line.map fun c => (c.ulo, c.uhi)) &&
    T.line.all (lineFoldOk (foldL (foldRof D T.nu) (foldUof D T.nu)) T.MF D.W T.Rtwo T.eW T.eP D)

def capCheckF (T : PolyTablesFC) (D : SplineData) : Bool :=
  (foldOk (foldRof D T.nu) (foldUof D T.nu) (cellPieces D T.nu) &&
      globalOk ((foldL (foldRof D T.nu) (foldUof D T.nu)).map negW) T.Mn) &&
    plChain (-D.r0) T.capCells 0 &&
    T.cap.all (plUbFoldOk (foldL (foldRof D T.nu) (foldUof D T.nu)) D.W T.Rtwo T.eW T.eP D) &&
    capGokOf T.RP T.CP D T.G &&
    decide (D.Scap + plSum D.mprime T.capCells ≤ T.G - D.mprime * D.r0)

def check (T : PolyTablesFC) (D : SplineData) (P : RatPolygon) : Bool :=
  D.basicOkP && P.okB && decide (D.r0 = P.r0) &&
    decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
    T.tubeG D.noRay P &&
    T.lineTestF D.noRay && T.capCheckF D.noRay &&
    energyFoldOk D.noRay (fun i j => (T.cn.getD i []).getD j (i, j)) T.E

theorem lineTestF_eq (T : PolyTablesFC) (D : SplineData) : T.lineTestF D = T.parts.lineTest D := rfl

theorem capCheckF_eq (T : PolyTablesFC) (D : SplineData) : T.capCheckF D = T.parts.capTest D := rfl

def tubeOk (T : PolyTablesFC) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay && T.tubeG D.noRay P

theorem tubeOk_sound (G₀ : BlockGeom) (T : PolyTablesFC)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) :
    ∀ D P, D.basicOkP = true → T.tubeOk D P = true → ∀ w ∈ normSet P, ∀ δ : ℝ,
      |δ| ≤ (D.W : ℝ) → (D.mprime : ℝ) ≤ gNu D.Mq G₀.nodePot (D.ε : ℝ) D.A D.B D.f (w + δ) := by
  intro D P hb h
  have hV : ∀ z, G₀.nodePot z = nuPot T.nu z := nodePot_eq_nuPot G₀ T.RP T.CP hrow hcol
  simp only [tubeOk, Bool.and_eq_true, decide_eq_true_eq, tubeG] at h
  obtain ⟨⟨hM, hf⟩, hg, ht⟩ := h
  have hbn := basicOk_noRay hb
  have hMq : D.noRay.Mq = G₀.totalMass := by
    show D.Mq = _
    rw [hM, hMq0]
  exact tubeCheckC_sound T.nu T.M T.Rtwo T.eW T.eP hV (D := D.noRay) hbn
    (farHyp_of_tables G₀ T.RP T.CP hrow hcol (SplineData.basicOk_sound hbn) hMq hf) hg ht

end PolyTablesFC

/-- The rule record of the cached tables. -/
noncomputable def rulesOfTablesFC (G₀ : BlockGeom) (T : PolyTablesFC)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) : PolyCellRulesB G₀.nodePot :=
  rulesOfParts G₀ T.parts hrow hcol T.tubeOk (T.tubeOk_sound G₀ hrow hcol hMq0)

theorem checkPB_of_tablesFC (G₀ : BlockGeom) (T : PolyTablesFC)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (hMq0 : T.Mq = G₀.totalMass) {D : SplineData} {P : RatPolygon} (hT : T.check D P = true) :
    checkPB (rulesOfTablesFC G₀ T hrow hcol hMq0) D P = true := by
  simp only [PolyTablesFC.check, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hb, hp⟩, hr⟩, hm⟩, hf⟩, ht⟩, hl⟩, hc⟩, he⟩ := hT
  refine checkPB_of_parts G₀ T.parts hrow hcol T.tubeOk hb hp (by simpa using hr) ?_ hl hc he
  simp only [PolyTablesFC.tubeOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hm, hf⟩, ht⟩

theorem hasScaledDecay_of_tablesFC (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTablesFC)
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
  have hMq : D.Mq = G₀.totalMass := by
    simp only [PolyTablesFC.check, Bool.and_eq_true, decide_eq_true_eq] at hT
    rw [hT.1.1.1.1.1.2, hMq0]
  exact hasScaledDecay_of_rules G₀ hC hAR hnorm1 (rulesOfTablesFC G₀ T hrow hcol hMq0) D P
    (checkPB_of_tablesFC G₀ T hrow hcol hMq0 hT) hMq hd hInu hsupp hBd0 hBc hBr hBq hm0 hm0μ he0 heε
    depth

end CatalanCore.Uniform.Decay.PolyWire3

#print axioms CatalanCore.Uniform.Decay.PolyWire3.hasScaledDecay_of_tablesF
#print axioms CatalanCore.Uniform.Decay.PolyWire3.hasScaledDecay_of_tablesFC
#print axioms CatalanCore.Uniform.Decay.PolyWire3.checkPB_of_tablesF
#print axioms CatalanCore.Uniform.Decay.PolyWire3.checkPB_of_tablesFC
