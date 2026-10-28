import CatalanCore.Uniform.Decay.PolyWire.Far
import CatalanCore.Uniform.Decay.PolyWire.Tables
import CatalanCore.Uniform.Decay.PolyFull.FullLb
set_option Elab.async false

/-!
# `hasScaledDecay_of_tables` (lane D, package D11)

One theorem for the polygon family: from the Boolean check `PolyTables.check D P = true` of the
cell tables (far data, tube cells with the tail segment, line cells, cap lower bounds, pair-energy
table) conclude `HasScaledDecay`.  The remaining hypotheses are the geometry links between the
tables and the block geometry (`rowPieces`/`colPieces` are the rational pieces, `Mq` is the total
mass) and the frame hypotheses of D7.

* the tail `tailSet L d` is covered by the tube check (`tail_covered`): the finite tail segment is
  an ordinary edge of `edgesAll P tmax`, and `t ≥ tmax` is far (`PolyCells.tubeCheck_sound`);
* `FarHyp` is discharged by the Boolean `farDataOk` (`Far.lean`);
* `hV` is `nodePot_eq_nuPot` (`Link.lean`).
-/

namespace CatalanCore.Uniform.Decay.PolyWire

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.PolyChain CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform

/-- The whole input: node pieces, far data, near tuning, cell tables, cap cells, energy table. -/
structure PolyTables where
  Mq : ℚ
  RP : List (ℚ × ℚ × ℚ)
  CP : List (ℚ × ℚ × ℚ)
  Rn : ℚ
  F : FarData
  n : ℕ
  Rtwo : ℚ
  eW : ℕ
  eP : ℕ
  tmax : ℚ
  tube : List ((Pt × Pt) × List TCell)
  line : List TCell
  capCells : List CapCell
  cap : List TCell
  E : List (List ℚ)

namespace PolyTables

def nt (T : PolyTables) : NearTables :=
  { nu := nodeSegs T.RP T.CP, n := T.n, Rtwo := T.Rtwo, eW := T.eW, eP := T.eP, tube := T.tube,
    line := T.line, cap := T.cap }

/-- Parameter intervals of the tube table. -/
def tcells (T : PolyTables) : List (List (ℚ × ℚ)) :=
  T.tube.map fun x => x.2.map fun c => (c.ulo, c.uhi)

def tubeCheckT (T : PolyTables) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (0 < T.tmax) && decide (0 ≤ P.s) &&
    tubeCellsOk (fun e c => cellFarOk D T.F e c ||
      segNearT T.nt.nu T.n T.Rtwo T.eW T.eP T.tube D e c) (edgesAll P T.tmax) T.tcells &&
    farOk D T.F ((lastPt (basePt P) P.verts).2 + P.s * T.tmax)

def capCheckT (T : PolyTables) (D : SplineData) : Bool :=
  capChain (-D.r0) T.capCells 0 && T.capCells.all (lbOkT T.nt.nu T.n T.Rtwo T.eW T.eP T.cap D) &&
    decide (D.Scap ≤ capLbSum D.mprime T.capCells)

/-- **The Boolean check** (everything is `= true` data). -/
def check (T : PolyTables) (D : SplineData) (P : RatPolygon) : Bool :=
  D.basicOkP && P.okB && decide (D.r0 = P.r0) &&
    decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay && T.tubeCheckT D.noRay P &&
    D.lineCells.all (lineOkT T.nt.nu T.n T.Rtwo T.eW T.eP T.line D.noRay) &&
    T.capCheckT D.noRay && energyOkOf pairOracle T.E D.noRay

end PolyTables

/-- The tube test of the tables is D9's `tubeCheck` with the table near oracle. -/
theorem tubeCheckT_eq (T : PolyTables) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot T.nt.nu z)
    (D : SplineData) (P : RatPolygon) :
    T.tubeCheckT D P = tubeCheck (nearOracle_of_tables T.nt hV) T.F T.tmax T.tcells D P := rfl

theorem capCheckT_eq (T : PolyTables) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot T.nt.nu z)
    (D : SplineData) :
    T.capCheckT D = capLbOkOf (capOracle_of_tables T.nt hV) T.capCells D := rfl

/-- **Tail.**  If the tube check passes, every point of the tail `L + t(-1 + i s)` (`t ≥ 0`), with
any real transverse shift of size `≤ W`, satisfies `m' ≤ g`.  The finite part is covered by the cells of the
tail segment, the rest by the far rule. -/
theorem tail_covered {Vnu : ℂ → ℝ} (N : SegNearOracle Vnu) {F : FarData} {tmax : ℚ}
    {tcells : List (List (ℚ × ℚ))} {D : SplineData} {P : RatPolygon}
    (hb : D.basicOk = true) (H : FarHyp D Vnu F) (h : tubeCheck N F tmax tcells D P = true) :
    ∀ z ∈ tailSet (vertC (lastPt (basePt P) P.verts)) P.tailDir, ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (z + (δ : ℂ)) := by
  intro z hz δ hδ
  refine tubeCheck_sound N hb H h z (Or.inr ?_) δ hδ
  have hL := getLast_map_vertC P.verts _ (basePt P) (base_eq P) (List.cons_ne_nil _ _)
  rw [hL]
  exact hz

/-- **`hasScaledDecay_of_tables`**: from the table check conclude `HasScaledDecay`. -/
theorem hasScaledDecay_of_tables (G₀ : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTables)
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
  have hV : ∀ z, G₀.nodePot z = nuPot T.nt.nu z := nodePot_eq_nuPot G₀ T.RP T.CP hrow hcol
  let N := nearOracle_of_tables T.nt hV
  let Lo := lineOracle_of_tables T.nt hV
  let Lb := capOracle_of_tables T.nt hV
  let R : PolyCellRulesB G₀.nodePot :=
    { tubeOk := fun D P => decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
        tubeCheck N T.F T.tmax T.tcells D.noRay P
      lineOk := fun D p => Lo.lineOk D.noRay p
      capOk := fun D => capLbOkOf Lb T.capCells D.noRay
      energyOk := fun D => energyOkOf pairOracle T.E D.noRay
      tube_sound := fun D P hb h => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hM, hf⟩, ht⟩ := h
        have hbn := basicOk_noRay hb
        have hMq : D.noRay.Mq = G₀.totalMass := by
          show D.Mq = _
          rw [hM, hMq0]
        exact tubeCheck_sound (D := D.noRay) N hbn
          (farHyp_of_tables G₀ T.RP T.CP hrow hcol (SplineData.basicOk_sound hbn) hMq hf) ht
      line_sound := fun D hb p h => Lo.line_sound D.noRay (basicOk_noRay hb) p h
      cap_sound := fun D hb h => capLbOkOf_sound Lb T.capCells D.noRay (basicOk_noRay hb)
        ((nodePot_real_continuous G₀).continuousOn) h
      energy_sound := fun D hb h => energyOkOf_sound pairOracle T.E D.noRay (basicOk_noRay hb) h }
  have hchk : checkPB R D P = true := by
    have hT' := hT
    simp only [PolyTables.check, Bool.and_eq_true, decide_eq_true_eq] at hT'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hT'
    simp only [checkPB, Bool.and_eq_true, decide_eq_true_eq]
    simp only [R, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h4, h5⟩, h6⟩⟩, h7⟩, h8⟩, h9⟩
  have hMq : D.Mq = G₀.totalMass := by
    simp only [PolyTables.check, Bool.and_eq_true, decide_eq_true_eq] at hT
    rw [hT.1.1.1.1.1.2, hMq0]
  exact hasScaledDecay_of_check_poly G₀ hC hAR hnorm1 R.toRules D P (checkP_of_checkPB hchk) hMq hd
    hInu (nodePot_conj G₀) ((nodePot_real_continuous G₀).continuousOn) hsupp hBd0 hBc hBr hBq hm0 hm0μ
    he0 heε depth

end CatalanCore.Uniform.Decay.PolyWire
