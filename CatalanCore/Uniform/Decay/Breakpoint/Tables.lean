import CatalanCore.Uniform.Decay.Breakpoint.Kind
import CatalanCore.Uniform.Decay.PolyWire2.Energy2
import CatalanCore.Uniform.Decay.PolyWire2.Kinds
import CatalanCore.Uniform.Decay.PolyWire.Top
set_option Elab.async false

/-!
# Tables with breakpoint cells (lane D, package D14)

`PolyWire2.Kinds` and `PolyWire2.Top2` with `TCell3` / `kindOk3` (the cell kinds of `PolyWire2` plus
the breakpoint kind) in place of `TCell2` / `kindOk2`; every statement and proof is the PolyWire2 one,
the only change is the cell type.  `hasScaledDecay_of_tables3` is `hasScaledDecay_of_tables2` with
`PolyTables3`.
-/

namespace CatalanCore.Uniform.Decay.Breakpoint

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.NearFast
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyWire2

/-! ### Tube cells -/

/-- The near test of the cell `c` of the edge `e`. -/
def nearCellT3 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (e : Pt × Pt) (c : TCell3) :
    Bool :=
  decide (D.ε < 1) &&
    kindOk3 (cellPieces D nu) (edgeCentre (cqOf e.1) (cqOf e.2) c.ulo c.uhi)
      (CQ.sub (cqOf e.2) (cqOf e.1)) ((c.uhi - c.ulo) / 2) D.W Rtwo (cpiOf D) D.mprime eW eP c.kind

theorem nearCellT3_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (e : Pt × Pt) (c : TCell3)
    (h : nearCellT3 nu Rtwo eW eP D e c = true)
    (t : ℝ) (h1 : (c.ulo : ℝ) ≤ t) (h2 : t ≤ (c.uhi : ℝ)) (δ : ℝ) (hδ : |δ| ≤ (D.W : ℝ)) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)) := by
  unfold nearCellT3 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hε, hm⟩ := h
  have key := kindOk3_sound hm (t - (((c.ulo + c.uhi) / 2 : ℚ) : ℝ)) δ (by
    rw [abs_le]; push_cast; constructor <;> linarith) hδ
  have ez : (edgeCentre (cqOf e.1) (cqOf e.2) c.ulo c.uhi).toC +
      ((t - (((c.ulo + c.uhi) / 2 : ℚ) : ℝ) : ℝ) : ℂ) * (CQ.sub (cqOf e.2) (cqOf e.1)).toC
      + (δ : ℂ) = segPtC e t + (δ : ℂ) := by
    unfold edgeCentre
    rw [CQ.toC_add, CQ.toC_smul, CQ.toC_sub, cqOf_toC, cqOf_toC]
    unfold segPtC
    push_cast; ring
  rw [ez] at key
  exact gNu_ge_of D nu hV hε key

/-- One tube cell: far or near. -/
def cellOk3 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (D : SplineData) (e : Pt × Pt)
    (c : TCell3) : Bool :=
  cellFarOk D F e (c.ulo, c.uhi) || nearCellT3 nu Rtwo eW eP D e c

/-- The cells of one edge: they cover `[0,1]` and each is ok. -/
def edgeCells3 (ok : Pt × Pt → TCell3 → Bool) (e : Pt × Pt) (cs : List TCell3) : Bool :=
  coverOk 0 1 (cs.map fun c => (c.ulo, c.uhi)) && cs.all (ok e)

/-- Edge by edge. -/
def tubeCells3 (ok : Pt × Pt → TCell3 → Bool) : List (Pt × Pt) → List (List TCell3) → Bool
  | [], [] => true
  | e :: es, cs :: css => edgeCells3 ok e cs && tubeCells3 ok es css
  | _, _ => false

theorem tubeCells3_sound {ok : Pt × Pt → TCell3 → Bool} {Q : Pt × Pt → ℝ → Prop}
    (hQ : ∀ e (c : TCell3), ok e c = true → ∀ t : ℝ, (c.ulo : ℝ) ≤ t → t ≤ (c.uhi : ℝ) → Q e t) :
    ∀ (es : List (Pt × Pt)) (css : List (List TCell3)), tubeCells3 ok es css = true →
      ∀ e ∈ es, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Q e t
  | [], [], _, e, he, _, _, _ => by simp at he
  | [], _ :: _, h, _, _, _, _, _ => by simp [tubeCells3] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [tubeCells3] at h
  | e0 :: es, cs :: css, h, e, he, t, ht0, ht1 => by
      simp only [tubeCells3, edgeCells3, Bool.and_eq_true] at h
      obtain ⟨⟨hcov, hall⟩, hrest⟩ := h
      rcases List.mem_cons.1 he with rfl | he
      · obtain ⟨p, hp, h1, h2⟩ := coverOk_sound hcov t (by simpa using ht0) (by simpa using ht1)
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
        exact hQ _ c (List.all_eq_true.1 hall c hc) t h1 h2
      · exact tubeCells3_sound hQ es css hrest e he t ht0 ht1

/-- **The tube test.** -/
def tubeCheck3 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (F : FarData) (tmax : ℚ)
    (tube : List (List TCell3)) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (0 < tmax) && decide (0 ≤ P.s) &&
    tubeCells3 (cellOk3 nu Rtwo eW eP F D) (edgesAll P tmax) tube &&
    farOk D F ((lastPt (basePt P) P.verts).2 + P.s * tmax)

theorem tubeCheck3_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) {F : FarData} {tmax : ℚ} {tube : List (List TCell3)}
    {D : SplineData} {P : RatPolygon} (hb : D.basicOk = true) (H : FarHyp D Vnu F)
    (h : tubeCheck3 nu Rtwo eW eP F tmax tube D P = true) :
    ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + (δ : ℂ)) := by
  simp only [tubeCheck3, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨htm, hs⟩, hcells⟩, hfar⟩ := h
  have B := SplineData.basicOk_sound hb
  have key := tubeCells3_sound (Q := fun e t => ∀ δ : ℝ, |δ| ≤ (D.W : ℝ) →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (segPtC e t + (δ : ℂ)))
    (fun e c hc t h1 h2 δ hδ => by
      rcases Bool.or_eq_true_iff.1 hc with hc | hc
      · exact cellFar_sound H B hc t h1 h2 δ
      · exact nearCellT3_sound nu Rtwo eW eP hV D e c hc t h1 h2 δ hδ) _ _ hcells
  intro w hw δ hδ
  rcases hw with hw | hw
  · rw [base_eq] at hw
    obtain ⟨e, he, t, h0, h1, rfl⟩ := chainSet_edges P.verts (basePt P) hw
    exact key e (List.mem_append_left _ he) t h0 h1 δ hδ
  · obtain ⟨t, ht0, rfl⟩ := hw
    have hL := getLast_map_vertC P.verts _ (basePt P) (base_eq P) (List.cons_ne_nil _ _)
    rw [hL]
    by_cases hle : t ≤ tmax
    · rw [tail_seg htm]
      have htm' : (0 : ℝ) < tmax := by exact_mod_cast htm
      refine key _ (List.mem_append_right _ (List.mem_singleton_self _)) _
        (div_nonneg ht0 htm'.le) ((div_le_one htm').2 hle) δ hδ
    · push Not at hle
      refine far_g_ge H B hfar _ ?_
      have him : (vertC (lastPt (basePt P) P.verts) + (t : ℂ) * P.tailDir + (δ : ℂ)).im
          = ((lastPt (basePt P) P.verts).2 : ℝ) + t * (P.s : ℝ) := by
        simp [vertC, RatPolygon.tailDir]
      rw [him]
      have hs' : (0 : ℝ) ≤ P.s := by exact_mod_cast hs
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hle.le hs']

/-! ### Line and cap cells -/

/-- Line cell `[ulo, uhi] ⊆ [0,1]`, threshold `gmin`. -/
def lineCellOk3 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (c : TCell3) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk3 (cellPieces D nu) ⟨(c.ulo + c.uhi) / 2, 0⟩ ⟨1, 0⟩ ((c.uhi - c.ulo) / 2) D.W Rtwo
      (cpiOf D) D.gmin eW eP c.kind

/-- Cap cell `[ulo, uhi]` with lower bound `lb` of `g`. -/
def capCellOk3 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (c : TCell3 × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk3 (cellPieces D nu) ⟨(c.1.ulo + c.1.uhi) / 2, 0⟩ ⟨1, 0⟩ ((c.1.uhi - c.1.ulo) / 2) D.W Rtwo
      (cpiOf D) c.2 eW eP c.1.kind

theorem realCell3_sound {ps : List WP} {a b W Rtwo cpi m' : ℚ} {eW eP : ℕ} {k : CellKind3}
    (hW : 0 ≤ W)
    (hc : kindOk3 ps ⟨(a + b) / 2, 0⟩ ⟨1, 0⟩ ((b - a) / 2) W Rtwo cpi m' eW eP k = true)
    (x : ℝ) (hx1 : (a : ℝ) ≤ x) (hx2 : x ≤ (b : ℝ)) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (⟨x, 0⟩ : ℂ))).sum
      + (cpi : ℝ) * |(⟨x, 0⟩ : ℂ).im| := by
  have hW' : (0 : ℝ) ≤ W := by exact_mod_cast hW
  have key := kindOk3_sound hc (x - (((a + b) / 2 : ℚ) : ℝ)) 0 (by
    rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hW')
  have hz : (⟨((a + b) / 2 : ℚ), 0⟩ : CQ).toC + ((x - (((a + b) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
      (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨x, 0⟩ := by
    apply Complex.ext <;> simp [CQ.toC]
  rw [hz] at key
  exact key

theorem lineCellOk3_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (c : TCell3)
    (h : lineCellOk3 nu Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.ulo : ℝ) ≤ x → x ≤ c.uhi →
      (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold lineCellOk3 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  exact gNu_ge_of D nu hV hε (realCell3_sound hW hm x hx1 hx2)

theorem capCellOk3_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (c : TCell3 × ℚ)
    (h : capCellOk3 nu Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.1.ulo : ℝ) ≤ x → x ≤ c.1.uhi →
      (c.2 : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold capCellOk3 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  exact gNu_ge_of D nu hV hε (realCell3_sound hW hm x hx1 hx2)

/-! ### Cap upper bounds (Darboux rule): the same cell rules for the negated pieces -/

/-- Cap cell `[ulo, uhi]` with an UPPER bound `ub` of `g`: lower bound `-ub` for the negated pieces
(on the real axis `Im = 0`, so the `cpi` term vanishes). -/
def ubCellOk3 (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) (D : SplineData) (c : TCell3 × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    kindOk3 ((cellPieces D nu).map negW) ⟨(c.1.ulo + c.1.uhi) / 2, 0⟩ ⟨1, 0⟩
      ((c.1.uhi - c.1.ulo) / 2) D.W Rtwo 0 (-c.2) eW eP c.1.kind

theorem ubCellOk3_sound (nu : List Seg) (Rtwo : ℚ) (eW eP : ℕ) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (D : SplineData) (c : TCell3 × ℚ)
    (h : ubCellOk3 nu Rtwo eW eP D c = true) :
    ∀ x : ℝ, (c.1.ulo : ℝ) ≤ x → x ≤ c.1.uhi →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ (c.2 : ℝ) := by
  intro x hx1 hx2
  unfold ubCellOk3 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  have key := realCell3_sound hW hm x hx1 hx2
  rw [negW_sum] at key
  rw [gNu_eq D nu hV]
  have him : (⟨x, 0⟩ : ℂ).im = 0 := rfl
  rw [him] at key ⊢
  simp only [abs_zero, mul_zero, add_zero, neg_neg, Rat.cast_neg, Rat.cast_zero] at key ⊢
  linarith



/-- The whole input: node pieces, far data, near tuning, per-cell tables, cap cells, energy table. -/
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
  tube : List (List TCell3)
  line : List TCell3
  cap : List (TCell3 × ℚ)
  G : ℚ
  E : List (List ℚ)

namespace PolyTables3

def nu (T : PolyTables3) : List Seg := nodeSegs T.RP T.CP

def capCells (T : PolyTables3) : List CapCell := T.cap.map fun c => (c.1.ulo, c.1.uhi, c.2)

def lineTest (T : PolyTables3) (D : SplineData) : Bool :=
  decide (D.lineCells = T.line.map fun c => (c.ulo, c.uhi)) &&
    T.line.all (lineCellOk3 T.nu T.Rtwo T.eW T.eP D)

def capCheck3 (T : PolyTables3) (D : SplineData) : Bool :=
  capChain (-D.r0) T.capCells 0 && T.cap.all (ubCellOk3 T.nu T.Rtwo T.eW T.eP D) &&
    capGokOf T.RP T.CP D T.G &&
    decide (D.Scap + capSum D.mprime T.capCells ≤ T.G - D.mprime * D.r0)

/-- **The Boolean check** (everything is `= true` data). -/
def check (T : PolyTables3) (D : SplineData) (P : RatPolygon) : Bool :=
  D.basicOkP && P.okB && decide (D.r0 = P.r0) &&
    decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
    tubeCheck3 T.nu T.Rtwo T.eW T.eP T.F T.tmax T.tube D.noRay P &&
    T.lineTest D.noRay && T.capCheck3 D.noRay && energyOk2 T.E D.noRay

end PolyTables3

theorem lineTest_all (T : PolyTables3) (D : SplineData) (h : T.lineTest D = true) :
    D.lineCells.all (fun p => T.line.any fun c => decide (c.ulo = p.1 ∧ c.uhi = p.2) &&
      lineCellOk3 T.nu T.Rtwo T.eW T.eP D c) = true := by
  simp only [PolyTables3.lineTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1, List.all_map]
  rw [List.all_eq_true]
  intro c hc
  simp only [Function.comp, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨c, hc, ⟨rfl, rfl⟩, List.all_eq_true.1 h2 c hc⟩

/-- The cap upper-bound oracle of the tables. -/
def capOracle3 (T : PolyTables3) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot T.nu z) : CapUb Vnu where
  ubOk D c := T.cap.any fun x => decide (x.1.ulo = c.1 ∧ x.1.uhi = c.2.1 ∧ x.2 = c.2.2) &&
    ubCellOk3 T.nu T.Rtwo T.eW T.eP D x
  ub_sound D _ c h := by
    obtain ⟨x, _, hx⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, hok⟩ := hx
    intro y hy1 hy2
    have := ubCellOk3_sound T.nu T.Rtwo T.eW T.eP hV D x hok y (by rw [h1]; exact hy1)
      (by rw [h2]; exact hy2)
    rw [h3] at this
    exact this

theorem capCheck3_imp (T : PolyTables3) (G₀ : BlockGeom) (hV : ∀ z, G₀.nodePot z = nuPot T.nu z)
    (hrow : G₀.rowPieces = T.RP.map ratPiece) (hcol : G₀.colPieces = T.CP.map ratPiece)
    (D : SplineData) (h : T.capCheck3 D = true) :
    capOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol (capOracle3 T hV)) T.capCells T.G D = true := by
  simp only [PolyTables3.capCheck3, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hch, hall⟩, hG⟩, hsum⟩ := h
  simp only [capOkOf, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hch, ?_⟩, ?_⟩, hsum⟩
  · rw [List.all_eq_true]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    show (capOracle3 T hV).ubOk D _ = true
    simp only [capOracle3, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨x, hx, ⟨rfl, rfl, rfl⟩, List.all_eq_true.1 hall x hx⟩
  · exact hG

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
  let U := capOracle3 T hV
  let R : PolyCellRulesB G₀.nodePot :=
    { tubeOk := fun D P => decide (D.Mq = T.Mq) && farDataOk T.F T.Rn T.RP T.CP D.noRay &&
        tubeCheck3 T.nu T.Rtwo T.eW T.eP T.F T.tmax T.tube D.noRay P
      lineOk := fun D p => T.line.any fun c => decide (c.ulo = p.1 ∧ c.uhi = p.2) &&
        lineCellOk3 T.nu T.Rtwo T.eW T.eP D.noRay c
      capOk := fun D => capOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.capCells T.G D.noRay
      energyOk := fun D => energyOkOf pairOracle T.E D.noRay
      tube_sound := fun D P hb h => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hM, hf⟩, ht⟩ := h
        have hbn := basicOk_noRay hb
        have hMq : D.noRay.Mq = G₀.totalMass := by
          show D.Mq = _
          rw [hM, hMq0]
        exact tubeCheck3_sound T.nu T.Rtwo T.eW T.eP hV (D := D.noRay) hbn
          (farHyp_of_tables G₀ T.RP T.CP hrow hcol (SplineData.basicOk_sound hbn) hMq hf) ht
      line_sound := fun D hb p h => by
        obtain ⟨c, _, hc⟩ := List.any_eq_true.1 h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨h1, h2⟩, hok⟩ := hc
        intro x hx1 hx2
        exact lineCellOk3_sound T.nu T.Rtwo T.eW T.eP hV D.noRay c hok x (by rw [h1]; exact hx1)
          (by rw [h2]; exact hx2)
      cap_sound := fun D hb h => capOkOf_sound (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.capCells T.G
        D.noRay (basicOk_noRay hb) h
      energy_sound := fun D hb h => energyOkOf_sound pairOracle T.E D.noRay (basicOk_noRay hb) h }
  have hchk : checkPB R D P = true := by
    have hT' := hT
    simp only [PolyTables3.check, Bool.and_eq_true, decide_eq_true_eq] at hT'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hT'
    have h7' : D.lineCells.all (R.lineOk D) = true := lineTest_all T D.noRay h7
    have h8' : capOkOf (mkCapOracle G₀ T.RP T.CP hrow hcol U) T.capCells T.G D.noRay = true :=
      capCheck3_imp T G₀ hV hrow hcol D.noRay h8
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

end CatalanCore.Uniform.Decay.Breakpoint
