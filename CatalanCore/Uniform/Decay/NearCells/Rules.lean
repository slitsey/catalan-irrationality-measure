import CatalanCore.Uniform.Decay.NearCells.Edge
import CatalanCore.Uniform.Decay.Cells.Cap
set_option Elab.async false

/-!
# Near-tube, line and cap-upper oracles (lane D, package D6b)

All built from the generic edge-parameter rule.  `NearParams` holds the (untrusted) cell data and
the global tuning (`n`, `Rtwo`, `eW`, `eP`); the second potential is `nuPot nu`.

* `tubeChainOkD` / `tubeChainOkD_sound`: the finite-chain half of `PolyCellRules.tube_sound`.
* `lineOkD` / `lineOkD_sound`: exactly the shape of `PolyCellRules.line_sound`.
* `ubOkD` / `ubOkD_sound`: cap cells `g ≤ ub` (the `CapOracle.ubOk` / `ub_sound` shape).
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.Cells

structure NearParams where
  nu : List Seg
  n : ℕ
  Rtwo : ℚ
  eW : ℕ
  eP : ℕ
  tube : List (List NCell)
  line : List NCell
  capUb : List NCell

def cpiOf (D : SplineData) : ℚ := (1 - D.ε) * piLo

theorem gNu_ge_of (D : SplineData) (nu : List Seg) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot nu z)
    (hε : D.ε < 1) {m' : ℚ} {z : ℂ}
    (h : (m' : ℝ) ≤ -((cellPieces D nu).map (fun P => (P.w : ℝ) * PhiW P z)).sum
      + (cpiOf D : ℝ) * |z.im|) :
    (m' : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f z := by
  rw [gNu_eq D nu hV]
  have hε1 : (D.ε : ℝ) < 1 := by exact_mod_cast hε
  have hcp : (cpiOf D : ℝ) * |z.im| ≤ (1 - (D.ε : ℝ)) * Real.pi * |z.im| := by
    unfold cpiOf; push_cast
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left piLo_lt.le (by linarith)
  linarith

/-- The tube over the finite polygon chain. -/
def tubeChainOkD (prm : NearParams) (D : SplineData) (P : RatPolygon) : Bool :=
  decide (D.ε < 1) &&
    chainEdgesOk prm.n (cellPieces D prm.nu) D.W prm.Rtwo (cpiOf D) D.mprime prm.eW prm.eP
      ⟨-P.r0, 0⟩ (P.verts.map fun p => ⟨p.1, p.2⟩) prm.tube

theorem tubeChainOkD_sound (prm : NearParams) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot prm.nu z)
    (D : SplineData) (P : RatPolygon) (h : tubeChainOkD prm D P = true) :
    ∀ w ∈ chainSet (((-(P.r0 : ℝ)) : ℝ) : ℂ) (P.verts.map vertC), ∀ δ : ℝ, |δ| ≤ D.W →
      (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + (δ : ℂ)) := by
  simp only [tubeChainOkD, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hε, hch⟩ := h
  intro w hw δ hδ
  have ha : (⟨-P.r0, 0⟩ : CQ).toC = (((-(P.r0 : ℝ)) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [CQ.toC]
  have hvs : (P.verts.map fun p => (⟨p.1, p.2⟩ : CQ)).map CQ.toC = P.verts.map vertC := by
    rw [List.map_map]; rfl
  have key := chainEdgesOk_sound _ _ _ hch w (by rw [ha, hvs]; exact hw) δ hδ
  exact gNu_ge_of D prm.nu hV hε key

def findCell (t : List NCell) (a b : ℚ) : Option (Option (ℚ × List ℚ × ℚ)) :=
  (t.find? fun c => decide (c.1 = a ∧ c.2.1 = b)).map fun c => c.2.2

theorem findCell_some {t : List NCell} {a b : ℚ} {lo : Option (ℚ × List ℚ × ℚ)} (h : findCell t a b = some lo) :
    ∃ c ∈ t, c.1 = a ∧ c.2.1 = b ∧ c.2.2 = lo := by
  unfold findCell at h
  cases hf : t.find? (fun c => decide (c.1 = a ∧ c.2.1 = b)) with
  | none => rw [hf] at h; simp at h
  | some c =>
    rw [hf] at h
    simp at h
    have := List.find?_some hf
    simp only [decide_eq_true_eq] at this
    exact ⟨c, List.mem_of_find?_eq_some hf, this.1, this.2, h⟩

/-- Line cells: `g(x, 0) ≥ gmin` on `[p.1, p.2]`. -/
def lineOkD (prm : NearParams) (D : SplineData) (p : ℚ × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    match findCell prm.line p.1 p.2 with
    | some lo => oneCellOk prm.n (cellPieces D prm.nu) ⟨(p.1 + p.2) / 2, 0⟩ ⟨1, 0⟩
        ((p.2 - p.1) / 2) D.W prm.Rtwo (cpiOf D) D.gmin prm.eW prm.eP lo
    | none => false

theorem lineOkD_sound (prm : NearParams) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot prm.nu z)
    (D : SplineData) (p : ℚ × ℚ) (h : lineOkD prm D p = true) :
    ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 →
      (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ := by
  intro x hx1 hx2
  unfold lineOkD at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  split at hm
  · rename_i lo hlo
    have hW' : (0 : ℝ) ≤ D.W := by exact_mod_cast hW
    have key := oneCellOk_sound hm (x - (((p.1 + p.2) / 2 : ℚ) : ℝ)) 0 (by
      rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hW')
    have hz : (⟨((p.1 + p.2) / 2 : ℚ), 0⟩ : CQ).toC + ((x - (((p.1 + p.2) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
        (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨x, 0⟩ := by
      apply Complex.ext <;> simp [CQ.toC]
    rw [hz] at key
    exact gNu_ge_of D prm.nu hV hε key
  · cases hm

/-- Negated weights: lower bounds of `-g` are upper bounds of `g`. -/
def negPieces (ps : List WP) : List WP := ps.map fun P => { P with w := -P.w }

theorem negPieces_sum (ps : List WP) (z : ℂ) :
    ((negPieces ps).map (fun P => (P.w : ℝ) * PhiW P z)).sum
      = -(ps.map (fun P => (P.w : ℝ) * PhiW P z)).sum := by
  induction ps with
  | nil => simp [negPieces]
  | cons P ps ih =>
    simp only [negPieces, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [PhiW]
    push_cast; ring

/-- Cap cells: `g(x, 0) ≤ ub` on `[a, b]` (jet or endpoint data from the table). -/
def ubOkD (prm : NearParams) (D : SplineData) (c : ℚ × ℚ × ℚ) : Bool :=
  decide (D.ε < 1) && decide (0 ≤ D.W) &&
    match findCell prm.capUb c.1 c.2.1 with
    | some lo => oneCellOk prm.n (negPieces (cellPieces D prm.nu)) ⟨(c.1 + c.2.1) / 2, 0⟩ ⟨1, 0⟩
        ((c.2.1 - c.1) / 2) D.W prm.Rtwo 0 (-c.2.2) prm.eW prm.eP lo
    | none => false

theorem ubOkD_sound (prm : NearParams) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot prm.nu z)
    (D : SplineData) (c : ℚ × ℚ × ℚ) (h : ubOkD prm D c = true) :
    ∀ x : ℝ, (c.1 : ℝ) ≤ x → x ≤ c.2.1 →
      gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ c.2.2 := by
  intro x hx1 hx2
  unfold ubOkD at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hε, hW⟩, hm⟩ := h
  split at hm
  · rename_i lo hlo
    have hW' : (0 : ℝ) ≤ D.W := by exact_mod_cast hW
    have key := oneCellOk_sound hm (x - (((c.1 + c.2.1) / 2 : ℚ) : ℝ)) 0 (by
      rw [abs_le]; push_cast; constructor <;> linarith) (by simpa using hW')
    have hz : (⟨((c.1 + c.2.1) / 2 : ℚ), 0⟩ : CQ).toC + ((x - (((c.1 + c.2.1) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
        (⟨1, 0⟩ : CQ).toC + ((0 : ℝ) : ℂ) = ⟨x, 0⟩ := by
      apply Complex.ext <;> simp [CQ.toC]
    rw [hz, negPieces_sum] at key
    rw [gNu_eq D prm.nu hV]
    push_cast at key
    simp at key ⊢
    linarith
  · cases hm

end CatalanCore.Uniform.Decay.NearCells
