import CatalanCore.Uniform.Decay.NearCells.Point
import CatalanCore.Uniform.Decay.PolyChain.Check
set_option Elab.async false

/-!
# Tube cells along polygon edges, and line cells (lane D, package D6b)

A cell of an edge `[a, b]` is `(ulo, uhi, lo)` with `lo = some l` a jet cell (`cellOk`, Bernstein
lower bound `l`) and `lo = none` an endpoint cell (`ptOk`).  `edgeOk` covers the edge parameter
`u ∈ [0,1]`; `chainEdgesOk` runs over the finite polygon.  The soundness statements are the
`chainSet` half of `PolyCellRules.tube_sound`.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Assembly

abbrev NCell := ℚ × ℚ × Option (ℚ × List ℚ × ℚ)

def edgeCentre (a b : CQ) (ulo uhi : ℚ) : CQ :=
  CQ.add a (CQ.smul ((ulo + uhi) / 2) (CQ.sub b a))

/-- Radius bound of a cell: `h (|dd.re| + |dd.im|) + W`. -/
def cellRadius (dd : CQ) (h W : ℚ) : ℚ := h * (|dd.re| + |dd.im|) + W

/-- One cell with centre `zc`, direction `dd`, half-width `h`. -/
def oneCellOk (n : ℕ) (ps : List WP) (zc dd : CQ) (h W Rtwo cpi m' : ℚ) (eW eP : ℕ)
    (lo : Option (ℚ × List ℚ × ℚ)) : Bool :=
  match lo with
  | some l => cellOk n ps zc dd h W Rtwo cpi l.1 m' l.2.1 l.2.2 eW eP
  | none => ptOk n ps zc (cellRadius dd h W) Rtwo cpi m' eW eP

theorem oneCellOk_sound {n : ℕ} {ps : List WP} {zc dd : CQ} {h W Rtwo cpi m' : ℚ} {eW eP : ℕ}
    {lo : Option (ℚ × List ℚ × ℚ)} (hc : oneCellOk n ps zc dd h W Rtwo cpi m' eW eP lo = true) (s δ : ℝ)
    (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
        PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  unfold oneCellOk at hc
  split at hc
  · exact cellOk_sound hc s δ hs hδ
  · refine ptOk_sound hc _ ?_
    have : zc.toC + (s : ℂ) * dd.toC + (δ : ℂ) - zc.toC = (s : ℂ) * dd.toC + (δ : ℂ) := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    unfold cellRadius
    push_cast
    have h1 : ‖dd.toC‖ ≤ |(dd.re : ℝ)| + |(dd.im : ℝ)| := Complex.norm_le_abs_re_add_abs_im _
    have h2 : |s| * ‖dd.toC‖ ≤ h * (|(dd.re : ℝ)| + |(dd.im : ℝ)|) :=
      mul_le_mul hs h1 (norm_nonneg _) (by exact_mod_cast (le_trans (abs_nonneg _) hs))
    linarith [hδ]

/-- One polygon edge covered by cells. -/
def edgeOk (n : ℕ) (ps : List WP) (a b : CQ) (W Rtwo cpi m' : ℚ) (eW eP : ℕ)
    (cells : List NCell) : Bool :=
  coverOk 0 1 (cells.map fun c => (c.1, c.2.1)) &&
    cells.all fun c =>
      oneCellOk n ps (edgeCentre a b c.1 c.2.1) (CQ.sub b a) ((c.2.1 - c.1) / 2) W Rtwo cpi m'
        eW eP c.2.2

theorem edgeOk_sound {n : ℕ} {ps : List WP} {a b : CQ} {W Rtwo cpi m' : ℚ} {eW eP : ℕ}
    {cells : List NCell} (h : edgeOk n ps a b W Rtwo cpi m' eW eP cells = true)
    (u δ : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
        PhiW P (a.toC + (u : ℂ) * (b.toC - a.toC) + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(a.toC + (u : ℂ) * (b.toC - a.toC) + (δ : ℂ)).im| := by
  simp only [edgeOk, Bool.and_eq_true] at h
  obtain ⟨hcov, hall⟩ := h
  obtain ⟨p, hp, hp1, hp2⟩ := coverOk_sound hcov u (by simpa using hu0) (by simpa using hu1)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
  have hcell := List.all_eq_true.1 hall c hc
  have key := oneCellOk_sound hcell (u - (((c.1 + c.2.1) / 2 : ℚ) : ℝ)) δ (by
    rw [abs_le]; push_cast at *; constructor <;> nlinarith [hp1, hp2]) hδ
  have e : (edgeCentre a b c.1 c.2.1).toC + ((u - (((c.1 + c.2.1) / 2 : ℚ) : ℝ) : ℝ) : ℂ) *
      (CQ.sub b a).toC = a.toC + (u : ℂ) * (b.toC - a.toC) := by
    unfold edgeCentre
    rw [CQ.toC_add, CQ.toC_smul, CQ.toC_sub]
    push_cast; ring
  rw [e] at key
  exact key

/-- Assembly from per-cell facts (one kernel declaration per cell). -/
theorem edgeOk_of {n : ℕ} {ps : List WP} {a b : CQ} {W Rtwo cpi m' : ℚ} {eW eP : ℕ}
    {cells : List NCell}
    (hcov : coverOk 0 1 (cells.map fun c => (c.1, c.2.1)) = true)
    (hall : ∀ c ∈ cells, oneCellOk n ps (edgeCentre a b c.1 c.2.1) (CQ.sub b a)
      ((c.2.1 - c.1) / 2) W Rtwo cpi m' eW eP c.2.2 = true) :
    edgeOk n ps a b W Rtwo cpi m' eW eP cells = true := by
  simp only [edgeOk, Bool.and_eq_true]
  exact ⟨hcov, List.all_eq_true.2 hall⟩

/-- The finite polygon chain `a → v₁ → v₂ → …`. -/
def chainEdgesOk (n : ℕ) (ps : List WP) (W Rtwo cpi m' : ℚ) (eW eP : ℕ) :
    CQ → List CQ → List (List NCell) → Bool
  | _, [], [] => true
  | a, b :: vs, cs :: rest =>
    edgeOk n ps a b W Rtwo cpi m' eW eP cs && chainEdgesOk n ps W Rtwo cpi m' eW eP b vs rest
  | _, _, _ => false

theorem chainEdgesOk_sound {n : ℕ} {ps : List WP} {W Rtwo cpi m' : ℚ} {eW eP : ℕ} :
    ∀ (vs : List CQ) (a : CQ) (cells : List (List NCell)),
    chainEdgesOk n ps W Rtwo cpi m' eW eP a vs cells = true →
    ∀ w ∈ chainSet a.toC (vs.map CQ.toC), ∀ δ : ℝ, |δ| ≤ W →
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (w + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(w + (δ : ℂ)).im| := by
  intro vs
  induction vs with
  | nil =>
    intro a cells _ w hw
    simp [chainSet] at hw
  | cons b vs ih =>
    intro a cells h w hw δ hδ
    cases cells with
    | nil => simp [chainEdgesOk] at h
    | cons cs rest =>
      simp only [chainEdgesOk, Bool.and_eq_true] at h
      simp only [List.map_cons, chainSet, Set.mem_union] at hw
      rcases hw with hw | hw
      · rw [segment_eq_image'] at hw
        obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := hw
        have := edgeOk_sound h.1 u δ hu0 hu1 hδ
        simpa [smul_eq_mul, Complex.real_smul] using this
      · exact ih b rest h.2 w hw δ hδ

end CatalanCore.Uniform.Decay.NearCells
