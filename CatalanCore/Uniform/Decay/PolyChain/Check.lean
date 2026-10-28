module

public import CatalanCore.Uniform.Decay.PolyChain.Bridge
public import CatalanCore.Uniform.Decay.Cert.Check
public import CatalanCore.Uniform.Decay.PolyChain.BasicP

@[expose] public section

/-!
# The polygon finite checker and its soundness (lane D, package D7)

Polygon analogue of D5's `CellRules` / `SplineData.check` / `check_sound`.  The rational data
are D5's `SplineData` (segments, Bernstein bounds, mass, conjugation, smoothing loss, line cells,
cap, energy, decay target: checked by `basicOkP`, which is `basicOk` without the ray cover)
together with a `RatPolygon P`.  The straight-ray fields of `SplineData` (`sl`, `umax`,
`rayBoxes`) are not used by the polygon chain.

`PolyCellRules Vnu` packages the cell-level checkers: the polygon tube rule (soundness: `g ≥ m'`
on the `W`-tube of `Γ`), line, cap and energy rules.  `checkP R D P` additionally checks
`P.OK` (`okB`) and `D.r0 = P.r0`.  `checkP_sound` gives `BasicFacts D`, `P.OK`, `D.r0 = P.r0`
and the polygon bridge certificate `SplineCertNuP`.
-/

namespace CatalanCore.Uniform.Decay.PolyChain

open Finset intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Polygon

/-- Cell-level checkers with soundness, polygon version. -/
structure PolyCellRules (Vnu : ℂ → ℝ) where
  tubeOk : SplineData → RatPolygon → Bool
  lineOk : SplineData → ℚ × ℚ → Bool
  capOk : SplineData → Bool
  energyOk : SplineData → Bool
  tube_sound : ∀ D P, tubeOk D P = true → ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ D.W →
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f (w + δ)
  line_sound : ∀ D p, lineOk D p = true → ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 →
    (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩
  cap_sound : ∀ D, capOk D = true →
    IntervalIntegrable (fun x : ℝ => min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0)
      volume (-(D.r0 : ℝ)) 0 ∧
    (D.Scap : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0,
      min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0
  energy_sound : ∀ D, energyOk D = true → I0 D.A D.B D.f ≤ D.Ibound

/-- Boolean admissibility test of a rational polygon. -/
def _root_.CatalanCore.Uniform.Decay.Polygon.RatPolygon.okB (P : RatPolygon) : Bool :=
  decide (0 < P.r0) && P.verts.all (fun p => decide (0 < p.2)) && decide (1 ≤ P.s)

theorem _root_.CatalanCore.Uniform.Decay.Polygon.RatPolygon.okB_sound {P : RatPolygon} (h : P.okB = true) : P.OK := by
  simp only [RatPolygon.okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

/-- **The polygon finite checker.** -/
def _root_.CatalanCore.Uniform.Decay.Cert.SplineData.checkP {Vnu : ℂ → ℝ} (R : PolyCellRules Vnu) (D : SplineData) (P : RatPolygon) : Bool :=
  D.basicOkP && P.okB && decide (D.r0 = P.r0) && R.tubeOk D P && D.lineCells.all (R.lineOk D) &&
    R.capOk D && R.energyOk D

/-- **Soundness of the polygon checker.** -/
theorem _root_.CatalanCore.Uniform.Decay.Cert.SplineData.checkP_sound {Vnu : ℂ → ℝ} {R : PolyCellRules Vnu} {D : SplineData} {P : RatPolygon}
    (h : D.checkP R P = true) :
    SplineData.BasicFactsP D ∧ P.OK ∧ D.r0 = P.r0 ∧
      ∃ C : SplineCertNuP P D.Mq Vnu (D.ε : ℝ) D.A D.B D.f,
        C.W = D.W ∧ C.mprime = D.mprime ∧ C.gmin = D.gmin ∧
        C.Scap = D.Scap ∧ C.Ibound = D.Ibound ∧ C.ccert = D.ccert := by
  simp only [SplineData.checkP, Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hb, hok, hr0, htube, hline, hcap, hen⟩ := h
  have B := SplineData.basicOkP_sound hb
  refine ⟨B, RatPolygon.okB_sound hok, hr0, ?_⟩
  obtain ⟨hci, hcs⟩ := R.cap_sound D hcap
  rw [hr0] at hci hcs
  exact ⟨SplineCertNuP.mk D.W D.mprime D.gmin D.Scap D.Ibound D.ccert B.W_pos
    (R.tube_sound D P htube) D.lineCells
    (fun p hp => R.line_sound D p (List.all_eq_true.1 hline p hp)) B.hline hci hcs
    (R.energy_sound D hen) B.hccert, rfl, rfl, rfl, rfl, rfl, rfl⟩

end CatalanCore.Uniform.Decay.PolyChain
