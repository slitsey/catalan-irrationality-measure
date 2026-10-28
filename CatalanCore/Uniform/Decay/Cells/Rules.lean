module

public import CatalanCore.Uniform.Decay.Cells.Facts

@[expose] public section

/-!
# Cell rules with a `basicOk` hypothesis, and the checker `checkB` (lane D, package D6)

D5 states the soundness of every cell rule for an arbitrary `SplineData`.  The concrete rules need
the elementary facts (`BasicFacts`: continuity and nonnegativity of the densities, radius,
`ε < 1`, ...), and re-running `basicOk` inside every cell would cost seconds per cell.
`CellRulesB` therefore states soundness *under* `D.basicOk = true`, and `checkB` runs `basicOk`
once.  `checkB_sound` has the same conclusion as D5's `check_sound`.
-/

namespace CatalanCore.Uniform.Decay.Cells

open Finset intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline

/-- Cell-level checkers whose soundness may assume `D.basicOk = true`. -/
structure CellRulesB (Vnu : ℂ → ℝ) where
  rayOk : SplineData → ℚ × ℚ → Bool
  lineOk : SplineData → ℚ × ℚ → Bool
  tailOk : SplineData → Bool
  capOk : SplineData → Bool
  energyOk : SplineData → Bool
  ray_sound : ∀ D, D.basicOk = true → ∀ p, rayOk D p = true → ∀ x y : ℝ,
    -(D.r0 : ℝ) - p.2 - D.W ≤ x → x ≤ -(D.r0 : ℝ) - p.1 + D.W → (D.sl : ℝ) * (p.1 : ℝ) ≤ y →
    y ≤ (D.sl : ℝ) * (p.2 : ℝ) →
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, y⟩
  line_sound : ∀ D, D.basicOk = true → ∀ p, lineOk D p = true → ∀ x : ℝ, (p.1 : ℝ) ≤ x →
    x ≤ p.2 → (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩
  tail_sound : ∀ D, D.basicOk = true → tailOk D = true → ∀ u δ : ℝ, (D.umax : ℝ) ≤ u →
    |δ| ≤ D.W →
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨-(D.r0 : ℝ) + δ - u, (D.sl : ℝ) * u⟩
  cap_sound : ∀ D, D.basicOk = true → capOk D = true →
    IntervalIntegrable
      (fun x : ℝ => min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0)
      volume (-(D.r0 : ℝ)) 0 ∧
    (D.Scap : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0,
      min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0
  energy_sound : ∀ D, D.basicOk = true → energyOk D = true → I0 D.A D.B D.f ≤ D.Ibound

/-- **The finite checker** (`basicOk` is run once). -/
def checkB {Vnu : ℂ → ℝ} (R : CellRulesB Vnu) (D : SplineData) : Bool :=
  D.basicOk && D.rayBoxes.all (R.rayOk D) && D.lineCells.all (R.lineOk D) && R.tailOk D &&
    R.capOk D && R.energyOk D

/-- **Soundness**: same conclusion as D5's `SplineData.check_sound`. -/
theorem checkB_sound {Vnu : ℂ → ℝ} {R : CellRulesB Vnu} {D : SplineData}
    (h : checkB R D = true) :
    SplineData.BasicFacts D ∧ ∃ C : SplineCertNu (D.sl : ℝ) D.Mq Vnu (D.ε : ℝ) D.A D.B D.f,
      C.r0 = D.r0 ∧ C.W = D.W ∧ C.umax = D.umax ∧ C.mprime = D.mprime ∧ C.gmin = D.gmin ∧
      C.Scap = D.Scap ∧ C.Ibound = D.Ibound ∧ C.ccert = D.ccert := by
  simp only [checkB, Bool.and_assoc, Bool.and_eq_true] at h
  obtain ⟨hb, hray, hline, htail, hcap, hen⟩ := h
  have B := SplineData.basicOk_sound hb
  refine ⟨B, ?_⟩
  obtain ⟨hci, hcs⟩ := R.cap_sound D hb hcap
  refine ⟨SplineCertNu.mk D.r0 D.W D.umax D.mprime D.gmin D.Scap D.Ibound D.ccert B.r0_pos B.W_pos
    D.rayBoxes (fun p hp => R.ray_sound D hb p (List.all_eq_true.1 hray p hp)) B.hray
    (R.tail_sound D hb htail) D.lineCells
    (fun p hp => R.line_sound D hb p (List.all_eq_true.1 hline p hp)) B.hline hci hcs
    (R.energy_sound D hb hen) B.hccert, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end CatalanCore.Uniform.Decay.Cells
