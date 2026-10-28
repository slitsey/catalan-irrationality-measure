module

public import CatalanCore.Uniform.Decay.Cert.Basic
public import CatalanCore.Uniform.Decay.Cert.BridgeNu

@[expose] public section

/-!
# The finite checker `SplineData.check` and its soundness (lane D, package D5)

`CellRules Vnu` packages the *cell-level* Boolean checks (ray box, line cell, tail, cap integral,
exact energy) together with their soundness statements about the exact hybrid function
`gNu M Vnu ε σ`.  The elementary obligations (Bernstein bounds, exact mass, conjugation, radius,
smoothing loss, covers, decay target) are checked by `basicOk` and proved sound in `Basic`.

`SplineData.check R D` is the conjunction; `check_sound` produces the `SplineCertNu` of the
bridge together with the `BasicFacts`.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Spline

/-- Cell-level checkers with soundness, for the second potential `Vnu`. -/
structure CellRules (Vnu : ℂ → ℝ) where
  rayOk : SplineData → ℚ × ℚ → Bool
  lineOk : SplineData → ℚ × ℚ → Bool
  tailOk : SplineData → Bool
  capOk : SplineData → Bool
  energyOk : SplineData → Bool
  ray_sound : ∀ D p, rayOk D p = true → ∀ x y : ℝ, -(D.r0 : ℝ) - p.2 - D.W ≤ x →
    x ≤ -(D.r0 : ℝ) - p.1 + D.W → (D.sl : ℝ) * (p.1 : ℝ) ≤ y → y ≤ (D.sl : ℝ) * (p.2 : ℝ) →
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, y⟩
  line_sound : ∀ D p, lineOk D p = true → ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 →
    (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩
  tail_sound : ∀ D, tailOk D = true → ∀ u δ : ℝ, (D.umax : ℝ) ≤ u → |δ| ≤ D.W →
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨-(D.r0 : ℝ) + δ - u, (D.sl : ℝ) * u⟩
  cap_sound : ∀ D, capOk D = true →
    IntervalIntegrable (fun x : ℝ => min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0)
      volume (-(D.r0 : ℝ)) 0 ∧
    (D.Scap : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0,
      min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0
  energy_sound : ∀ D, energyOk D = true → I0 D.A D.B D.f ≤ D.Ibound

namespace SplineData

/-- **The finite checker.** -/
def check {Vnu : ℂ → ℝ} (R : CellRules Vnu) (D : SplineData) : Bool :=
  D.basicOk && D.rayBoxes.all (R.rayOk D) && D.lineCells.all (R.lineOk D) && R.tailOk D &&
    R.capOk D && R.energyOk D

/-- **Soundness of the checker**: `check = true` yields the bridge certificate. -/
theorem check_sound {Vnu : ℂ → ℝ} {R : CellRules Vnu} {D : SplineData}
    (h : D.check R = true) :
    BasicFacts D ∧ ∃ C : SplineCertNu (D.sl : ℝ) D.Mq Vnu (D.ε : ℝ) D.A D.B D.f,
      C.r0 = D.r0 ∧ C.W = D.W ∧ C.umax = D.umax ∧ C.mprime = D.mprime ∧ C.gmin = D.gmin ∧
      C.Scap = D.Scap ∧ C.Ibound = D.Ibound ∧ C.ccert = D.ccert := by
  simp only [check, Bool.and_assoc, Bool.and_eq_true] at h
  obtain ⟨hb, hray, hline, htail, hcap, hen⟩ := h
  have B := basicOk_sound hb
  refine ⟨B, ?_⟩
  obtain ⟨hci, hcs⟩ := R.cap_sound D hcap
  refine ⟨SplineCertNu.mk D.r0 D.W D.umax D.mprime D.gmin D.Scap D.Ibound D.ccert B.r0_pos B.W_pos
    D.rayBoxes (fun p hp => R.ray_sound D p (List.all_eq_true.1 hray p hp)) B.hray
    (R.tail_sound D htail) D.lineCells
    (fun p hp => R.line_sound D p (List.all_eq_true.1 hline p hp)) B.hline hci hcs
    (R.energy_sound D hen) B.hccert, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SplineData

end CatalanCore.Uniform.Decay.Cert
