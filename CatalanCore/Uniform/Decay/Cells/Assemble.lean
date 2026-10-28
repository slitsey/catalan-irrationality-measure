module

public import CatalanCore.Uniform.Decay.Cells.Far
public import CatalanCore.Uniform.Decay.Cells.Cap
public import CatalanCore.Uniform.Decay.Cells.Energy

@[expose] public section

/-!
# Assembly of the cell rules (lane D, package D6)

`mkRules` builds a `CellRulesB Vnu` from
* the far/tail rule (`Far`, proved from the mass-cancellation hypothesis `FarHyp`),
* a near-cell oracle for the ray and line cells that are not far (`NearOracle`),
* the cap rule (`Cap`, proved; oracles: cell upper bounds and `∫ g` lower bound),
* the energy rule (`Energy`, proved decomposition; oracle: pair-energy upper bounds).
`mkRules_check_sound` is `checkB_sound` for these rules.
-/

namespace CatalanCore.Uniform.Decay.Cells

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline

/-- Oracle for the potential cells that are not far: ray cells and line cells. -/
structure NearOracle (Vnu : ℂ → ℝ) where
  rayNear : SplineData → ℚ × ℚ → Bool
  lineOk : SplineData → ℚ × ℚ → Bool
  ray_sound : ∀ D : SplineData, D.basicOk = true → ∀ p, rayNear D p = true → ∀ x y : ℝ,
    -(D.r0 : ℝ) - p.2 - D.W ≤ x → x ≤ -(D.r0 : ℝ) - p.1 + D.W → (D.sl : ℝ) * (p.1 : ℝ) ≤ y →
    y ≤ (D.sl : ℝ) * (p.2 : ℝ) →
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, y⟩
  line_sound : ∀ D : SplineData, D.basicOk = true → ∀ p, lineOk D p = true → ∀ x : ℝ,
    (p.1 : ℝ) ≤ x → x ≤ p.2 → (D.gmin : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩

/-- The concrete cell rules. -/
def mkRules {Vnu : ℂ → ℝ} (F : FarData) (hfar : ∀ D : SplineData, D.basicOk = true → FarHyp D Vnu F)
    (N : NearOracle Vnu) (O : CapOracle Vnu) (cells : List CapCell) (G : ℚ) (P : PairOracle)
    (E : List (List ℚ)) : CellRulesB Vnu where
  rayOk D p := rayFarOk D F p || N.rayNear D p
  lineOk := N.lineOk
  tailOk D := tailFarOk D F
  capOk := capOkOf O cells G
  energyOk := energyOkOf P E
  ray_sound D hb p h x y _ _ hy1 hy2 := by
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact rayFar_sound (hfar D hb) (SplineData.basicOk_sound hb) h x y hy1
    · exact N.ray_sound D hb p h x y ‹_› ‹_› hy1 hy2
  line_sound D hb p h x h1 h2 := N.line_sound D hb p h x h1 h2
  tail_sound D hb h u δ hu _ := tailFar_sound (hfar D hb) (SplineData.basicOk_sound hb) h u δ hu
  cap_sound D hb h := capOkOf_sound O cells G D hb h
  energy_sound D hb h := energyOkOf_sound P E D hb h

end CatalanCore.Uniform.Decay.Cells
