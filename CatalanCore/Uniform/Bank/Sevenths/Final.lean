module

public import CatalanCore.Uniform.Bank.Sevenths.NV
public import CatalanCore.Uniform.Content.Shape.Reindex
public import CatalanCore.Measure.Scaling

@[expose] public section
set_option Elab.async false

/-! Conditional sevenths assembly on the new alternating family.
The content and decay suppliers remain explicit obligations. -/

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

/-- The exact content constant of the sevenths bank. -/
noncomputable def Lam7 : ℝ :=
  8926987763346083870538925313134246938568387 / 2458710375447819602863559629392237970329600 + (1 / 72) * Real.log 2

/-- The directed decay rate. -/
def D7 : ℚ := 2185487560184413390033 / 600000000000000000000

/-- The directed decay constant. -/
def c7 : ℚ := 7425954607455103 / 1000000000000000

theorem Lam7_lt_D7 : Lam7 < (D7 : ℝ) := by
  have h := Real.log_two_lt_d9
  unfold Lam7 D7
  push_cast
  nlinarith

/-- The exponent is below `70993/20`. -/
theorem sevenths_X_le :
    (1 : ℝ) * (c7 : ℝ) / ((D7 : ℝ) - Lam7) ≤ ((70993 / 20 : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  have hpos : 0 < (D7 : ℝ) - Lam7 := sub_pos.2 Lam7_lt_D7
  rw [one_mul, div_le_iff₀ hpos]
  unfold Lam7 D7 c7
  push_cast
  nlinarith

/-- **Measure of the sevenths block family.**  Content and decay as hypotheses. -/
theorem sevenths_measureLB (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : F7.selectionDepth Fr 2 ≤ depth)
    (hS : HasScaledContent ((F7.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) F7.scale Lam7)
    (hD : HasScaledDecay (F7.family Fr depth) F7.scale (D7 : ℝ) (c7 : ℝ)) :
    (F7.family Fr depth).MeasureLB ((70993 / 20 : ℚ) : ℝ) := by
  have hmass : (F7.common.mass : ℝ) = 1 := by rw [F7_common_mass]; norm_num
  have hc : (0 : ℝ) < (c7 : ℝ) := by unfold c7; norm_num
  have key := measure_of_family_nv0_even
    ((F7.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) F7.scale
    (γ := 1) (K := F7.common.n) hS
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) Lam7_lt_D7 hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := F7.degree_bound Fr depth n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := F7_nv0 Fr hd hw depth hdepth
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : F7.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  exact (Measure.MeasureLB_iff _ _).2
    (Measure.MeasureLBAt.mono sevenths_X_le ((Measure.MeasureLB_iff _ _).1 key))

/-- **Target transport.**  For a frame whose constant is `(-1/49)` times the target, the measure
statement for the family becomes the one for the target. -/
theorem sevenths_measure_of_const (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : F7.selectionDepth Fr 2 ≤ depth) {target : ℝ}
    (hconst : Fr.const = ((-1 / 49 : ℚ) : ℝ) * target)
    (hS : HasScaledContent ((F7.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) F7.scale Lam7)
    (hD : HasScaledDecay (F7.family Fr depth) F7.scale (D7 : ℝ) (c7 : ℝ)) :
    Measure.MeasureLBAt target ((70993 / 20 : ℚ) : ℝ) := by
  have h0 := (Measure.MeasureLB_iff _ _).1 (sevenths_measureLB Fr hd hw depth hdepth hS hD)
  have h' : Measure.MeasureLBAt Fr.const ((70993 / 20 : ℚ) : ℝ) := h0
  have he : target = ((-49 : ℚ) : ℝ) * Fr.const + ((0 : ℚ) : ℝ) := by
    rw [hconst]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) (-49) 0 (by norm_num)

end CatalanCore.Uniform.Bank.Sevenths
