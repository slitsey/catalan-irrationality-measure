import CatalanCore.Uniform.Bank.FifthsContent.Auto
import CatalanCore.Uniform.Bank.Fifths.Final
import CatalanCore.Uniform.Bank.Fifths.Frame
set_option Elab.async false

/-! # The fifths measures from the automatic content (lane C1L)

With the automatic content `Auto.fifthsK_content_auto` at `Λ_fin = bankData.Λ` (selection depth `≤ 64`,
`depth_le`) and the decay `HasScaledDecay (F5.family fifthsK (F5.selectionDepth fifthsK 2)) F5.scale D5 c5`, the
target bound `59983/2500` follows by `Auto.fifths_mu_le`.  The theorems are conditional only on the decay. -/

namespace CatalanCore.Uniform.Bank.FifthsContent.AutoMeasure
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Fifths
  CatalanCore.Uniform.Bank.FifthsContent.Auto

/-- The selection depth of the fifths geometry is at most `64` for a two-family frame. -/
theorem depth_le {Fr : Frame} (hd : Fr.d = 2) : F5.selectionDepth Fr 2 ≤ 64 := by
  unfold BlockGeom.selectionDepth
  rw [hd]
  decide +kernel

theorem lam_lt_D5 : ((bankData.Λ : ℚ) : ℝ) < (D5 : ℝ) := by
  have h : bankData.Λ < D5 := by rw [bankData_Λ]; unfold D5; norm_num
  exact_mod_cast h

theorem X_le : (1 : ℝ) * (c5 : ℝ) / ((D5 : ℝ) - (bankData.Λ : ℚ)) ≤ ((59983 / 2500 : ℚ) : ℝ) := by
  rw [one_mul]; exact fifths_mu_le

/-- The fifths measure of a frame with constant `(-1/25)` times the target, from the automatic content and the
decay at the selection depth. -/
theorem fifths_measure_auto (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) {target : ℝ}
    (hconst : Fr.const = ((-1 / 25 : ℚ) : ℝ) * target)
    (hS : HasScaledContent ((F5.family Fr (F5.selectionDepth Fr 2)).restrictAdm (fun i => i.1 % 2 = 0))
      F5.scale ((bankData.Λ : ℚ) : ℝ))
    (hD : HasScaledDecay (F5.family Fr (F5.selectionDepth Fr 2)) F5.scale (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt target ((59983 / 2500 : ℚ) : ℝ) := by
  have hmass : (F5.common.mass : ℝ) = 1 := by rw [F5_common_mass]; norm_num
  have hc : (0 : ℝ) < (c5 : ℝ) := by unfold c5; norm_num
  have key := measure_of_family_nv0_even
    ((F5.family Fr (F5.selectionDepth Fr 2)).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
    (γ := 1) (K := F5.common.n) hS
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) lam_lt_D5 hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := F5.degree_bound Fr (F5.selectionDepth Fr 2) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := F5_nv0 Fr hd hw (F5.selectionDepth Fr 2) le_rfl
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : F5.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  have h' : Measure.MeasureLBAt Fr.const ((59983 / 2500 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono X_le ((Measure.MeasureLB_iff _ _).1 key)
  have he : target = ((-25 : ℚ) : ℝ) * Fr.const + ((0 : ℚ) : ℝ) := by
    rw [hconst]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) (-25) 0 (by norm_num)

/-- **`μ(fifthsTarget 1) ≤ 59983/2500`**, conditional only on the decay. -/
theorem fifths1_measure_auto
    (hD : HasScaledDecay (F5.family fifths1 (F5.selectionDepth fifths1 2)) F5.scale (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 1) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_auto fifths1 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths1_const
    (fifths1_content_auto _ (depth_le rfl)) hD

/-- **`μ(fifthsTarget 2) ≤ 59983/2500`**, conditional only on the decay. -/
theorem fifths2_measure_auto
    (hD : HasScaledDecay (F5.family fifths2 (F5.selectionDepth fifths2 2)) F5.scale (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 2) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_auto fifths2 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths2_const
    (fifths2_content_auto _ (depth_le rfl)) hD

/-- **`μ(fifthsTarget 3) ≤ 59983/2500`**, conditional only on the decay. -/
theorem fifths3_measure_auto
    (hD : HasScaledDecay (F5.family fifths3 (F5.selectionDepth fifths3 2)) F5.scale (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 3) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_auto fifths3 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths3_const
    (fifths3_content_auto _ (depth_le rfl)) hD

/-- **`μ(fifthsTarget 4) ≤ 59983/2500`**, conditional only on the decay. -/
theorem fifths4_measure_auto
    (hD : HasScaledDecay (F5.family fifths4 (F5.selectionDepth fifths4 2)) F5.scale (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 4) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_auto fifths4 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) fifths4_const
    (fifths4_content_auto _ (depth_le rfl)) hD

#print axioms fifths1_measure_auto
#print axioms fifths2_measure_auto
#print axioms fifths3_measure_auto
#print axioms fifths4_measure_auto

end CatalanCore.Uniform.Bank.FifthsContent.AutoMeasure
