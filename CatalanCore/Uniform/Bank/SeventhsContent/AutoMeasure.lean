import CatalanCore.Uniform.Bank.SeventhsContent.Auto
import CatalanCore.Uniform.Bank.Sevenths.Final
import CatalanCore.Uniform.Bank.Sevenths.Frame
set_option Elab.async false

/-! # The sevenths measures from the automatic content (lane C1L)

With the automatic content `Auto.sevenths_content_auto a` at `Λ_fin = bankData.Λ` (selection depth `≤ 64`,
`depth_le`) and the decay
`HasScaledDecay (F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2)) F7.scale D7 c7`, the
target bound `2801` follows by `Auto.sevenths_mu_le`.  The theorem is conditional only on the
decay. -/

namespace CatalanCore.Uniform.Bank.SeventhsContent.AutoMeasure
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Sevenths
  CatalanCore.Uniform.Bank.SeventhsContent.Auto

/-- The selection depth of the sevenths geometry is at most `64` for a two-family frame. -/
theorem depth_le {Fr : Frame} (hd : Fr.d = 2) : F7.selectionDepth Fr 2 ≤ 64 := by
  unfold BlockGeom.selectionDepth
  rw [hd]
  decide +kernel

theorem lam_lt_D7 : ((bankData.Λ : ℚ) : ℝ) < (D7 : ℝ) := by
  have h : bankData.Λ < D7 := by rw [bankData_Λ]; unfold D7; norm_num
  exact_mod_cast h

theorem X_le : (1 : ℝ) * (c7 : ℝ) / ((D7 : ℝ) - (bankData.Λ : ℚ)) ≤ ((2801 : ℚ) : ℝ) := by
  rw [one_mul]; exact sevenths_mu_le

/-- **`μ(seventhsTarget (a + 1)) ≤ 2801`** for each of the six members, conditional only on the decay. -/
theorem sevenths_measure_auto (a : Fin 6)
    (hD : HasScaledDecay (F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2)) F7.scale
      (D7 : ℝ) (c7 : ℝ)) :
    Measure.MeasureLBAt (seventhsTarget (seventhNumerator a)) ((2801 : ℚ) : ℝ) := by
  have hmass : (F7.common.mass : ℝ) = 1 := by rw [F7_common_mass]; norm_num
  have hc : (0 : ℝ) < (c7 : ℝ) := by unfold c7; norm_num
  have hd2 : (seventhsFrameAt a).d = 2 := rfl
  have key := measure_of_family_nv0_even
    ((F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2)).restrictAdm (fun i => i.1 % 2 = 0)) F7.scale
    (γ := 1) (K := F7.common.n) (sevenths_content_auto a _ (depth_le hd2))
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) lam_lt_D7 hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := F7.degree_bound (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := F7_nv0 (seventhsFrameAt a) (by rw [hd2]; norm_num) (seventhsFrameAt_w_ne a) (F7.selectionDepth (seventhsFrameAt a) 2) le_rfl
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : F7.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  have h' : Measure.MeasureLBAt (seventhsFrameAt a).const ((2801 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono X_le ((Measure.MeasureLB_iff _ _).1 key)
  have he : seventhsTarget (seventhNumerator a) = ((-49 : ℚ) : ℝ) * (seventhsFrameAt a).const + ((0 : ℚ) : ℝ) := by
    rw [seventhsFrameAt_const a]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) (-49) 0 (by norm_num)

#print axioms sevenths_measure_auto

end CatalanCore.Uniform.Bank.SeventhsContent.AutoMeasure
