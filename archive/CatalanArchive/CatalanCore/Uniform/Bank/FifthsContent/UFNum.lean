import CatalanCore.Uniform.Bank.FifthsContent.FullUF
import CatalanCore.Uniform.Bank.Fifths.Final
set_option Elab.async false

/-! # Fifths with UF: the finite-template numerical assembly (lane B, B5c)

`LamFinU` is the content constant of the finite no-UF template (sawtooth prefix cut at `1/900`, the
exact strict envelope `min(T,R,LP,M3D)` per prime class).  It exceeds the exact strict no-UF constant
by about `1.4e-7`, and `c5/(D5 - LamFinU) <= 243052/10000` (exact 24.30517...). -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Fifths

theorem LamFinU_lt_D5 : (LamFinU : ℝ) < (D5 : ℝ) := by
  unfold LamFinU D5
  push_cast
  norm_num

theorem finiteU_X_le :
    (1 : ℝ) * (c5 : ℝ) / ((D5 : ℝ) - (LamFinU : ℝ)) ≤ ((59983 / 2500 : ℚ) : ℝ) := by
  have hpos : 0 < (D5 : ℝ) - (LamFinU : ℝ) := sub_pos.2 LamFinU_lt_D5
  rw [one_mul, div_le_iff₀ hpos]
  unfold LamFinU D5 c5
  push_cast
  norm_num

/-- **Measure of the fifths block family without UF.**  Content (at the finite constant) and decay as
hypotheses. -/
theorem fifths_UF_measureLB (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : F5.selectionDepth Fr 2 ≤ depth)
    (hS : HasScaledContent ((F5.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
      (LamFinU : ℝ))
    (hD : HasScaledDecay (F5.family Fr depth) F5.scale (D5 : ℝ) (c5 : ℝ)) :
    (F5.family Fr depth).MeasureLB ((59983 / 2500 : ℚ) : ℝ) := by
  have hmass : (F5.common.mass : ℝ) = 1 := by rw [F5_common_mass]; norm_num
  have hc : (0 : ℝ) < (c5 : ℝ) := by unfold c5; norm_num
  have key := measure_of_family_nv0_even
    ((F5.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
    (γ := 1) (K := F5.common.n) hS
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) LamFinU_lt_D5 hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := F5.degree_bound Fr depth n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := F5_nv0 Fr hd hw depth hdepth
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : F5.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  exact (Measure.MeasureLB_iff _ _).2
    (Measure.MeasureLBAt.mono finiteU_X_le ((Measure.MeasureLB_iff _ _).1 key))

/-- **Target transport (no UF).** -/
theorem fifths_UF_measure_of_const (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0)
    (depth : ℕ) (hdepth : F5.selectionDepth Fr 2 ≤ depth) {target : ℝ}
    (hconst : Fr.const = ((-1 / 25 : ℚ) : ℝ) * target)
    (hS : HasScaledContent ((F5.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
      (LamFinU : ℝ))
    (hD : HasScaledDecay (F5.family Fr depth) F5.scale (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt target ((59983 / 2500 : ℚ) : ℝ) := by
  have h0 := (Measure.MeasureLB_iff _ _).1 (fifths_UF_measureLB Fr hd hw depth hdepth hS hD)
  have h' : Measure.MeasureLBAt Fr.const ((59983 / 2500 : ℚ) : ℝ) := h0
  have he : target = ((-25 : ℚ) : ℝ) * Fr.const + ((0 : ℚ) : ℝ) := by
    rw [hconst]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) (-25) 0 (by norm_num)

#print axioms fifths_UF_measureLB
#print axioms fifths_UF_measure_of_const
end CatalanCore.Uniform.Bank.FifthsContent
