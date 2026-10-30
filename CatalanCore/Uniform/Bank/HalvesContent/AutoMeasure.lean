import CatalanCore.Uniform.Bank.HalvesContent.Auto
import CatalanCore.Uniform.Bank.Halves.Final
import CatalanCore.Uniform.Bank.Halves.Frame
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.HalvesContent.AutoMeasure
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Halves
  CatalanCore.Uniform.Bank.HalvesContent.Auto

theorem depth_le {Fr : Frame} (hd : Fr.d = 2) : FH.selectionDepth Fr 2 ≤ 64 := by
  unfold BlockGeom.selectionDepth
  rw [hd]
  decide +kernel

theorem halves_measure_at (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) {target : ℝ}
    (hconst : Fr.const = ((-1 / 12 : ℚ) : ℝ) * target)
    (hS : HasScaledContent ((FH.family Fr (FH.selectionDepth Fr 2)).restrictAdm (fun i => i.1 % 2 = 0))
      FH.scale ((bankData.Λ : ℚ) : ℝ))
    (D : ℚ) (hΛD : bankData.Λ < D) (hμ : cH ≤ 65253 / 10000 * (D - bankData.Λ))
    (hD : HasScaledDecay (FH.family Fr (FH.selectionDepth Fr 2)) FH.scale (D : ℝ) (cH : ℝ)) :
    Measure.MeasureLBAt target ((65253 / 10000 : ℚ) : ℝ) := by
  have hlam : ((bankData.Λ : ℚ) : ℝ) < (D : ℝ) := by exact_mod_cast hΛD
  have hX : (1 : ℝ) * (cH : ℝ) / ((D : ℝ) - (bankData.Λ : ℚ)) ≤ ((65253 / 10000 : ℚ) : ℝ) := by
    have hpos : (0 : ℝ) < (D : ℝ) - (bankData.Λ : ℝ) := by linarith
    rw [one_mul, div_le_iff₀ hpos]
    have h3 := (Rat.cast_le (K := ℝ)).2 hμ
    push_cast at h3 ⊢
    linarith
  have hmass : (FH.common.mass : ℝ) = 1 := by rw [FH_common_mass]; norm_num
  have hc : (0 : ℝ) < (cH : ℝ) := by unfold cH; norm_num
  have key := measure_of_family_nv0_even
    ((FH.family Fr (FH.selectionDepth Fr 2)).restrictAdm (fun i => i.1 % 2 = 0)) FH.scale
    (γ := 1) (K := FH.common.n) hS
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) hlam hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := FH.degree_bound Fr (FH.selectionDepth Fr 2) n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := FH_nv0 Fr hd hw (FH.selectionDepth Fr 2) le_rfl
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
      exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : FH.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  have h' : Measure.MeasureLBAt Fr.const ((65253 / 10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono hX ((Measure.MeasureLB_iff _ _).1 key)
  have he : target = ((-12 : ℚ) : ℝ) * Fr.const + ((0 : ℚ) : ℝ) := by
    rw [hconst]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) (-12) 0 (by norm_num)


end CatalanCore.Uniform.Bank.HalvesContent.AutoMeasure
