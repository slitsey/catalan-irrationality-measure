module

public import CatalanCore.Uniform.Bank.Fifths.NV
public import CatalanCore.Uniform.Content.Shape.Reindex
public import CatalanCore.Measure.Scaling

@[expose] public section
set_option Elab.async false

/-! # Terminal assembly of the fifths bank (lane B, B5)

For the new family `F5 = altGeom (2/9)` and any frame `Fr` with nonzero weights, the two
provider statements

* `HasScaledContent ((F5.family Fr depth).restrictAdm even) F5.scale Lam5`  (spec contract 7),
* `HasScaledDecay (F5.family Fr depth) F5.scale D5 c5`                      (spec contract 8),

with the exact rationals of SPEC-fifths, give `μ(Fr.const) ≤ 59983/2500`.  Here
`Lam5 = 18614248183031951531578379/5321679222691225544230080 + (2/81) log 2`,
`D5 = 4826561916291581150063627/1265625000000000000000000`, `c5 = 2239239458955067/312500000000000`,
and `c5/(D5 - Lam5) = 23.99316846…`. -/

namespace CatalanCore.Uniform.Bank.Fifths
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

/-- The exact content constant of the fifths bank. -/
noncomputable def Lam5 : ℝ :=
  18614248183031951531578379 / 5321679222691225544230080 + (2 / 81) * Real.log 2

/-- The directed decay rate. -/
def D5 : ℚ := 4826561916291581150063627 / 1265625000000000000000000

/-- The directed decay constant. -/
def c5 : ℚ := 2239239458955067 / 312500000000000

theorem Lam5_lt_D5 : Lam5 < (D5 : ℝ) := by
  have h := Real.log_two_lt_d9
  unfold Lam5 D5
  push_cast
  nlinarith

/-- The exponent is below `59983/2500`. -/
theorem fifths_X_le :
    (1 : ℝ) * (c5 : ℝ) / ((D5 : ℝ) - Lam5) ≤ ((59983 / 2500 : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  have hpos : 0 < (D5 : ℝ) - Lam5 := sub_pos.2 Lam5_lt_D5
  rw [one_mul, div_le_iff₀ hpos]
  unfold Lam5 D5 c5
  push_cast
  nlinarith

/-- **Measure of the fifths block family.**  Content and decay as hypotheses. -/
theorem fifths_measureLB (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : F5.selectionDepth Fr 2 ≤ depth)
    (hS : HasScaledContent ((F5.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale Lam5)
    (hD : HasScaledDecay (F5.family Fr depth) F5.scale (D5 : ℝ) (c5 : ℝ)) :
    (F5.family Fr depth).MeasureLB ((59983 / 2500 : ℚ) : ℝ) := by
  have hmass : (F5.common.mass : ℝ) = 1 := by rw [F5_common_mass]; norm_num
  have hc : (0 : ℝ) < (c5 : ℝ) := by unfold c5; norm_num
  have key := measure_of_family_nv0_even
    ((F5.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale
    (γ := 1) (K := F5.common.n) hS
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) Lam5_lt_D5 hc one_pos (Nat.cast_nonneg _)
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
    (Measure.MeasureLBAt.mono fifths_X_le ((Measure.MeasureLB_iff _ _).1 key))

/-- **Target transport.**  For a frame whose constant is `(-1/25)` times the target, the measure
statement for the family becomes the one for the target. -/
theorem fifths_measure_of_const (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : F5.selectionDepth Fr 2 ≤ depth) {target : ℝ}
    (hconst : Fr.const = ((-1 / 25 : ℚ) : ℝ) * target)
    (hS : HasScaledContent ((F5.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) F5.scale Lam5)
    (hD : HasScaledDecay (F5.family Fr depth) F5.scale (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt target ((59983 / 2500 : ℚ) : ℝ) := by
  have h0 := (Measure.MeasureLB_iff _ _).1 (fifths_measureLB Fr hd hw depth hdepth hS hD)
  have h' : Measure.MeasureLBAt Fr.const ((59983 / 2500 : ℚ) : ℝ) := h0
  have he : target = ((-25 : ℚ) : ℝ) * Fr.const + ((0 : ℚ) : ℝ) := by
    rw [hconst]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) (-25) 0 (by norm_num)

end CatalanCore.Uniform.Bank.Fifths
