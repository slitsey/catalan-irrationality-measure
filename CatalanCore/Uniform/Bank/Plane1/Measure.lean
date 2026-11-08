module

public import CatalanCore.Uniform.Bank.Plane1.Cover
public import CatalanCore.Uniform.Bank.Plane1.Data.Ok
public import CatalanCore.Uniform.Bank.Plane1.Rows

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # The plane 1 measure bound (wave P114; ledger P116, P117, P118)

**`plane1_measure`** (a, b form; `a ≠ 0` for now, one place: P119 relaxes it) is derived from `plane1_measure_t`: for every rational `t`, `L₃ + t π²` is irrational and `μ(L₃ + t π²) ≤ 20.6622`, with no open
hypotheses: the content `planeLam` is `planeContent_data` (closed form, `N = 32` strips), the decay is the generated
cover `Dp1` (`planeDecay_cover`), and `ccert / (Dt - planeLam) ≤ 20.6622` is an exact rational comparison.  The frame of `t`
is `exists_planeRow t`: `S⁺`, or `S⁻` at `t ∈ {1/9, 1/27}`.  `plane1_sixths` is the corollary at `t = 11/135`
(`ψ′(1/6) - ζ(2)`), `plane1_mirror` the `S⁻` instance of the same frame (`t = -11/135`, P117). -/

namespace CatalanCore.Uniform.Bank.Plane1
open CatalanCore CatalanCore.Uniform CatalanCore.Measure CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Bank.Plane1.Data

theorem plane1_eta : planeLam < Dp1.Dt := by
  -- kcost: rational comparison of two literals, < 1 s
  decide +kernel

theorem plane1_cc : 0 < Dp1.ccert := by decide +kernel

theorem plane1_ratio : Dp1.ccert / (Dp1.Dt - planeLam) ≤ 206622 / 10000 := by
  -- kcost: exact rational arithmetic, < 1 s
  decide +kernel

theorem plane1_ratio_real : ((Dp1.ccert : ℚ) : ℝ) / (((Dp1.Dt : ℚ) : ℝ) - ((planeLam : ℚ) : ℝ)) ≤ 206622 / 10000 := by
  have h : ((Dp1.ccert / (Dp1.Dt - planeLam) : ℚ) : ℝ) ≤ ((206622 / 10000 : ℚ) : ℝ) := Rat.cast_le.2 plane1_ratio
  push_cast at h
  exact h

/-- **The plane 1 theorem (P116), with no open hypotheses**: `μ(L₃ + t π²) ≤ 20.6622` and `L₃ + t π²` is irrational,
for every rational `t`. -/
theorem plane1_measure_t (t : ℚ) :
    MeasureLBAt (CatalanFrames.P6.chi3L2 + (t : ℝ) * Real.pi ^ 2) (206622 / 10000) ∧ Irrational (CatalanFrames.P6.chi3L2 + (t : ℝ) * Real.pi ^ 2) := by
  obtain ⟨h1, h2⟩ := plane_point t planeContent_data planeDecay_cover plane1_eta plane1_cc
  exact ⟨h1.mono plane1_ratio_real, h2⟩

/-- **The plane 1 theorem in (a, b) form**: for rational `a ≠ 0` and `b`, `a L₃ + b π²` is irrational and
`μ(a L₃ + b π²) ≤ 20.6622`.  The hypothesis `ha : a ≠ 0` enters only here (the affine transfer from `t = b / a`);
the a = 0 case replaces this proof (P119) without touching the cover data. -/
theorem plane1_measure (a b : ℚ) (ha : a ≠ 0) :
    MeasureLBAt ((a : ℝ) * CatalanFrames.P6.chi3L2 + (b : ℝ) * Real.pi ^ 2) (206622 / 10000) ∧
      Irrational ((a : ℝ) * CatalanFrames.P6.chi3L2 + (b : ℝ) * Real.pi ^ 2) := by
  obtain ⟨h1, h2⟩ := plane1_measure_t (b / a)
  have e : (a : ℝ) * (CatalanFrames.P6.chi3L2 + ((b / a : ℚ) : ℝ) * Real.pi ^ 2) + ((0 : ℚ) : ℝ) =
      (a : ℝ) * CatalanFrames.P6.chi3L2 + (b : ℝ) * Real.pi ^ 2 := by
    have : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    push_cast
    field_simp
    ring
  have m := h1.affine (by norm_num) a 0 ha
  have i := irrational_affine h2 a 0 ha
  rw [e] at m i
  exact ⟨m, i⟩

/-- **Sixths (P118)**: `t = 11/135`, `ψ′(1/6) - ζ(2) = (45/2)(L₃ + 11π²/135)`. -/
theorem plane1_sixths :
    MeasureLBAt (CatalanFrames.P6.chi3L2 + ((11 / 135 : ℚ) : ℝ) * Real.pi ^ 2) (206622 / 10000) ∧
      Irrational (CatalanFrames.P6.chi3L2 + ((11 / 135 : ℚ) : ℝ) * Real.pi ^ 2) :=
  plane1_measure_t (11 / 135)

/-- **The mirror (P117)**: the frame `(5, -2, -3)` on `S⁻`, `t = -11/135`, on the same cover. -/
theorem plane1_mirror :
    MeasureLBAt (CatalanFrames.P6.chi3L2 + ((-(11 / 135) : ℚ) : ℝ) * Real.pi ^ 2) (206622 / 10000) ∧
      Irrational (CatalanFrames.P6.chi3L2 + ((-(11 / 135) : ℚ) : ℝ) * Real.pi ^ 2) := by
  obtain ⟨h1, h2⟩ := mirror_point (planeContent_data .minus 5 (-2) (-3) (by norm_num))
    (planeDecay_cover .minus 5 (-2) (-3) (by norm_num)) plane1_eta plane1_cc
  exact ⟨h1.mono plane1_ratio_real, h2⟩

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.plane1_measure
#print axioms CatalanCore.Uniform.Bank.Plane1.plane1_sixths
#print axioms CatalanCore.Uniform.Bank.Plane1.plane1_mirror
