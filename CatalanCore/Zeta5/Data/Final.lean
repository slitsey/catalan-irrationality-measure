module

public import CatalanCore.Zeta5.Data.Cover
public import CatalanCore.Zeta5.Data.Zd22
public import CatalanCore.Zeta5.Padic.Final

@[expose] public section

/-!
# Z5-DATA, part 5: the unconditional theorem `μ(ζ(5)) ≤ 87`

`zeta5_mu87_of_decay'` (`Padic.Final`) applied to `Decay.zeta5_decay` at the design of
`Data.Design`: the positive sum-of-squares density `cR` (`c_0 = 37/40`), `b = (43/50)²`,
`M₀ = −3330031/500000`.  The cell inequality on `[0, 4]` is `Cells.hcell_of_cells` from the region A
and B covers (`zd17_design`, `zd18_design`: 100 + 10 kernel-checked cells), the constant
inequality is `Cells.hconst_of_zd22` from `zd22_design`.
-/

namespace CatalanCore.Zeta5.Data

open Set CatalanCore.Zeta5.Cells CatalanCore.Zeta5.Potential

noncomputable section

theorem M0_ge : (-8 : ℝ) ≤ (desA.M0 : ℝ) := by
  norm_num [desA]

/-- **`μ(ζ(5)) ≤ 87`**, unconditionally. -/
theorem zeta5_mu87 : CatalanCore.Measure.MeasureLBAt Apery.zeta5 87 := by
  have hyb : (0 : ℝ) < 43 / 50 := by norm_num
  have hT : (4 : ℝ) ≤ ((43 / 50 : ℝ) ^ 2 / 2) * (1 + Real.cosh 3) := four_lt_t_three.le
  have hcell := hcell_of_cells hyb hpos_design hT zd17_design zd18_design
  have hconst := hconst_of_zd22 (c := cR) (N := 60) cR_zero zd22_design
  exact CatalanCore.Zeta5.zeta5_mu87_of_decay'
    (CatalanCore.Zeta5.Decay.zeta5_decay (b := (43 / 50 : ℝ) ^ 2) (by norm_num) (by norm_num)
      hpos_design cR_zero M0_ge hcell hconst) le_rfl

end

end CatalanCore.Zeta5.Data
