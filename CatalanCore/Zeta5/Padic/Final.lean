module

public import CatalanCore.Zeta5.Padic.All
public import CatalanCore.Zeta5.Criterion.Signed
public import CatalanCore.Zeta5.Rho.Norm

@[expose] public section

/-!
# `μ(ζ(5)) ≤ 87` from the parity gain

`zeta5_mu87_of_decay`: the parity gain (`Apery.parity_gain`) discharges `hpar` of
`zeta5_measure_of_parity`. `rhoBound_907427`: the ρ bound `RhoBound (907427/10⁵)` is
`Rho.zeta5_rho_bound`. `zeta5_mu87_of_decay'`: the composite with only the decay input left.
-/

namespace CatalanCore.Zeta5

theorem zeta5_mu87_of_decay {D : ℝ} (hD : CatalanCore.Zeta5.DecayAtConst D)
    (hD0 : 138500086 / 10 ^ 8 ≤ D) (hρ : CatalanCore.Zeta5.RhoBound (907427 / 10 ^ 5)) :
    CatalanCore.Measure.MeasureLBAt Apery.zeta5 87 :=
  CatalanCore.Zeta5.zeta5_measure_of_parity Apery.parity_gain hD hD0 hρ

/-- **ZR10 in the form `RhoBound`.** -/
theorem rhoBound_907427 : CatalanCore.Zeta5.RhoBound (907427 / 10 ^ 5) :=
  CatalanCore.Zeta5.Rho.zeta5_rho_bound

theorem zeta5_mu87_of_decay' {D : ℝ} (hD : CatalanCore.Zeta5.DecayAtConst D)
    (hD0 : 138500086 / 10 ^ 8 ≤ D) : CatalanCore.Measure.MeasureLBAt Apery.zeta5 87 :=
  zeta5_mu87_of_decay hD hD0 rhoBound_907427

end CatalanCore.Zeta5
