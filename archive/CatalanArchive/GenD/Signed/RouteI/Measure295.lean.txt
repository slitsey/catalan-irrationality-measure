module

public import CatalanMeasure.GenD.Signed.RouteI.Terminal295
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.All
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.All
public import CatalanMeasure.GenD.Signed.RouteI.GasEnergyHi
public import CatalanMeasure.GenD.Signed.RouteI.AngAll

@[expose] public section

/-!
# The irrationality measure bound 295 for Catalan's constant

`Terminal295.measure_295` with its five inputs supplied.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.Measure295

open Filter

theorem catalan_irrationalityMeasure_295 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(295 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  Terminal295.measure_295 RowCert.freeRowCap0_cert ColCert.All.freeColCap0_cert
    GasEnergy.hi_final AngAll.certN AngAll.certP

end CatalanMeasure.GenD.Signed.RouteI.Measure295
