module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RowP
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RowN

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The anchor-0 free row of `capSource`

kcost: no computation here.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.Davis.CircleCheb
open Set

theorem freeRowCap0_cert : capSource.FreeRowCap Trunc.exact 0 (-2579777 / 1000000) :=
  freeRowCap0_of_checks rowP rowN

end CatalanMeasure.GenD.Signed.RouteI.RowCert
