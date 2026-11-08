module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RadLP

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The radial checks at degree 224, sign P

kcost: 16 classes of 224 terms, about 3 s each measured.
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
open CatalanMeasure.GenD.Signed.RouteI.OrdHf

theorem rcP0 : (RP2.chk (auxT Sign.pos) 0 && radChk (RP2.B 0).rho (RP2.B 0).sg (RP2.eta 0) 0) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP1 : (RP2.chk (auxT Sign.pos) 1 && radChk (RP2.B 1).rho (RP2.B 1).sg (RP2.eta 1) 1) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP2 : (RP2.chk (auxT Sign.pos) 2 && radChk (RP2.B 2).rho (RP2.B 2).sg (RP2.eta 2) 2) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP3 : (RP2.chk (auxT Sign.pos) 3 && radChk (RP2.B 3).rho (RP2.B 3).sg (RP2.eta 3) 3) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP4 : (RP2.chk (auxT Sign.pos) 4 && radChk (RP2.B 4).rho (RP2.B 4).sg (RP2.eta 4) 4) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP5 : (RP2.chk (auxT Sign.pos) 5 && radChk (RP2.B 5).rho (RP2.B 5).sg (RP2.eta 5) 5) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP6 : (RP2.chk (auxT Sign.pos) 6 && radChk (RP2.B 6).rho (RP2.B 6).sg (RP2.eta 6) 6) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP7 : (RP2.chk (auxT Sign.pos) 7 && radChk (RP2.B 7).rho (RP2.B 7).sg (RP2.eta 7) 7) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP8 : (RP2.chk (auxT Sign.pos) 8 && radChk (RP2.B 8).rho (RP2.B 8).sg (RP2.eta 8) 8) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP9 : (RP2.chk (auxT Sign.pos) 9 && radChk (RP2.B 9).rho (RP2.B 9).sg (RP2.eta 9) 9) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP10 : (RP2.chk (auxT Sign.pos) 10 && radChk (RP2.B 10).rho (RP2.B 10).sg (RP2.eta 10) 10) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP11 : (RP2.chk (auxT Sign.pos) 11 && radChk (RP2.B 11).rho (RP2.B 11).sg (RP2.eta 11) 11) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP12 : (RP2.chk (auxT Sign.pos) 12 && radChk (RP2.B 12).rho (RP2.B 12).sg (RP2.eta 12) 12) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP13 : (RP2.chk (auxT Sign.pos) 13 && radChk (RP2.B 13).rho (RP2.B 13).sg (RP2.eta 13) 13) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP14 : (RP2.chk (auxT Sign.pos) 14 && radChk (RP2.B 14).rho (RP2.B 14).sg (RP2.eta 14) 14) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcP15 : (RP2.chk (auxT Sign.pos) 15 && radChk (RP2.B 15).rho (RP2.B 15).sg (RP2.eta 15) 15) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem allP : RP2.allChk (auxT Sign.pos) = true :=
  allChk_of (lt16 (p := fun i => (RP2.chk (auxT Sign.pos) i && radChk (RP2.B i).rho (RP2.B i).sg (RP2.eta i) i) = true) rcP0 rcP1 rcP2 rcP3 rcP4 rcP5 rcP6 rcP7 rcP8 rcP9 rcP10 rcP11 rcP12 rcP13 rcP14 rcP15)
theorem wP : RP2.W + RP2.sh = 160 := by decide +kernel -- kcost: two literals
theorem bP : RP2.Bs.length = 16 := by decide +kernel -- kcost: one list
theorem hqP : RP2.hq = (1 - massQ gP.T gP.L) / (sumP (auxT Sign.pos) : ℚ) := pHq
theorem hq0P : 0 ≤ RP2.hq := pHq0
theorem radP : RadOK RP2 capSource (auxT Sign.pos) (tgt Sign.pos) (sumP (auxT Sign.pos)) 16 :=
  radOK_of RP2 Sign.pos enc_valid tgtP hqP hq0P pAux cos_ok co_ok cq_ok cq_len wP dc0 bP allP pTot

end CatalanMeasure.GenD.Signed.RouteI.RowCert
