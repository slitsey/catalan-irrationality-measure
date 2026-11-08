module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RadLN

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The radial checks at degree 224, sign N

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

theorem rcN0 : (RN2.chk (auxT Sign.neg) 0 && radChk (RN2.B 0).rho (RN2.B 0).sg (RN2.eta 0) 0) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN1 : (RN2.chk (auxT Sign.neg) 1 && radChk (RN2.B 1).rho (RN2.B 1).sg (RN2.eta 1) 1) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN2 : (RN2.chk (auxT Sign.neg) 2 && radChk (RN2.B 2).rho (RN2.B 2).sg (RN2.eta 2) 2) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN3 : (RN2.chk (auxT Sign.neg) 3 && radChk (RN2.B 3).rho (RN2.B 3).sg (RN2.eta 3) 3) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN4 : (RN2.chk (auxT Sign.neg) 4 && radChk (RN2.B 4).rho (RN2.B 4).sg (RN2.eta 4) 4) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN5 : (RN2.chk (auxT Sign.neg) 5 && radChk (RN2.B 5).rho (RN2.B 5).sg (RN2.eta 5) 5) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN6 : (RN2.chk (auxT Sign.neg) 6 && radChk (RN2.B 6).rho (RN2.B 6).sg (RN2.eta 6) 6) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN7 : (RN2.chk (auxT Sign.neg) 7 && radChk (RN2.B 7).rho (RN2.B 7).sg (RN2.eta 7) 7) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN8 : (RN2.chk (auxT Sign.neg) 8 && radChk (RN2.B 8).rho (RN2.B 8).sg (RN2.eta 8) 8) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN9 : (RN2.chk (auxT Sign.neg) 9 && radChk (RN2.B 9).rho (RN2.B 9).sg (RN2.eta 9) 9) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN10 : (RN2.chk (auxT Sign.neg) 10 && radChk (RN2.B 10).rho (RN2.B 10).sg (RN2.eta 10) 10) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN11 : (RN2.chk (auxT Sign.neg) 11 && radChk (RN2.B 11).rho (RN2.B 11).sg (RN2.eta 11) 11) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN12 : (RN2.chk (auxT Sign.neg) 12 && radChk (RN2.B 12).rho (RN2.B 12).sg (RN2.eta 12) 12) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN13 : (RN2.chk (auxT Sign.neg) 13 && radChk (RN2.B 13).rho (RN2.B 13).sg (RN2.eta 13) 13) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN14 : (RN2.chk (auxT Sign.neg) 14 && radChk (RN2.B 14).rho (RN2.B 14).sg (RN2.eta 14) 14) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem rcN15 : (RN2.chk (auxT Sign.neg) 15 && radChk (RN2.B 15).rho (RN2.B 15).sg (RN2.eta 15) 15) = true := by
  decide +kernel -- kcost: one class of 224 terms, 3 s measured
theorem allN : RN2.allChk (auxT Sign.neg) = true :=
  allChk_of (lt16 (p := fun i => (RN2.chk (auxT Sign.neg) i && radChk (RN2.B i).rho (RN2.B i).sg (RN2.eta i) i) = true) rcN0 rcN1 rcN2 rcN3 rcN4 rcN5 rcN6 rcN7 rcN8 rcN9 rcN10 rcN11 rcN12 rcN13 rcN14 rcN15)
theorem wN : RN2.W + RN2.sh = 160 := by decide +kernel -- kcost: two literals
theorem bN : RN2.Bs.length = 16 := by decide +kernel -- kcost: one list
theorem hqN : RN2.hq = (53 / 58 - massQ gN.T gN.L) / (sumP (auxT Sign.neg) : ℚ) := nHq
theorem hq0N : 0 ≤ RN2.hq := nHq0
theorem radN : RadOK RN2 capSource (auxT Sign.neg) (tgt Sign.neg) (sumP (auxT Sign.neg)) 16 :=
  radOK_of RN2 Sign.neg enc_valid tgtN hqN hq0N nAux cos_ok co_ok cq_ok cq_len wN dc0 bN allN nTot
theorem rnN : rnOK RN2 rnsN 44 = true := by decide +kernel -- kcost: 16 comparisons
theorem fbN : fbOK RN2 = true := by decide +kernel -- kcost: 16 rows of comparisons
theorem dmN : Dm224 = truncD RN2.sh 224 (mirF RN2 rnsN 44 16) := by decide +kernel -- kcost: the mirror series, 224 terms
theorem tmN : abs1 ((mirF RN2 rnsN 44 16).drop 224) = Tm224 := by decide +kernel -- kcost: its tail

end CatalanMeasure.GenD.Signed.RouteI.RowCert
