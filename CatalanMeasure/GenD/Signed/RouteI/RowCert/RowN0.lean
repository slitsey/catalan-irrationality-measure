module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.BindN
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RestN
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpFinN
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnAllN
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.SqN0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.HcN0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.CoverN

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The certificate of the moved row, sign N, level 0 (`h0` for 0, `h0 + h1` for 1)

kcost: constants only.
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
open CatalanMeasure.GenD.Signed.RouteI.RowCertMoved

theorem eAN0 : Enc.tail (53 / 58 - massQ gN.T gN.L) 2 ≤ (9 / 1000000000) := by
  decide +kernel -- kcost: 0.1 s estimated, one tail
theorem eRN0 : errN RN2 Tm224 ≤ (19 / 10000000) := by
  decide +kernel -- kcost: 1 s estimated, 16 class errors
noncomputable def rowN0 : RowCertMv Sign.neg (Ioc (0 : ℝ) 1) ((-2579740254 / 1000000000) : ℝ) (fun t => hMov0 (sgOf Sign.neg * t)) where
  dP := dPc
  hdP := by norm_num [dPc]
  hdom := fun t ht => ht
  cr := 2
  hcr := by norm_num
  wl := 0
  Go := GoN
  Gs := GsN
  Gq := GqN
  Gc := GcN
  qR := qRN
  qO := qON
  q0 := qC0N
  qC := qCTN
  LF := LFN
  LT := LTN
  cD := cDN
  cF := cFN
  cT := cTN
  cl := clN
  cH := cHN0
  r := rMN0
  q := qMN0
  K := 167
  m := 16383
  lgs := 15
  lgq := 14
  c := cMN0
  Lq := (-233412854896680293853 / 590295810358705651712)
  eD := (12903603511 / 1125899906842624)
  eF := 9 / 10 ^ 10
  eT := 1 / 10 ^ 10
  eR := (19 / 10000000)
  eA := (9 / 1000000000)
  eE := (0 / 1)
  eH := 161 / ((dPc : ℕ) : ℝ)
  bindO := fun F => by
    have := bind_two_neg gasNeg_ev sON cnON F
    simpa [sgOf, GoN] using this
  bindQ := fun F => by
    have := bind_chain_pos gasPos_ev sQN cnQN F
    simpa [sgOf, opp, GqN] using this
  bindC := fun F => by
    have := bind_chain_neg col_ev sCN cnCN F
    simpa [sgOf, GcN] using this
  keyO := keyB_real kON
  keyQ := keyB_real kQN
  posS := posB_real pSN
  chkR := chkRN
  chkO := chkON
  chkC := chkCN
  hLq := hLqN
  hRf := hRf_neg _
  hLog := hLogN
  hRad := fun t ht => (hRadN t ht).trans (by
    have e := (Rat.cast_le (K := ℝ)).2 eRN0
    push_cast at e ⊢
    linarith)
  hDir := hDirFN
  hF := hFN
  hT := hTN
  hH := hHN0
  hAux := auxN_le.trans (by
    have e := (Rat.cast_le (K := ℝ)).2 eAN0
    push_cast at e
    linarith)
  hE := by
    simp
  hs := sLenN0
  hq := qLenN0
  hgs := by norm_num
  hgq := by norm_num
  hK := sqN0
  hb := sqbN0
  hc := sqcN0
  hfin := by
    obtain ⟨e1, e2⟩ := sqrN0
    rw [e1, e2]
    norm_num [cMN0, dPc, kappa]

end CatalanMeasure.GenD.Signed.RouteI.RowCert
