module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.BindP
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RestP
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpFinP
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnAllP
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.SqP0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.HcP0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.CoverP

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The certificate of the moved row, sign P, level 0 (`h0` for 0, `h0 + h1` for 1)

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

theorem eAP0 : Enc.tail (1 - massQ gP.T gP.L) 1 ≤ (3 / 1000000000) := by
  decide +kernel -- kcost: 0.1 s estimated, one tail
theorem eRP0 : errS RP2 16 ≤ (7 / 125000000) := by
  decide +kernel -- kcost: 1 s estimated, 16 class errors
theorem eEP0 : (1 / 900 + 1 / 901) / 901 * ((EvP : ℚ) / 2 ^ 64) ≤ (9783 / 5000000000) := by
  decide +kernel -- kcost: 0.01 s estimated, one product
noncomputable def rowP0 : RowCertMv Sign.pos (Ioo (0 : ℝ) 1) ((-2579740254 / 1000000000) : ℝ) (fun t => hMov0 (sgOf Sign.pos * t)) where
  dP := dPc
  hdP := by norm_num [dPc]
  hdom := fun t ht => ⟨ht.1, ht.2.le⟩
  cr := 1
  hcr := by norm_num
  wl := 0
  Go := GoP
  Gs := GsP
  Gq := GqP
  Gc := GcP
  qR := qRP
  qO := qOP
  q0 := qC0P
  qC := qCTP
  LF := LFP
  LT := LTP
  cD := cDP
  cF := cFP
  cT := cTP
  cl := clP
  cH := cHP0
  r := rMP0
  q := qMP0
  K := 167
  m := 16383
  lgs := 15
  lgq := 14
  c := cMP0
  Lq := (-21776484962337950565 / 73786976294838206464)
  eD := (12441036745 / 1125899906842624)
  eF := 9 / 10 ^ 10
  eT := 1 / 10 ^ 10
  eR := (7 / 125000000)
  eA := (3 / 1000000000)
  eE := (9783 / 5000000000)
  eH := 161 / ((dPc : ℕ) : ℝ)
  bindO := fun F => by
    have := bind_two_pos gasPos_ev sOP cnOP F
    simpa [sgOf, GoP] using this
  bindQ := fun F => by
    have := bind_chain_neg gasNeg_ev sQP cnQP F
    simpa [sgOf, opp, GqP] using this
  bindC := fun F => by
    have := bind_chain_pos col_ev sCP cnCP F
    simpa [sgOf, GcP] using this
  keyO := keyB_real kOP
  keyQ := keyB_real kQP
  posS := posB_real pSP
  chkR := chkRP
  chkO := chkOP
  chkC := chkCP
  hLq := hLqP
  hRf := hRf_pos (fun F => by simpa [sgOf, GoP] using bind_two_pos gasPos_ev sOP cnOP F) (keyB_real kOP)
  hLog := hLogP
  hRad := fun t ht => (hRadP t ht).trans (by
    have e := (Rat.cast_le (K := ℝ)).2 eRP0
    push_cast at e ⊢
    linarith)
  hDir := hDirFP
  hF := hFP
  hT := hTP
  hH := hHP0
  hAux := auxP_le.trans (by
    have e := (Rat.cast_le (K := ℝ)).2 eAP0
    push_cast at e
    linarith)
  hE := by
    simp only [if_true]
    refine eref_cap.trans ?_
    have e := (Rat.cast_le (K := ℝ)).2 eEP0
    push_cast at e
    linarith
  hs := sLenP0
  hq := qLenP0
  hgs := by norm_num
  hgq := by norm_num
  hK := sqP0
  hb := sqbP0
  hc := sqcP0
  hfin := by
    obtain ⟨e1, e2⟩ := sqrP0
    rw [e1, e2]
    norm_num [cMP0, dPc, kappa]

end CatalanMeasure.GenD.Signed.RouteI.RowCert
