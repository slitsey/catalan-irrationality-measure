module

public import CatalanMeasure.GenD.Signed.RouteI.Theorem296
public import CatalanMeasure.GenD.Signed.RouteI.T4Instance
public import CatalanMeasure.GenD.Signed.RouteI.OrdHf
public import CatalanMeasure.GenD.Signed.RouteI.NearDataCert
public import CatalanMeasure.GenD.Signed.RouteI.PhaseHoleProof
public import CatalanMeasure.GenD.Signed.RouteI.AngularCap
public import CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.Caps
public import CatalanMeasure.GenD.Signed.Count.LedgerContent
public import CatalanMeasure.GenD.Signed.Count.WinCertGlue
public import CatalanMeasure.GenD.Signed.Davis.S1Contour
public import CatalanMeasure.GenD.Signed.Davis.RealSegmentWeights
public import CatalanMeasure.GenD.Analytic.PsiEntropy
public import CatalanMeasure.GenD.Analytic.DeltaChain
public import CatalanMeasure.GenD.DesignInstance.FirstTrialCert
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Norm
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Near
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RCover

@[expose] public section
set_option Elab.async false

/-!
# Route I terminal assembly at `B = 295`

Discharges every premise of `RouteI.catalan_irrationalityMeasure_295` except the five inputs named
in `measure_295`: the free row cap `hR`, the free column cap `hC`, the intercept scalar `hi`, and the
angular radius certificates `certN`, `certP`, all at the source record `capSource`.

The sources of the discharged premises:

* `hcontent`, `hgain`: `Count.LedgerContent.content`, `Count.WinCertGlue.eta295_lt_of_gain`.
* `hweights`: `S1Contour.hweights58_of_cheb` on the same `tau58`, with the segment bound
  `RealSegmentWeights.segmentPhi58` and the continuum entropy selector `hPsi58` below.
* `hfirst`: `firstTrial_D58` directly from `FirstTrialCert`, not `Providers`.
* `hlarge`: the K590 trial pair with the route-I maxima caps `row_sup_S'`, `column_sup_S'` and the
  residual extended to `G58` by `UnsignedInstance.residual_sup_d58`.
* `hnear`: `T4Instance.freeNear_anchor0` with the compact caps at degree `384` taken to the exact
  fields, the angular caps likewise, and `PhysicalPick.phaseHole`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.Terminal295

open Filter Set CatalanMeasure.GenD D58 Analytic CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.CellCert CatalanMeasure.Cert
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.Davis

noncomputable section

/-! ### Weights -/

/-- The strict nodal exponent. -/
def psi58 : ℝ := 872299 / 10000

/-- One exact price check at the radius `3/5`. -/
def priceOK : Bool :=
  match LogEval.logQ 12 (3 / 5), LogEval.logQ 12 (8 / 3) with
  | some (v, e), some (w, f) =>
      decide (10 * (v + e) + 709 / 20 + 58 * (w + f) ≤ 872299 / 10000)
  | _, _ => false

theorem priceOK_true : priceOK = true := by
  -- kcost: 0.02 s estimated; two logQ at n = 12 (S1Selector runs three per cell at the same n).
  decide +kernel

theorem price_le :
    10 * Real.log (3 / 5) + 709 / 20 + 58 * Real.log (1 + 1 / (3 / 5)) ≤ psi58 := by
  have h := priceOK_true
  unfold priceOK at h
  split at h
  · rename_i v e w f h1 h2
    have hp := of_decide_eq_true h
    have l1 := (LogEval.logQ_spec h1).2.le_upper
    have l2 := (LogEval.logQ_spec h2).2.le_upper
    have hp' : ((10 * (v + e) + 709 / 20 + 58 * (w + f) : ℚ) : ℝ) ≤
        ((872299 / 10000 : ℚ) : ℝ) := Rat.cast_le.mpr hp
    push_cast at hp' l1 l2
    have e2 : (8 / 3 : ℝ) = 1 + 1 / (3 / 5) := by norm_num
    rw [e2] at l2
    unfold psi58
    linarith
  · simp at h

/-- `hΨ` of `hweights58` at the cap `709/20`, for every `κ`. -/
theorem hPsi58 : ∀ κ ∈ Icc (0 : ℝ) 1, omega58 (709 / 20) κ + binomRate κ ≤ psi58 / 58 := by
  intro κ hκ
  have h := affine_binomRate_continuum (3 / 5) 10 58 (709 / 20) psi58 (by norm_num) (by norm_num)
    (by norm_num) price_le κ hκ
  unfold omega58
  linarith

/-- `hweights` of `catalan_irrationalityMeasure_295`, unconditional, on the nodes `tau58`. -/
theorem hweights295 : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p + m = dc58.toParameters.n N →
    ∀ k : ℕ, k < dc58.toParameters.n N → ∀ a : Fin (53 * N),
    |(rowCommonFactor dc58.toParameters N).eval (tau58 N a)| *
      |restrictedWeight dc58.toParameters N k (tau58 N) a| *
      (CatalanMeasure.binomBeta p m k : ℝ) ≤
        108000 * (N : ℝ) * Real.exp (psi296 * N) := by
  have h := S1Contour.hweights58_of_cheb tau58 rfl psi58 RealSegmentWeights.segmentPhi58 hPsi58
    (by norm_num [psi58])
  filter_upwards [h] with N hN p m hpm k hk a
  exact hN p m hpm k hk a

/-! ### First sheet -/

/-- The first trial, from `FirstTrialCert`. -/
def first295 : FirstTrialBounds Odd.design K590.target K590.firstCost :=
  firstTrial_D58 hrow_D58 hcol_D58 K590.first_budget_log2

theorem hfirst295 : FreeFirstBound dc58.toParameters T296 (58 * cost296) :=
  freeFirst296 first295 rfl rfl rfl

/-! ### Large sheet: the K590 pair -/

theorem row_sup_K590 : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (11 / 29) (3 / 29) (39 / 29) (trialSeqS Cert590.Pc Cert590.P)
      (trialSeqS Cert590.Vc Cert590.V) x ≤ ((Cert590.MX : ℚ) : ℝ) := by
  intro x hx
  have h := Cert590.row_sup_S' x hx
  have e : rowFieldS Cert590.R Cert590.Pc Cert590.Vc Cert590.P Cert590.V =
      rowFieldG (11 / 29) (3 / 29) (39 / 29) (trialSeqS Cert590.Pc Cert590.P)
        (trialSeqS Cert590.Vc Cert590.V) := by
    unfold rowFieldS
    norm_num [Cert590.R]
  rw [e] at h
  exact h

theorem column_sup_K590 : ∀ s ∈ Ioo (0 : ℝ) 1,
    colFieldG (9 / 58) (3 / 58) (trialSeqS Cert590.Vc Cert590.V) s ≤ ((Cert590.MY : ℚ) : ℝ) := by
  intro s hs
  have h := Cert590.column_sup_S' s hs
  have e : colFieldS Cert590.C Cert590.Vc Cert590.V =
      colFieldG (9 / 58) (3 / 58) (trialSeqS Cert590.Vc Cert590.V) := by
    unfold colFieldS
    norm_num [Cert590.C]
  rw [e] at h
  exact h

theorem near_K590 : ∀ y ∈ Ioo (0 : ℝ) 1,
    -gRes Odd.design * Real.log (1 + y ^ 2) +
      (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
        trialSeqS Cert590.Pc Cert590.P 1 * y ≤ D58.nearCap := by
  intro y hy
  have h := D58.Cert.near_residual_field_le_d58 Cert590.first_lower hy.1 hy.2.le
  rw [Instances.d58_gRes]
  have e : (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) = 47 / 58 := by
    norm_num [Odd.design]
  rw [e]
  have e2 : D58.nearCap = -(77 / 100 : ℝ) := by norm_num [D58.nearCap]
  rw [e2]
  exact h

theorem residual_K590 : ∀ x ∈ Icc (-1 : ℝ) 1, G58 x →
    resFieldGen (gRes Odd.design) (trialSeqS Cert590.Pc Cert590.P) x ≤ K590.residualCap := by
  have hMR : ((Cert590.MR : ℚ) : ℝ) = K590.residualCap := by
    norm_num [Cert590.MR, K590.residualCap]
  exact UnsignedInstance.residual_sup_d58 Instances.d58_gRes Cert590.hZ_R (fun _ h => h)
    (fun x hx hg => hMR ▸ Cert590.residual_sup_S x hx hg)
    (by norm_num [K590.residualCap])

/-- The K590 budget in the shape of `SecondFieldCert`. -/
theorem budget_K590 {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      K590.normCap + (1 - a) * K590.fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * K590.residualCap + t * D58.nearCap ≤
        -K590.target + Real.log 2 / 2 + K590.secondCost * a := by
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K590.second_budget_log2 ha ht
  norm_num [c07, c26] at h
  linarith

/-- The K590 certificate on the support `G58`. -/
def second295 : SecondFieldCert Odd.design K590.target K590.residualCap D58.nearCap
    K590.secondCost G58 where
  u := trialSeqS Cert590.Pc Cert590.P
  v := trialSeqS Cert590.Vc Cert590.V
  hu := (trialSeqS_summable Cert590.tailsP).1
  hv := (trialSeqS_summable Cert590.tailsV).1
  MX := (Cert590.MX : ℚ)
  MY := (Cert590.MY : ℚ)
  normCap := K590.normCap
  fieldCap := K590.fieldCap
  near_sup := near_K590
  norm_le := by
    have h2 : (((2 * Cert590.NP + Cert590.NV / 2 : ℚ)) : ℝ) ≤ K590.normCap := by
      norm_num [Cert590.NP, Cert590.NV, K590.normCap]
    exact Cert590.weighted_norm_le.trans h2
  field_sum := by norm_num [Cert590.MX, Cert590.MY, K590.fieldCap]
  row_sup := by
    rw [(Instances.d58_row_weights).1, (Instances.d58_row_weights).2.1,
      (Instances.d58_row_weights).2.2]
    exact row_sup_K590
  column_sup := by
    rw [(Instances.d58_column_weights).1, (Instances.d58_column_weights).2]
    exact column_sup_K590
  residual_sup := residual_K590
  budget := budget_K590

/-- The tangent slack `u` of `second198`. -/
def slack295 : ℝ := 68682 / 10000000

theorem slack295_nonneg : 0 ≤ slack295 := by norm_num [slack295]

theorem hobj295 : (second295.bounds Odd.design_admissible).normCap +
    (second295.bounds Odd.design_admissible).fieldCap + T296 - c07 * lo ≤ slack295 := by
  change K590.normCap + K590.fieldCap + T296 - c07 * lo ≤ slack295
  norm_num [K590.normCap, K590.fieldCap, T296, K590.target, shift296, c07, lo, slack295]

theorem hcost295 : ((c26 - 1) * hi - (second295.bounds Odd.design_admissible).fieldCap +
    K590.residualCap - cost296) - lo * alpha296 + slack295 / alpha296 ≤ 0 := by
  change ((c26 - 1) * hi - K590.fieldCap + K590.residualCap - cost296) - lo * alpha296 +
    slack295 / alpha296 ≤ 0
  norm_num [c26, hi, K590.fieldCap, K590.residualCap, cost296, lo, alpha296, slack295]

theorem hnear295 : hi - K590.residualCap + D58.nearCap ≤ 0 := by
  norm_num [hi, K590.residualCap, D58.nearCap]

/-- The end record of the second sheet. -/
def secondEnd295 : SecondTrialBoundsEnd Odd.design alpha296 T296 K590.residualCap D58.nearCap
    cost296 G58 :=
  second198 (second295.bounds Odd.design_admissible) slack295 slack295_nonneg
    hobj295 hcost295 hnear295

theorem hlarge295 : FreeLargeBound dc58.toParameters G58 T296 (58 * cost296) alpha296 :=
  freeLarge198 (second295.bounds Odd.design_admissible) slack295 slack295_nonneg
    hobj295 hcost295 hnear295

/-! ### Near sheet -/

/-- The ordinary and near caps of the source, at the exact fields. -/
theorem compact295 :
    (∀ σ, capSource.OrdCap Trunc.exact σ (CompactInstance.ordCapC σ)) ∧
      capSource.NearCap Trunc.exact CompactInstance.nearCapC := by
  obtain ⟨h1, h2⟩ := CompactInstance.compact_caps_384_seed capSource capSource_admissible
    capSource_eps_ge capSource_eps_le capSource_massL_pos_ge OrdHf.posHf OrdHf.negHf
    NearDataCert.nearHf_capSource
  exact ⟨fun σ => CompactCap.ordCap_exact capSource capSource_admissible (h1 σ),
    CompactCap.nearCap_exact capSource capSource_admissible h2⟩

/-- The angular caps at the exact fields, from the radius certificates of both species. -/
theorem angular295
    (certN : ∀ i, i < capSource.nRad →
      AngularCap.AngRadiusCert capSource Sign.neg i (5489 / 100000))
    (certP : ∀ i, i < capSource.nRad →
      AngularCap.AngRadiusCert capSource Sign.pos i (29557 / 200000)) :
    ∀ σ, capSource.AngCap Trunc.exact σ (kappa σ) := by
  intro σ i hi θ
  refine (AngularSource.angular_dominates capSource capSource_admissible 384 σ i hi θ).trans ?_
  cases σ
  · exact AngularCap.angCap_neg capSource capSource_admissible certN i hi θ
  · exact AngularCap.angCap_pos capSource capSource_admissible certP i hi θ

theorem hnearSheet295
    (hR : capSource.FreeRowCap Trunc.exact 0 (-2579777 / 1000000))
    (hC : capSource.FreeColCap 0 (-2946610 / 1000000))
    (hi : -InterceptSource.refQuad capSource 0 + CompletedGas.gasConst capSource ≤
      2367346 / 1000000)
    (certN : ∀ i, i < capSource.nRad →
      AngularCap.AngRadiusCert capSource Sign.neg i (5489 / 100000))
    (certP : ∀ i, i < capSource.nRad →
      AngularCap.AngRadiusCert capSource Sign.pos i (29557 / 200000)) :
    FreeNearBound dc58.toParameters G58 (CatalanMeasure.Signed.NodeSub tau58) T296
      (58 * cost296) alpha296 :=
  T4Instance.freeNear_anchor0 hR hC compact295.1 compact295.2 (angular295 certN certP)
    (by norm_num) (fun σ => by norm_num [CompactInstance.ordCapC])
    (by norm_num [CompactInstance.nearCapC]) hi secondEnd295 rfl
    (by change K590.normCap ≤ _; norm_num [K590.normCap])
    (by change K590.fieldCap ≤ _; norm_num [K590.fieldCap])
    (by norm_num [K590.residualCap]) (by norm_num [D58.nearCap])
    _ PhysicalPick.phaseHole

/-! ### Terminal theorem -/

/-- `μ(G) ≤ 295`, with the five named cap inputs at the source `capSource`. -/
theorem measure_295
    (hR : capSource.FreeRowCap Trunc.exact 0 (-2579777 / 1000000))
    (hC : capSource.FreeColCap 0 (-2946610 / 1000000))
    (hi : -InterceptSource.refQuad capSource 0 + CompletedGas.gasConst capSource ≤
      2367346 / 1000000)
    (certN : ∀ i, i < capSource.nRad →
      AngularCap.AngRadiusCert capSource Sign.neg i (5489 / 100000))
    (certP : ∀ i, i < capSource.nRad →
      AngularCap.AngRadiusCert capSource Sign.pos i (29557 / 200000)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(295 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  obtain ⟨lbC, gain, hg, hc⟩ := Count.LedgerContent.content
  exact catalan_irrationalityMeasure_295 _ _ hc
    (Count.WinCertGlue.eta295_lt_of_gain hg) hfirst295
    (hnearSheet295 hR hC hi certN certP) hlarge295 hweights295

end
end CatalanMeasure.GenD.Signed.RouteI.Terminal295

#print axioms CatalanMeasure.GenD.Signed.RouteI.Terminal295.hweights295
#print axioms CatalanMeasure.GenD.Signed.RouteI.Terminal295.hfirst295
#print axioms CatalanMeasure.GenD.Signed.RouteI.Terminal295.hlarge295
#print axioms CatalanMeasure.GenD.Signed.RouteI.Terminal295.compact295
#print axioms CatalanMeasure.GenD.Signed.RouteI.Terminal295.hnearSheet295
#print axioms CatalanMeasure.GenD.Signed.RouteI.Terminal295.measure_295
