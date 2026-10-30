module

public import CatalanMeasure.GenD.Uniform.Bank540.Ledger5.Merge5
public import CatalanMeasure.GenD.Uniform.Bank540.Decay.Providers540
public import CatalanMeasure.GenD.D58.C3.Cert
public import CatalanMeasure.GenD.D58.Final
public import CatalanMeasure.GenD.Final

@[expose] public section
set_option Elab.async false

/-!
# `μ(G) ≤ 540` (lane G5h)

`measure_of_design` for the design `(58,9,3,5,3)`: denominator side `partial_growth5` (ledger `wins5`, gain
`gain5 = 21.68676`), payments and decay by the gate `etaG = 29.596`, and the decay `delta_small` of `Providers540`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

theorem gate5 :
    PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B ∧
      etaG < Bank540.tDelta - gDg gain5 := gate gain5 gain5_ge

/-- **`μ(G) ≤ 540`.** -/
theorem catalan_irrationalityMeasure_540 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(540 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have h := measure_of_design D58.Odd.design
    { B := 540
      Z := canonicalNormalizer design D58.Odd.design_admissible (famLB fams5) 79
        (by rw [D58.Odd.design_H]; norm_num)
      w := 3 / 4, ρ := Bank540.rho, η := etaG, κ := Bank540.kappa, δ := D58.delta
      pay := by
        rw [D58.n0_sub_g0]
        simpa [Bank540.B] using gate5.1
      gD := gDg gain5
      D_growth := fun ε hε => by
        filter_upwards [partial_growth5 hε] with N hN
        unfold gDg
        convert hN using 2
      tΔ := Bank540.tDelta
      delta_small := Bank540.delta_small
      eta_le := gate5.2
      nonvanishing := D58.nonvanishing_d58 D58.C3.c3_d58 }
  simpa [catalan] using h

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger5
