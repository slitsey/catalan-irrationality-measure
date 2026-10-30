module

public import CatalanMeasure.GenD.Uniform.Bank535.Ledger10.Merge12
public import CatalanMeasure.GenD.Uniform.Bank540.Ledger5.Final5
public import CatalanMeasure.GenD.Uniform.Bank535.Gate

@[expose] public section
set_option Elab.async false

/-!
# `μ(G) ≤ 535` (lane G6e)

`measure_of_design` for `(58,9,3,5,3)` with the ledger `wins12` (Theorem C windows on
`(58/17, 59/17] ∪ (29/8, 11/3]` added to `wins11`; `gain12 ≥ 21.8855`), `eta = 29.873`,
`kappa = 535 / rho`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger10
open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD.Uniform.Bank535
noncomputable section

theorem pay535_b : payB 535 (29873 / 1000) :=
  payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eta535_lt : (29873 / 1000 : ℝ) < Bank540.tDelta - gDg gain12 :=
  eta_lt_of_gain _ _ (by have := gain12_ge; linarith)

/-- **`μ(G) ≤ 535`.** -/
theorem catalan_irrationalityMeasure_535 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(535 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have h := measure_of_design D58.Odd.design
    { B := 535
      Z := canonicalNormalizer design D58.Odd.design_admissible (famLB fams12) 79
        (by rw [D58.Odd.design_H]; norm_num)
      w := 3 / 4, ρ := Bank540.rho, η := 29873 / 1000, κ := 535 / Bank540.rho, δ := D58.delta
      pay := by
        rw [D58.n0_sub_g0]
        simpa [payB] using pay535_b
      gD := gDg gain12
      D_growth := fun ε hε => by
        filter_upwards [partial_growth12 hε] with N hN
        unfold gDg
        convert hN using 2
      tΔ := Bank540.tDelta
      delta_small := Bank540.delta_small
      eta_le := eta535_lt
      nonvanishing := D58.nonvanishing_d58 D58.C3.c3_d58 }
  simpa [catalan] using h

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger10
#print axioms CatalanMeasure.GenD.Uniform.Bank535.Ledger10.catalan_irrationalityMeasure_535
