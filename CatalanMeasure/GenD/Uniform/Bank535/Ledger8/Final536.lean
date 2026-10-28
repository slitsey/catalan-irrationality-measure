module

public import CatalanMeasure.GenD.Uniform.Bank535.Ledger8.Merge10
public import CatalanMeasure.GenD.Uniform.Bank540.Ledger5.Final5
public import CatalanMeasure.GenD.Uniform.Bank535.Gate

@[expose] public section
set_option Elab.async false

/-!
# `μ(G) ≤ 536` (lane G6c)

`measure_of_design` for `(58,9,3,5,3)` with the ledger `wins10` (Theorem L* windows on
`(59/21, 3]` added to `wins9`; `gain10 ≥ 21.836`), `eta = 29.82`, `kappa = 536 / rho`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger8
open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD.Uniform.Bank535 CatalanMeasure.GenD.Uniform.Bank535.Ledger6
noncomputable section

theorem pay536' : payB 536 (2982 / 100) :=
  payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eta536_lt : (2982 / 100 : ℝ) < Bank540.tDelta - gDg gain10 :=
  eta_lt_of_gain _ _ (by have := gain10_ge; linarith)

/-- **`μ(G) ≤ 536`.** -/
theorem catalan_irrationalityMeasure_536 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(536 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have h := measure_of_design D58.Odd.design
    { B := 536
      Z := canonicalNormalizer design D58.Odd.design_admissible (famLB fams10) 79
        (by rw [D58.Odd.design_H]; norm_num)
      w := 3 / 4, ρ := Bank540.rho, η := 2982 / 100, κ := 536 / Bank540.rho, δ := D58.delta
      pay := by
        rw [D58.n0_sub_g0]
        simpa [payB] using pay536'
      gD := gDg gain10
      D_growth := fun ε hε => by
        filter_upwards [partial_growth10 hε] with N hN
        unfold gDg
        convert hN using 2
      tΔ := Bank540.tDelta
      delta_small := Bank540.delta_small
      eta_le := eta536_lt
      nonvanishing := D58.nonvanishing_d58 D58.C3.c3_d58 }
  simpa [catalan] using h

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger8
#print axioms CatalanMeasure.GenD.Uniform.Bank535.Ledger8.catalan_irrationalityMeasure_536
