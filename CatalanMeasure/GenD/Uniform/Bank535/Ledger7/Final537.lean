module

public import CatalanMeasure.GenD.Uniform.Bank535.Ledger7.Merge9
public import CatalanMeasure.GenD.Uniform.Bank540.Ledger5.Final5
public import CatalanMeasure.GenD.Uniform.Bank535.Gate

@[expose] public section
set_option Elab.async false

/-!
# `μ(G) ≤ 537` (lane G6)

`measure_of_design` for `(58,9,3,5,3)` with the ledger `wins9` (HY+ s = 9, 10, 11 and HP2 windows, gain `gain9 = 21.78298`), `eta = 29.765`, `kappa = 537 / rho`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger7
open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD.Uniform.Bank535 CatalanMeasure.GenD.Uniform.Bank535.Ledger6
noncomputable section

theorem pay537' : payB 537 (29765 / 1000) :=
  payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eta537_lt : (29765 / 1000 : ℝ) < Bank540.tDelta - gDg gain9 :=
  eta_lt_of_gain _ _ (by have := gain9_ge; linarith)

/-- **`μ(G) ≤ 537`.** -/
theorem catalan_irrationalityMeasure_537 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(537 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have h := measure_of_design D58.Odd.design
    { B := 537
      Z := canonicalNormalizer design D58.Odd.design_admissible (famLB fams9) 79
        (by rw [D58.Odd.design_H]; norm_num)
      w := 3 / 4, ρ := Bank540.rho, η := 29765 / 1000, κ := 537 / Bank540.rho, δ := D58.delta
      pay := by
        rw [D58.n0_sub_g0]
        simpa [payB] using pay537'
      gD := gDg gain9
      D_growth := fun ε hε => by
        filter_upwards [partial_growth9 hε] with N hN
        unfold gDg
        convert hN using 2
      tΔ := Bank540.tDelta
      delta_small := Bank540.delta_small
      eta_le := eta537_lt
      nonvanishing := D58.nonvanishing_d58 D58.C3.c3_d58 }
  simpa [catalan] using h

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger7
#print axioms CatalanMeasure.GenD.Uniform.Bank535.Ledger7.catalan_irrationalityMeasure_537
