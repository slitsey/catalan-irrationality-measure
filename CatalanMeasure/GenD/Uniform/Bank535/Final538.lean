module

public import CatalanMeasure.GenD.Uniform.Bank535.Ledger6.Merge6
public import CatalanMeasure.GenD.Uniform.Bank540.Ledger5.Final5

@[expose] public section
set_option Elab.async false

/-!
# `μ(G) ≤ 538` (lane G6)

`measure_of_design` for `(58,9,3,5,3)` with the ledger `wins6` (gain `gain6 = gain5 + 43/1210 = 21.7223`,
adding the HY+ `s = 11` windows), `eta = 29.708`, `kappa = 538 / rho`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535
open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD.Uniform.Bank535.Ledger6
noncomputable section

theorem pay538' : payB 538 (29708 / 1000) :=
  payB_of _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eta538_lt : (29708 / 1000 : ℝ) < Bank540.tDelta - gDg gain6 :=
  eta_lt_of_gain _ _ (by have := gain6_ge; linarith)

/-- **`μ(G) ≤ 538`.** -/
theorem catalan_irrationalityMeasure_538 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(538 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have h := measure_of_design D58.Odd.design
    { B := 538
      Z := canonicalNormalizer design D58.Odd.design_admissible (famLB fams6) 79
        (by rw [D58.Odd.design_H]; norm_num)
      w := 3 / 4, ρ := Bank540.rho, η := 29708 / 1000, κ := 538 / Bank540.rho, δ := D58.delta
      pay := by
        rw [D58.n0_sub_g0]
        simpa [payB] using pay538'
      gD := gDg gain6
      D_growth := fun ε hε => by
        filter_upwards [partial_growth6 hε] with N hN
        unfold gDg
        convert hN using 2
      tΔ := Bank540.tDelta
      delta_small := Bank540.delta_small
      eta_le := eta538_lt
      nonvanishing := D58.nonvanishing_d58 D58.C3.c3_d58 }
  simpa [catalan] using h

end
end CatalanMeasure.GenD.Uniform.Bank535
#print axioms CatalanMeasure.GenD.Uniform.Bank535.catalan_irrationalityMeasure_538
