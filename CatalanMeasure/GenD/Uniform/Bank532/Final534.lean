module

public import CatalanMeasure.GenD.Uniform.Bank532.Ledger534

@[expose] public section
set_option Elab.async false

/-! `μ(G) ≤ 534`, conditional on the packet hosts `Hosts534` (G8d supplies them). -/

namespace CatalanMeasure.GenD.Uniform.Bank532
open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank535
noncomputable section

/-- **`μ(G) ≤ 534`** given the physical hosts of the 1 packets. -/
theorem catalan_irrationalityMeasure_534_of_hosts (H : Hosts534) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(534 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  have h := measure_of_design D58.Odd.design
    { B := 534
      Z := canonicalNormalizer design D58.Odd.design_admissible (famLB (fams534 H)) 79
        (by rw [D58.Odd.design_H]; norm_num)
      w := 3 / 4, ρ := Bank540.rho, η := 2993 / 100, κ := 534 / Bank540.rho, δ := D58.delta
      pay := by
        rw [D58.n0_sub_g0]
        simpa [payB] using pay534
      gD := gDg gain534
      D_growth := fun ε hε => by
        filter_upwards [partial_growth534 H hε] with N hN
        unfold gDg
        convert hN using 2
      tΔ := Bank540.tDelta
      delta_small := Bank540.delta_small
      eta_le := gain_ok534 _ gain534_ge
      nonvanishing := D58.nonvanishing_d58 D58.C3.c3_d58 }
  simpa [catalan] using h

end
end CatalanMeasure.GenD.Uniform.Bank532
#print axioms CatalanMeasure.GenD.Uniform.Bank532.catalan_irrationalityMeasure_534_of_hosts
