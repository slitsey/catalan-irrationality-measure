module
public import CatalanMeasure.GenD.Signed.RouteI.Literals
public import CatalanMeasure.GenD.Signed.Gate

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58
noncomputable section

/-- **Payment at an exponent `B`** (design C literals `rho296`, `eta295`, `delta296`, `w = 3/5`,
`κ = B/ρ`): the six real inequalities of `PayW'` hold for every `B` in `[269.7551, 400]`.  The
lower end is the root of `53 ρ + 212 δ B = η B`, `269.75508`; the stated exponent is a parameter. -/
theorem pay_design {B : ℝ} (hB1 : (2697551 / 10000 : ℝ) ≤ B) (hB2 : B ≤ 400) :
    PayW' (3/5) (dc58.d0 : ℝ) rho296 eta295 (B/rho296) delta296 B := by
  have hr : rho296 = (139171704799 / 500000000 : ℝ) := rho296_eq
  have he : eta295 = (1093749 / 20000 : ℝ) := eta295_eq
  apply Signed.Generic.payB' dc58 (3/5) rho296 eta295 delta296 B
  all_goals norm_num [hr, he, delta296, dc58_d0]
  all_goals linarith [hB1, hB2]

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.pay_design
