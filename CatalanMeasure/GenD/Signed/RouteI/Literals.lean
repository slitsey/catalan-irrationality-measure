module
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.DesignInstance.PositiveBudget

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58 CatalanMeasure.Parametric
noncomputable section

/-! Design C literals (config C, K = 160, per-radius mix; `DESIGN-C-CLOSE-2026-11-07.md`,
`G-UNDER-270-2026-11-07.md`).  The gain is `shift296 = 24.64`, the content constant is the kept
`content295`, `sigma296 = .33814269`.  None of these fixes the stated exponent: `μ` is a parameter of
the theorem modules and of `Pay`. -/
def content295 : ℝ := 220607/10000
def shift296 : ℝ := 616 / 25
def eta295 : ℝ := 798775/100000 + content295 + shift296 - 1/1000
def G58 (x : ℝ) : Prop := x≤-19501/100000 ∨ (98749/1000000:ℝ)≤x
def T296 : ℝ := K590.target + shift296 / 58 ^ 2
def sigma296 : ℝ := 33814269 / 100000000
def cost296 : ℝ := 3596893 / 1000000 + sigma296
def psi296 : ℝ := 50111339578 / 1000000000
def rho296 : ℝ := 58 * cost296 + psi296
def alpha296 : ℝ := 51 / 500
def delta296 : ℝ := 29 / 100000000

theorem rho296_eq : rho296 = (139171704799 / 500000000 : ℝ) := by
  norm_num [rho296, cost296, sigma296, psi296]

theorem eta295_eq : eta295 = (1093749 / 20000 : ℝ) := by
  norm_num [eta295, content295, shift296]

theorem dc58_normalizer_cut : dc58.toParameters.H 1 < 79 := by
  norm_num [dc58, Parameters.H, Parameters.C, Parameters.L,
    Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.rho296_eq
#print axioms CatalanMeasure.GenD.Signed.RouteI.eta295_eq
#print axioms CatalanMeasure.GenD.Signed.RouteI.dc58_normalizer_cut




