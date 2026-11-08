module
public import CatalanMeasure.GenD.Signed.RouteI.Literals
public import CatalanMeasure.GenD.Signed.RouteI.Pay
public import CatalanMeasure.GenD.Signed.RouteI.Theorem296

@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58 Analytic Filter Polynomial
open CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

/-! Design C with the raised budget constant (t4leaf, 8 Nov 2026): the signed piece 1 of the T4 cover
needs `σ ≥ 0.338704` with the certified intercept cap `2366997/10^6` (`GasEnergyHi.hi_final`).  The
active constant is `sigmaC = 33871/10^5`; `Literals.sigma296 = 33814269/10^8` is kept only for the
295/296 modules. -/
def sigmaC : ℝ := 33871 / 100000
def costC : ℝ := 3596893 / 1000000 + sigmaC
def rhoC : ℝ := 58 * costC + psi296

theorem rhoC_eq : rhoC = (139188156789 / 500000000 : ℝ) := by
  norm_num [rhoC, costC, sigmaC, psi296]

/-- **Payment at an exponent `B`** with `rhoC`: the six real inequalities of `PayW'` hold for every
`B` in `[269.787, 400]` (lower end: the root `269.78697` of `53 ρ + 212 δ B = η B`). -/
theorem pay_designC {B : ℝ} (hB1 : (269787 / 1000 : ℝ) ≤ B) (hB2 : B ≤ 400) :
    PayW' (3/5) (dc58.d0 : ℝ) rhoC eta295 (B/rhoC) delta296 B := by
  have hr : rhoC = (139188156789 / 500000000 : ℝ) := rhoC_eq
  have he : eta295 = (1093749 / 20000 : ℝ) := eta295_eq
  apply Signed.Generic.payB' dc58 (3/5) rhoC eta295 delta296 B
  all_goals norm_num [hr, he, delta296, dc58_d0]
  all_goals linarith [hB1, hB2]

/-- `Theorem296.catalan_irrationalityMeasure_of_nodes` with `rhoC`, `costC` (same proof). -/
theorem catalan_irrationalityMeasure_of_nodes_C
    (tau : (N : ℕ) → Fin (dc58.d0 * N) → ℝ) (G : ℝ → Prop)
    (hinj : ∀ N, Function.Injective (tau N))
    (hmem : ∀ N a, tau N a ∈ Set.Ioo (-1:ℝ) 1)
    (hzero : ∀ N a, tau N a ≠ 0)
    (hsupport : ∀ N a, G (realCoordinate (tau N a)))
    (lb : NullityLB dc58.toParameters) (μ : ℚ) (eta price α1 ζ Cw : ℝ) (δ : ℝ → ℝ)
    (hζ : 0 < ζ) (hCw : 0 ≤ Cw)
    (hpay : PayW' (3/5) (dc58.d0:ℝ) rhoC eta ((μ:ℝ)/rhoC) delta296 (μ:ℝ))
    (hcontent : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer dc58.toParameters dc58.admissible lb 79
        dc58_normalizer_cut).D N) ≤ (price+ε)*(N:ℝ)^2)
    (hgain : eta < 58^2*(T296-Real.log 2/2)-price)
    (hfirst : FreeFirstBoundZ dc58.toParameters G ζ δ T296 (58*costC))
    (hnear : FreeNearBoundZ dc58.toParameters G (CatalanMeasure.Signed.NodeSub tau) ζ δ
      T296 (58*costC) α1)
    (hlarge : FreeLargeBoundZ dc58.toParameters G ζ δ T296 (58*costC) α1)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p+m=dc58.toParameters.n N →
      ∀ k : ℕ, k<dc58.toParameters.n N → ∀ a : Fin (dc58.d0 * N),
      |(rowCommonFactor dc58.toParameters N).eval (tau N a)| *
        |restrictedWeight dc58.toParameters N k (tau N) a| *
        CatalanMeasure.zetaBeta ζ p m k ≤
          Cw*(N:ℝ)*Real.exp ((psi296 + δ (tau N a))*N)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b:ℝ)^(-(μ:ℝ)) <
        |(∑' j : ℕ, (-1:ℝ)^j/((2*j+1:ℕ):ℝ)^2)-a/b| := by
  have hsmall := Data.Assembly.Generic.delta_small_nodes dc58 tau G
    hinj hmem hzero hsupport T296 costC psi296 α1 ζ Cw hζ hCw δ
    (by simpa only [dc58_n0, Nat.cast_ofNat] using hfirst)
    (by simpa only [dc58_n0, Nat.cast_ofNat] using hnear)
    (by simpa only [dc58_n0, Nat.cast_ofNat] using hlarge) hweights
  exact Signed.Generic.catalan_irrationalityMeasure_of_design' dc58
    { μ := μ
      Z := canonicalNormalizer dc58.toParameters dc58.admissible lb 79 dc58_normalizer_cut
      w := 3/5
      ρ := rhoC
      η := eta
      κ := (μ:ℝ)/rhoC
      δ := delta296
      pay := hpay
      gD := price
      D_growth := hcontent
      tΔ := 58^2*(T296-Real.log 2/2)
      delta_small := by simpa only [dc58_n0,Nat.cast_ofNat,rhoC] using hsmall
      eta_le := hgain
      nonvanishing := nonvanishing_d58 C3.c3_d58 }

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.rhoC_eq
#print axioms CatalanMeasure.GenD.Signed.RouteI.pay_designC
#print axioms CatalanMeasure.GenD.Signed.RouteI.catalan_irrationalityMeasure_of_nodes_C
