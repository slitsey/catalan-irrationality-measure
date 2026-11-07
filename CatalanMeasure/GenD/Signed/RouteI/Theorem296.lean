module
public import CatalanMeasure.GenD.Signed.RouteI.Pay
public import CatalanMeasure.GenD.Signed.RouteI.FinalPrimed
public import CatalanMeasure.GenD.Signed.RouteI.Wrappers
public import CatalanMeasure.GenD.Signed.DecayOfData
public import CatalanMeasure.GenD.Uniform.Arithmetic.Exponents
public import CatalanMeasure.GenD.DesignInstance.Final
public import CatalanMeasure.GenD.DesignInstance.C3.Cert

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58 Analytic Filter Polynomial
open CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic

noncomputable section

/-! The whole-chain assembly with the terminal hypotheses explicit: the three sheet bounds with the
column factor `Z = (∏ (1 + ζ s))^m` and the node field `δ` (GP Theorems 4.3, 8.3), the weight bound
with `β_ζ` (GP Proposition 4.4), the payment at the stated exponent `μ : ℚ` and the content growth.
No cap certificate, inverse branch certificate or content input is asserted here; `μ`, `ζ`, `δ`,
`Cw`, `Psi0` stay parameters. -/
theorem catalan_irrationalityMeasure_of_nodes
    (tau : (N : ℕ) → Fin (dc58.d0 * N) → ℝ) (G : ℝ → Prop)
    (hinj : ∀ N, Function.Injective (tau N))
    (hmem : ∀ N a, tau N a ∈ Set.Ioo (-1:ℝ) 1)
    (hzero : ∀ N a, tau N a ≠ 0)
    (hsupport : ∀ N a, G (realCoordinate (tau N a)))
    (lb : NullityLB dc58.toParameters) (μ : ℚ) (eta price α1 ζ Cw : ℝ) (δ : ℝ → ℝ)
    (hζ : 0 < ζ) (hCw : 0 ≤ Cw)
    (hpay : PayW' (3/5) (dc58.d0:ℝ) rho296 eta ((μ:ℝ)/rho296) delta296 (μ:ℝ))
    (hcontent : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer dc58.toParameters dc58.admissible lb 79
        dc58_normalizer_cut).D N) ≤ (price+ε)*(N:ℝ)^2)
    (hgain : eta < 58^2*(T296-Real.log 2/2)-price)
    (hfirst : FreeFirstBoundZ dc58.toParameters G ζ δ T296 (58*cost296))
    (hnear : FreeNearBoundZ dc58.toParameters G (CatalanMeasure.Signed.NodeSub tau) ζ δ
      T296 (58*cost296) α1)
    (hlarge : FreeLargeBoundZ dc58.toParameters G ζ δ T296 (58*cost296) α1)
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
    hinj hmem hzero hsupport T296 cost296 psi296 α1 ζ Cw hζ hCw δ
    (by simpa only [dc58_n0, Nat.cast_ofNat] using hfirst)
    (by simpa only [dc58_n0, Nat.cast_ofNat] using hnear)
    (by simpa only [dc58_n0, Nat.cast_ofNat] using hlarge) hweights
  exact Signed.Generic.catalan_irrationalityMeasure_of_design' dc58
    { μ := μ
      Z := canonicalNormalizer dc58.toParameters dc58.admissible lb 79 dc58_normalizer_cut
      w := 3/5
      ρ := rho296
      η := eta
      κ := (μ:ℝ)/rho296
      δ := delta296
      pay := hpay
      gD := price
      D_growth := hcontent
      tΔ := 58^2*(T296-Real.log 2/2)
      delta_small := by simpa only [dc58_n0,Nat.cast_ofNat,rho296] using hsmall
      eta_le := hgain
      nonvanishing := nonvanishing_d58 C3.c3_d58 }

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.catalan_irrationalityMeasure_of_nodes
