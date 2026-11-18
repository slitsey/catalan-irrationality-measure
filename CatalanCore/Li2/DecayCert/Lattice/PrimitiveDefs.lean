module
public import CatalanCore.Li2.DecayCert.Lattice.PolynomialIntegral
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section
structure LatticeMomentData (σ1 σ2 : Measure ℂ) (Y : ℝ) where
  c : ℕ → ℝ
  N : ℕ
  finite_coeff : ∀ k, N < k → c k=0
  nonneg : ∀ x ∈ Icc (-1:ℝ) 1, 0 ≤ CatalanCore.Zeta5.Potential.chebF c N x
  first_measure : σ1=CatalanCore.Tools.Joukowski.segMeasure (Y/2:ℂ) (Y/2:ℂ) c N
  y0 : ℝ
  y0_neg : y0 < 0
  supportRadius : ℝ
  supportRadius_nonneg : 0 ≤ supportRadius
  separated : supportRadius < -y0
  second_support : σ2 {y | supportRadius < ‖y-(y0:ℂ)‖}=0
noncomputable def LatticeMomentData.mpValue {σ1 σ2 Y}
    (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) (s : ℝ) : ℝ :=
  mp σ2 (d.y0:ℂ) (s:ℂ) K
noncomputable def ownUPoly {σ1 σ2 Y} (d : LatticeMomentData σ1 σ2 Y) : ℝ[X] :=
  (∑ k ∈ Finset.range d.N,
    Polynomial.C (d.c (k+1)/(k+1:ℕ))*Polynomial.Chebyshev.T ℝ ((k+1:ℕ):ℤ)).comp
      (Polynomial.C (-1)+Polynomial.C (2/Y)*Polynomial.X)
noncomputable def Gtilde (x : ℝ) : ℝ := x^2*Real.log x/2-x^2/4
noncomputable def multipolePrimitive (σ : Measure ℂ) (y0 s : ℝ) (K : ℕ) : ℝ :=
  -σ.real univ*((s-y0)*Real.log (s-y0)-(s-y0)) +
    (if 0 < K then (moment σ y0 1).re*Real.log (s-y0) else 0) +
    ∑ k ∈ Finset.Icc 2 K, (moment σ y0 k).re*(s-y0)^((1:ℤ)-k)/((k:ℝ)*(1-k))
noncomputable def latticePrimitive {σ1 σ2 Y} (z θ : ℝ)
    (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) (s : ℝ) : ℝ :=
  3*Gtilde (s+1)-Gtilde (s+4)-2*Gtilde s +
    (1-2*d.c 0*Real.log (4/Y)-θ)*s+Real.log |z| *s^2/2 -
      2*((ownUPoly d).integral.eval s)-2*multipolePrimitive σ2 d.y0 s K

#print axioms latticePrimitive
end
end CatalanCore.Li2.DecayCert
