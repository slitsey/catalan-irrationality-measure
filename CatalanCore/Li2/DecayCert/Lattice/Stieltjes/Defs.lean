module
public import CatalanCore.Li2.DecayCert.Moments
public import CatalanCore.Li2.DecayCert.PolynomialList
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set
open scoped BigOperators
open CatalanCore.Li2.Decay
namespace CatalanCore.Li2.DecayCert
noncomputable section

/-- Frozen CHECKER-API:1438; the canonical arcsine polynomial moment. -/
def arcPolyMoment (p : ℚ[X]) : ℚ :=
  ∑ j ∈ Finset.range (p.natDegree+1), if Even j then
    p.coeff j*((j.choose (j/2):ℚ)/4^(j/2)) else 0

/-- Frozen CHECKER-API:1446. -/
def positiveArcMoment (ξ : ℚ) (k : ℕ) : ℚ :=
  arcPolyMoment ((Polynomial.C ξ-Polynomial.X)^k)

/-- Frozen CHECKER-API:1450; density is shifted BEFORE recurrence contraction. -/
def stieltjesQ (d : QSegment) (φ : ℚ) (k : ℕ) : ℚ :=
  let ξ := (φ+φ⁻¹)/2
  let B := d.density.comp (Polynomial.X-Polynomial.C ξ)
  d.half.1^(-(k:ℤ)) * ∑ i ∈ Finset.range (B.natDegree+1),
    B.coeff i*(if i≤k then momentRec φ (k-i) else positiveArcMoment ξ (i-k))

/-- Actual inverse moments of the positive source measure, including order zero. -/
def inverseMoment (σ : Measure ℂ) (y0 : ℝ) (k : ℕ) : ℝ :=
  ∫ s, (s.re-y0)^(-(k:ℤ)) ∂σ

/-- The coefficient sign is positive for U(y0+u); atom cells use u=-x-y0. -/
def stieltjesCoeffs (σ : Measure ℂ) (y0 : ℝ) (K : ℕ) : List ℝ :=
  (List.range (K+1)).map (fun k : ℕ =>
    if k=0 then U σ (y0:ℂ) else inverseMoment σ y0 k/(k:ℝ))

end
end CatalanCore.Li2.DecayCert
