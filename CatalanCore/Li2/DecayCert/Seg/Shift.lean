module
public import CatalanCore.Li2.DecayCert.Arithmetic
public import CatalanCore.Li2.DecayCert.RealCells
@[expose] public section
set_option Elab.async false
open Polynomial Set
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.Decay

/-- Row 4: the real Int Horner result carries its error without an output witness. -/
theorem taylorShiftF_computed_spec (S C E : ℤ) (p : List ℤ) (hS : 0<S) :
    (shiftComputed S C E p).value.length=p.length ∧
    (shiftComputed S C E p).error.length=p.length ∧ ∀j<p.length,
      |dec S (getI (shiftComputed S C E p).value j)-
        ((gridPoly S p).comp (Polynomial.C (dec S C)+Polynomial.C (dec S E)*Polynomial.X)).coeff j|≤
        (getQ (shiftComputed S C E p).error j:ℝ) := by
  apply taylorShiftF_spec S C E p
  simp [shiftCheck,hS]

/-- Row 4, Gaussian version: no comparison against supplied model coefficients. -/
theorem taylorShiftCF_computed_spec (S : ℤ) (C E : CI) (p : List CI) (hS : 0<S) :
    (cShiftComputed S C E p).value.length=p.length ∧
    (cShiftComputed S C E p).error.length=p.length ∧ ∀j<p.length,
      ‖ciValue S (ciGet (cShiftComputed S C E p).value j)-
        ((cGridPoly S p).comp (Polynomial.C (ciValue S C)+Polynomial.C (ciValue S E)*Polynomial.X)).coeff j‖≤
        (getQ (cShiftComputed S C E p).error j:ℝ) := by
  apply taylorShiftCF_spec S C E p
  simp [cShiftCheck,hS]

/-- Row 6: the own polynomial and its closed finite tail come from the source. -/
theorem ownPoly_computed_spec (d : SegmentData) (hpos : d.densityNonneg)
    (a b l r : ℝ) (hab : ∀u∈Icc l r,a+b*u∈Icc (-1:ℝ) 1) (J : ℕ) :
    let q:=d.ownPolynomial.comp (Polynomial.C a+Polynomial.C b*Polynomial.X)
    ∀u∈Icc l r,
      |P d.ν (d.M+d.h*(a+b*u:ℂ))-∑j∈Finset.range (J+1),q.coeff j*u^j|≤
        ∑j∈Finset.Icc (J+1) q.natDegree,|q.coeff j| *(max |l| |r|)^j := by
  exact ownPoly_cell d hpos a b l r hab J _ rfl

#print axioms taylorShiftF_computed_spec
#print axioms taylorShiftCF_computed_spec
#print axioms ownPoly_computed_spec
end CatalanCore.Li2.DecayCert.Seg

