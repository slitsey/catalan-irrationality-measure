module
public import CatalanCore.Cert.QuarterCompute.ModelCell
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.ModelCellCached
open CatalanCore.Cert.QuarterCompute.DyadicInterval
open CatalanCore.Cert.QuarterCompute.ModelCell

/-- The same fixed-point cell evaluation, with coefficient normalization supplied once. -/
def sigmaLower (p : Model.Params) (cints : List Interval)
    (base : Int) (error : Nat) (yl yh : Int) : Int :=
  (-base)/562949953421312 +
    (horner H cints (vInterval p yl yh)).1 -
    ceilDiv (error : Int) 65536 - 268435968

/-- A finite equality for the cached intervals suffices for the complete substitution. -/
theorem sigmaLower_eq (p : Model.Params) (cs : List Int) (denom : Nat)
    (cints : List Interval) (base : Int) (error : Nat) (yl yh : Int)
    (hc : cints = coefficients H (denom : Int) cs) :
    sigmaLower p cints base error yl yh =
      ModelCell.sigmaLower p cs denom base error yl yh := by
  subst cints
  rfl
end CatalanCore.Cert.QuarterCompute.ModelCellCached
#print axioms CatalanCore.Cert.QuarterCompute.ModelCellCached.sigmaLower_eq
