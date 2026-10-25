module
public import CatalanCore.Cert.QuarterCompute.ModelDefs
public import CatalanCore.Cert.QuarterCompute.DyadicIntervalInput
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.ModelCell
open CatalanCore.Cert.QuarterCompute.DyadicInterval

def H : Int := 281474976710656
def Z : Int := 1099511627776

def vInterval (p : Model.Params) (yl yh : Int) : Interval :=
  encloseFractions H (yl*(p.U : Int)-p.Y0*Z) (yh*(p.U : Int)-p.Y0*Z) (p.DY*Z)

def sigmaLower (p : Model.Params) (cs : List Int) (denom : Nat) (base : Int) (error : Nat)
    (yl yh : Int) : Int :=
  (-base)/562949953421312 +
    (horner H (coefficients H (denom : Int) cs) (vInterval p yl yh)).1 -
    ceilDiv (error : Int) 65536 - 268435968
end CatalanCore.Cert.QuarterCompute.ModelCell