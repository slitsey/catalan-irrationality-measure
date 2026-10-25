module
public import CatalanCore.Cert.QuarterCompute.FastAxisNode
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.AxisModelCell
open CatalanCore.Cert.QuarterCompute.ModelCell
open CatalanCore.Cert.QuarterCompute.DyadicInterval
open CatalanCore.Cert.QuarterCompute.FastNode

/-- This carrier is used only for x-interval parametrization, never for atom geometry. -/
def carrier (m : Model.Params) : Model.Params := ⟨m.U,m.X0,m.X0,m.DX,m.DX⟩
def vInterval (m : Model.Params) (xl xh : Int) : Interval :=
  ModelCell.vInterval (carrier m) xl xh
/-- Axis models incur no horizontal tube loss. -/
def sigmaLower (m : Model.Params) (cints : List Interval) (base : Int) (error : Nat)
    (xl xh : Int) : Int :=
  (-base)/562949953421312+(horner H cints (vInterval m xl xh)).1-ceilDiv (error : Int) 65536

def nodeOK (m : Model.Params) (cints : List Interval) (base : Int) (error : Nat) (b : QBox) : Bool :=
  decide (FastAxisNode.axisGeom b) &&
  decide (-H ≤ (vInterval m b.1.1 b.1.2.1).1 ∧ (vInterval m b.1.1 b.1.2.1).2 ≤ H) &&
  decide ((b.2.2.2.1 : Rat)/2^32 ≤ FastAxisNode.quarterAxisLB
    ((sigmaLower m cints base error b.1.1 b.1.2.1 : Int)/(2^48 : Rat))
    (FastAxisNode.axisUt b.1.1 b.1.2.1) (FastAxisNode.axisUt b.2.1 b.2.2.1))
end CatalanCore.Cert.QuarterCompute.AxisModelCell
