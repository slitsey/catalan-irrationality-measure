module
public import CatalanCore.Cert.QuarterCompute.Polynomial
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.DyadicInterval
abbrev Interval := Int × Int

def add (a b : Interval) : Interval := (a.1+b.1,a.2+b.2)
def prodLo (a b : Interval) : Int := min (min (a.1*b.1) (a.1*b.2)) (min (a.2*b.1) (a.2*b.2))
def prodHi (a b : Interval) : Int := max (max (a.1*b.1) (a.1*b.2)) (max (a.2*b.1) (a.2*b.2))
def ceilDiv (a d : Int) : Int := -((-a)/d)
def mul (H : Int) (a b : Interval) : Interval := (prodLo a b/H,ceilDiv (prodHi a b) H)
def encloseRatio (H c d : Int) : Interval := (c*H/d,c*H/d+1)
def coefficients (H d : Int) (cs : List Int) : List Interval := cs.map (fun c => encloseRatio H c d)
def horner (H : Int) : List Interval → Interval → Interval
  | [], _ => (0,0)
  | c::cs, v => add c (mul H v (horner H cs v))
end CatalanCore.Cert.QuarterCompute.DyadicInterval