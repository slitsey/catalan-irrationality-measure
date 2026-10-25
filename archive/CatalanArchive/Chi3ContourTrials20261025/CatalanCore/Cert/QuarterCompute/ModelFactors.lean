module
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.ModelFactors

def inputScale : Nat := 1048576

def factorList (S : Nat) : List Int :=
  [0,
   -((360360*S^14 : Nat) : Int),
   ((180180*S^13 : Nat) : Int),
   -((120120*S^12 : Nat) : Int),
   ((90090*S^11 : Nat) : Int),
   -((72072*S^10 : Nat) : Int),
   ((60060*S^9 : Nat) : Int),
   -((51480*S^8 : Nat) : Int),
   ((45045*S^7 : Nat) : Int),
   -((40040*S^6 : Nat) : Int),
   ((36036*S^5 : Nat) : Int),
   -((32760*S^4 : Nat) : Int),
   ((30030*S^3 : Nat) : Int),
   -((27720*S^2 : Nat) : Int),
   ((25740*S : Nat) : Int),
   -24024]

def factors : List Int := factorList inputScale

def denominatorFor (S : Nat) : Nat := 2^33*S^15*360360

def denominator : Nat := denominatorFor inputScale
end CatalanCore.Cert.QuarterCompute.ModelFactors