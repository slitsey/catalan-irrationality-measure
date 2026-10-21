module
public import CatalanCore.Cert.SigmaQuarter.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6
def ptAtQ (k : ℕ) : Pt := pts.getD k (0, 0, 0)

def radiusOK (k : ℕ) : Bool :=
  decide ((ptAtQ k).1 ^ 2 + (ptAtQ k).2.1 ^ 2 ≤ (256 : ℤ) * (2 ^ 40) ^ 2)

def conjIndexQ (k : ℕ) : ℕ :=
  if k < 1000 then (if k % 2 = 0 then k + 1 else k - 1) else k

def conjOKQ (k : ℕ) : Bool :=
  decide (conjIndexQ k < pts.length) &&
    decide ((ptAtQ (conjIndexQ k)).1 = (ptAtQ k).1) &&
    decide ((ptAtQ (conjIndexQ k)).2.1 = -(ptAtQ k).2.1) &&
    decide ((ptAtQ (conjIndexQ k)).2.2 = (ptAtQ k).2.2) &&
    decide (conjIndexQ (conjIndexQ k) = k)


def pointCheck (k : ℕ) : Bool := radiusOK k && conjOKQ k
def checkChunk (r : ℕ) : List ℕ := (List.range 100).map (fun i => 100*r+i)
end CatalanCore.Cert.SigmaQuarter
