module
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.Polynomial
/-- Coefficient lists use increasing degree order. -/
def eval (x : Int) : List Int → Int
  | [] => 0
  | c::cs => c+x*eval x cs
end CatalanCore.Cert.QuarterCompute.Polynomial