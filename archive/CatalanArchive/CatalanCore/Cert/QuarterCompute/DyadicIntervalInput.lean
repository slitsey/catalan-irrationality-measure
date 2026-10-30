module
public import CatalanCore.Cert.QuarterCompute.DyadicInterval
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.DyadicInterval

def scale48 : Int := 281474976710656
def encloseFractions (H lo hi d : Int) : Interval := (lo*H/d,ceilDiv (hi*H) d)
end CatalanCore.Cert.QuarterCompute.DyadicInterval