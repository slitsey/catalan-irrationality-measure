module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedLits

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Moved column caps (G31): the certified cap literals

`cap0n, cap1n, cap2n` are numerators over `10^9` of the caps C0 (`F_C + k0`), C1 (`F_C + k0 + k1 + α_e g`) and
C2 (`F_C + k0 + k1 + α_1 g`), `g(s) = log(1 + (3/4) s)`, `α_e = 1/25`, `α_1 = 51/500`; each is the smallest value
on the `10^-9` grid above the maximum over the 386 units of the exact left-hand side of `finMv`.

kcost: no computation here.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved

def cap0n : ℤ := -2946694099
def cap1n : ℤ := -2888907917
def cap2n : ℤ := -2854213720

/-- The caps as rationals (`c0C, c1C, c2C` of `SigLits`). -/
def c0Cq : ℚ := cap0n / 1000000000
def c1Cq : ℚ := cap1n / 1000000000
def c2Cq : ℚ := cap2n / 1000000000

end CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved
