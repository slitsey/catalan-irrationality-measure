module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedLits

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Moved column caps (G31): the packed-Horner input polynomials are the Chebyshev monomial forms

kcost: 45 s per list measured (160 Chebyshev steps in the kernel), 2 lists, 8 Nov.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved

theorem b0_eq : b0 = bPoly m0.ws := by
  -- kcost: 45 s measured, 160 Chebyshev steps
  decide +kernel

theorem b1_eq : b1 = bPoly m1.ws := by
  -- kcost: 45 s measured, 160 Chebyshev steps
  decide +kernel

end CatalanMeasure.GenD.Signed.RouteI.ColCert.Moved
