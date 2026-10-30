import CatalanCore.Uniform.Bank.Sevenths.Geom
import CatalanCore.Uniform.Bank.Sevenths.Frame
import CatalanCore.Uniform.Content.BankShared.AltCrude
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.BankShared

/-- Every member at an even scale has a valid crude clearing exponent at every
prime, including 2, 3, 5, 7 and all primes dividing a later certificate modulus.
No simple-pole assumption is used. -/
theorem sevenths_gle_Ecrude (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] :
    GLE p (Ecrude (cFr (seventhsFrameAt a)) i.1 p)
      ((F7.family (seventhsFrameAt a) depth).Q i) :=
  altGeom_gle_Ecrude (1 / 6) one_sixth_pos (by norm_num)
    (seventhsFrameAt a) depth i hr p

#print axioms sevenths_gle_Ecrude
end CatalanCore.Uniform.Bank.Sevenths
