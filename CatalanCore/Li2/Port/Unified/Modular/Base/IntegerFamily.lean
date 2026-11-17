/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/IntegerFamily.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.MomentArithmetic

set_option backward.privateInPublic true

@[expose] public section

/-! The polynomial quotient of the original rational family has integer coefficients. -/
open Polynomial
namespace CatalanCore.Li2.Port.Li2
noncomputable section

def integerD (m : ℕ) : ℤ[X] := ∏ j ∈ Finset.Icc 1 m, (X + C (j:ℤ))

lemma integerD_monic (m : ℕ) : (integerD m).Monic := by
  apply monic_prod_of_monic
  intro j _
  exact monic_X_add_C _

lemma integerD_map (m : ℕ) : (integerD m).map (Int.castRingHom ℚ) = D m := by
  simp only [integerD, D, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, Int.coe_castRingHom, Int.cast_natCast]

def integerPolynomialPart (n k : ℕ) : ℤ[X] :=
  (X^k * (integerD n)^3) /ₘ integerD (4*n)

theorem integerPolynomialPart_map (n k : ℕ) :
    (integerPolynomialPart n k).map (Int.castRingHom ℚ) = polynomialPart n k := by
  unfold integerPolynomialPart polynomialPart numerator
  rw [map_divByMonic _ (integerD_monic _)]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, integerD_map]

theorem polynomialPart_GV (p : ℕ) (n k : ℕ) : GV p (polynomialPart n k) 0 := by
  rw [← integerPolynomialPart_map]
  intro j
  rw [coeff_map]
  exact VG.intCast _

theorem polynomialPartMoment_VG (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) (n k : ℕ) :
    VG p (polynomialMoment (polynomialPart n k)) 0 :=
  polynomialMoment_VG_of_ne_three p hp3 _ (polynomialPart_GV p n k)

end
end CatalanCore.Li2.Port.Li2

end
