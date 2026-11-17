/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Positive/Packed/P046.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P042

set_option backward.privateInPublic true

@[expose] public section

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section

open CatalanCore.Li2.Port.Unified.ParameterFamily CatalanCore.Li2.Port.Unified.Instances.PosHalf

/-- The good-prime fallback at the actual positive-half parameter and prime three. -/
theorem posHalf_three_adic_good_fallback (n : ℕ) (hn : 1 ≤ n) :
    CatalanCore.Li2.Port.Li2.GV 3 (Instances.PosHalf.Qtilde n)
      (-((4*n*Nat.log 3 (7*n-2):ℕ):ℚ)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hu := inverseParameter_unit (p := 3) 2 (by norm_num) (by norm_num)
  have hlam : CatalanCore.Li2.Port.Li2.VG 3 lambda 0 := by
    rw [lambda_eq_inverse]
    right
    rw [hu.2]
    norm_num
  have hinv : CatalanCore.Li2.Port.Li2.VG 3 lambda⁻¹ 0 := by
    rw [lambda_eq_inverse]
    exact CatalanCore.Li2.Port.Li2.rational_unit_inverse_VG (inverseParameter 2) hu.1 hu.2
  have hratio : CatalanCore.Li2.Port.Li2.VG 3 (lambda/(1-lambda)) 0 := by
    rw [lambda_eq_inverse]
    exact inverseParameter_moment_integral 2 (by norm_num) (by norm_num) (by norm_num)
  have h := Qtilde_GV_good_fallback 3 lambda lambda_ne_one hratio hlam hinv hn
  convert! h using 1 <;> push_cast <;> ring

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.posHalf_three_adic_good_fallback

end


end
