/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Positive/Packed/P020.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P019
public import CatalanCore.Li2.Port.Unified.Modular.Base.RationalPoleCongruence

set_option backward.privateInPublic true

@[expose] public section

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private theorem integer_fermat (z : ℤ) :
    CatalanCore.Li2.Port.Li2.VG p ((z : ℚ) ^ p - z) 1 := by
  have hmod : (((z ^ p - z : ℤ) : ZMod p)) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  have hdiv : (p : ℤ) ∣ z ^ p - z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
  simpa only [Int.cast_sub, Int.cast_pow] using CatalanCore.Li2.Port.Li2.VG.intCast_of_dvd hdiv

private theorem denominator_unit (q : ℚ) (hq : CatalanCore.Li2.Port.Li2.VG p q 0) :
    ¬p ∣ q.den := by
  by_cases hq0 : q = 0
  · subst q
    simpa using (Fact.out : p.Prime).ne_one
  intro hd
  have hcp : Nat.Coprime p q.num.natAbs :=
    (q.reduced.of_dvd_right hd).symm
  have hnp : ¬p ∣ q.num.natAbs :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcp
  have hni : ¬(p : ℤ) ∣ q.num := by
    simpa only [Int.natCast_dvd] using hnp
  have hvn : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hni
  have hvd : 1 ≤ padicValNat p q.den :=
    one_le_padicValNat_of_dvd q.den_ne_zero hd
  have hv : 0 ≤ padicValRat p q := by
    exact_mod_cast hq.resolve_left hq0
  rw [padicValRat_def, hvn] at hv
  omega

theorem rational_fermat (q : ℚ) (hq : CatalanCore.Li2.Port.Li2.VG p q 0) :
    CatalanCore.Li2.Port.Li2.VG p (q ^ p - q) 1 := by
  have hd : ¬p ∣ q.den := denominator_unit q hq
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdval : padicValRat p (q.den : ℚ) = 0 :=
    CatalanCore.Li2.Port.Unified.ParameterFamily.nat_valuation_zero q.den hd
  have hdpval : padicValRat p ((q.den : ℚ) ^ p) = 0 := by
    rw [padicValRat.pow, hdval]
    simp
  have hdi : CatalanCore.Li2.Port.Li2.VG p (q.den : ℚ)⁻¹ 0 :=
    CatalanCore.Li2.Port.Li2.rational_unit_inverse_VG _ hd0 hdval
  have hdpi : CatalanCore.Li2.Port.Li2.VG p ((q.den : ℚ) ^ p)⁻¹ 0 :=
    CatalanCore.Li2.Port.Li2.rational_unit_inverse_VG _ (pow_ne_zero _ hd0) hdpval
  have hnum : CatalanCore.Li2.Port.Li2.VG p ((q.num : ℚ) ^ p - q.num) 1 :=
    integer_fermat q.num
  have hden : CatalanCore.Li2.Port.Li2.VG p ((q.den : ℚ) ^ p - q.den) 1 := by
    simpa only [Int.cast_natCast] using (integer_fermat (p := p) (q.den : ℤ))
  have hi : CatalanCore.Li2.Port.Li2.VG p (((q.den : ℚ) ^ p)⁻¹ - (q.den : ℚ)⁻¹) 1 :=
    CatalanCore.Li2.Port.Li2.VG.inv_congr (pow_ne_zero _ hd0) hd0 hdpi hdi hden
  have hn : CatalanCore.Li2.Port.Li2.VG p (q.num : ℚ) 0 := CatalanCore.Li2.Port.Li2.VG.intCast q.num
  have hprod :
      CatalanCore.Li2.Port.Li2.VG p ((q.num : ℚ) ^ p * ((q.den : ℚ) ^ p)⁻¹ -
        (q.num : ℚ) * (q.den : ℚ)⁻¹) 1 :=
    CatalanCore.Li2.Port.Li2.VG.mul_congr hdpi hn hnum hi
  have he : q ^ p - q =
      (q.num : ℚ) ^ p * ((q.den : ℚ) ^ p)⁻¹ -
        (q.num : ℚ) * (q.den : ℚ)⁻¹ := by
    calc
      q ^ p - q = ((q.num : ℚ) / q.den) ^ p - ((q.num : ℚ) / q.den) := by
        simp only [Rat.num_div_den]
      _ = _ := by simp only [div_eq_mul_inv, mul_pow, inv_pow]
  rw [he]
  exact hprod

theorem one_sub_power_unit_of_hunit (lam : ℚ)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1 - lam ≠ 0 ∧ padicValRat p (1 - lam) = 0)) :
    1 - lam ^ p ≠ 0 ∧ padicValRat p (1 - lam ^ p) = 0 := by
  have hvg : CatalanCore.Li2.Port.Li2.VG p lam 0 := Or.inr (by rw [hunit.1.2]; norm_num)
  exact CatalanCore.Li2.Port.Unified.LambdaLift.one_sub_parameter_power_unit lam hunit.2
    (rational_fermat lam hvg)

#print axioms rational_fermat
#print axioms one_sub_power_unit_of_hunit

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

end


end
