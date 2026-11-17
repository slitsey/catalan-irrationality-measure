/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/PrimeRestrictedShift.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: commute p-adic cast/power simplification before integralRational unfolding; module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.RestrictedShift
public import CatalanCore.Li2.Port.Unified.Modular.Base.PadicParameterFunctional
public import CatalanCore.Li2.Port.Unified.Modular.Base.PrimeParameter

set_option backward.privateInPublic true

@[expose] public section

/-! The restricted-series shift identity for the actual parameter (-1/2)^p. -/
open Polynomial
open scoped BigOperators
namespace CatalanCore.Li2.Port.Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma integralParameterMoment_recurrence (z : ℚ) (hz0 : VG p z 0)
    (hz : VG p (z/(1-z)) 0) (hz1 : z ≠ 1) (k : ℕ) :
    integralParameterMoment z hz k = integralRational z hz0+integralRational z hz0*
      ∑ j ∈ Finset.range (k+1), (Nat.choose k j : ℤ_[p])*integralParameterMoment z hz j := by
  apply PadicInt.ext
  simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_sum, PadicInt.coe_natCast]
  change (parameterMoment z k : ℚ_[p]) = (z : ℚ_[p]) + (z : ℚ_[p]) *
    ∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℚ_[p]) * (parameterMoment z j : ℚ_[p])
  exact_mod_cast parameterMoment_full_recurrence z hz1 k

theorem padicParameterG_shift_scaled (z : ℚ) (hz0 : VG p z 0)
    (hz : VG p (z/(1-z)) 0) (hz1 : z ≠ 1)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) (k : ℕ) :
    (integralRational z hz0)^k*padicParameterG z hz (restrictedTranslate (k:ℤ_[p]) f) =
      padicParameterG z hz f-
      ∑ j ∈ Finset.range k, (integralRational z hz0)^(j+1)*restrictedEval ((j:ℤ_[p])+1) f :=
  restrictedMoment_shift_scaled (integralParameterMoment z hz) (integralRational z hz0)
    (integralParameterMoment_recurrence z hz0 hz hz1) f hf k

theorem padicParameterG_shift (z : ℚ) (hz0 : VG p z 0)
    (hz : VG p (z/(1-z)) 0) (hz1 : z ≠ 1) (hzne : z ≠ 0)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) (k : ℕ) :
    (padicParameterG z hz (restrictedTranslate (k:ℤ_[p]) f) : ℚ_[p]) =
      ((padicParameterG z hz f : ℚ_[p])-
        ∑ j ∈ Finset.range k, (z:ℚ_[p])^(j+1)*(restrictedEval ((j:ℤ_[p])+1) f : ℚ_[p]))/
        (z:ℚ_[p])^k := by
  have hzne' : (z:ℚ_[p]) ≠ 0 := by exact_mod_cast hzne
  apply (eq_div_iff (pow_ne_zero k hzne')).mpr
  have h := congrArg (fun a : ℤ_[p] => (a:ℚ_[p])) (padicParameterG_shift_scaled z hz0 hz hz1 f hf k)
  simp only [PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_sum] at h
  simpa only [integralRational, mul_comm] using! h

theorem primeRestrictedShift (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) (k : ℕ) :
    (padicParameterG (primeParameter p) (primeParameter_moment_integral hp2 hp3)
      (restrictedTranslate (k:ℤ_[p]) f) : ℚ_[p]) =
      ((padicParameterG (primeParameter p) (primeParameter_moment_integral hp2 hp3) f : ℚ_[p])-
        ∑ j ∈ Finset.range k, (primeParameter p:ℚ_[p])^(j+1)*
          (restrictedEval ((j:ℤ_[p])+1) f : ℚ_[p]))/(primeParameter p:ℚ_[p])^k := by
  have hu := primeParameter_unit hp2
  have hz0 : VG p (primeParameter p) 0 := Or.inr (by rw [hu.2]; norm_num)
  have hz1 : primeParameter p ≠ 1 := by
    intro h
    apply (primeParameter_one_sub_unit hp2 hp3).1
    rw [h, sub_self]
  exact padicParameterG_shift _ hz0 _ hz1 hu.1 f hf k

end
end CatalanCore.Li2.Port.Li2

end
