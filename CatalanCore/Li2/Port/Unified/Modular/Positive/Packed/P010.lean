/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Positive/Packed/P010.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P001
public import CatalanCore.Li2.Port.Unified.Modular.Base.PrimePoleExtension
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P009

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial
namespace CatalanCore.Li2.Port.Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- A uniform carrier for every matching pole when the largest pole is below
`p²`. Unused centers may carry zero residue. -/
def generalPoleCenters : Fin p → ℤ_[p] := fun k => -(k.val : ℤ_[p])

theorem generalPoleCenters_injective : Function.Injective (generalPoleCenters (p := p)) := by
  intro i j h
  apply Fin.ext
  have he : (i.val : ℤ_[p]) = (j.val : ℤ_[p]) := neg_injective h
  exact_mod_cast he

def generalPoleU (z : ℚ) (hzUnit : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : CatalanCore.Li2.Port.Li2.VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p]) : (ℤ_[p])[X] :=
  CatalanCore.Li2.Port.Li2.restrictedPoleFunctional
    (fun n => (n + 1 : ℕ) * CatalanCore.Li2.Port.Li2.integralParameterMoment z hz n)
    (fun k : Fin p => CatalanCore.Li2.Port.Li2.integralUPole z hzUnit.1 hzUnit.2 k.val k.isLt)
    f r

def generalPoleV (z : ℚ) (hzUnit : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : CatalanCore.Li2.Port.Li2.VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p]) : (ℤ_[p])[X] :=
  CatalanCore.Li2.Port.Li2.restrictedPoleFunctional
    (CatalanCore.Li2.Port.Li2.derivativeMoments (CatalanCore.Li2.Port.Li2.integralParameterMoment z hz))
    (fun k : Fin p => CatalanCore.Li2.Port.Li2.integralVPole z hzUnit.1 hzUnit.2 k.val k.isLt)
    f r

theorem generalPoleU_coeff_bound (z : ℚ)
    (hzUnit : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : CatalanCore.Li2.Port.Li2.VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p])
    (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B)
    (hr : ∀ k, ‖r k‖ ≤ B) (n : ℕ) :
    ‖(generalPoleU z hzUnit hz f r).coeff n‖ ≤ B := by
  exact CatalanCore.Li2.Port.Li2.restrictedPoleFunctional_coeff_bound _ _ f r B hB hf hr n

theorem generalPoleV_coeff_bound (z : ℚ)
    (hzUnit : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : CatalanCore.Li2.Port.Li2.VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p])
    (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B)
    (hr : ∀ k, ‖r k‖ ≤ B) (n : ℕ) :
    ‖(generalPoleV z hzUnit hz f r).coeff n‖ ≤ B := by
  exact CatalanCore.Li2.Port.Li2.restrictedPoleFunctional_coeff_bound _ _ f r B hB hf hr n

theorem generalPoleUV_well_defined (z : ℚ)
    (hzUnit : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : CatalanCore.Li2.Port.Li2.VG p (z / (1 - z)) 0)
    (f g : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f)
    (hg : PowerSeries.IsRestricted 1 g)
    (r s : Fin p → ℤ_[p])
    (he : CatalanCore.Li2.Port.Li2.integralPoleNumerator (generalPoleCenters (p := p)) f r =
      CatalanCore.Li2.Port.Li2.integralPoleNumerator (generalPoleCenters (p := p)) g s) :
    generalPoleU z hzUnit hz f r = generalPoleU z hzUnit hz g s ∧
      generalPoleV z hzUnit hz f r = generalPoleV z hzUnit hz g s := by
  obtain ⟨rfl, rfl⟩ := CatalanCore.Li2.Port.Li2.integralPoleNumerator_injective
    _ generalPoleCenters_injective f g hf hg r s he
  exact ⟨rfl, rfl⟩

#print axioms generalPoleCenters_injective
#print axioms generalPoleU_coeff_bound
#print axioms generalPoleV_coeff_bound
#print axioms generalPoleUV_well_defined

end
end CatalanCore.Li2.Port.Unified.Proofs.Hermite

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Hermite
noncomputable section

def generalMatchingPoleIndex (p m j : ℕ) (a : Fin p)
    (hp : 0 < p) (hm : m < p * p) (hj : j ≤ m)
    (_hmod : j % p = a.val) : Fin p :=
  ⟨j / p, pole_index_window p m j hp hm hj⟩

theorem generalMatchingPole_denominator (p m j : ℕ) (a : Fin p)
    (hp : 0 < p) (hm : m < p * p) (hj : j ≤ m)
    (hmod : j % p = a.val) :
    (j : ℚ) - (a.val : ℚ) =
      (p : ℚ) * (generalMatchingPoleIndex p m j a hp hm hj hmod).val := by
  have hdec := pole_index_decompose p j
  rw [hmod] at hdec
  have hc := congrArg (fun v : ℕ => (v : ℚ)) hdec
  push_cast at hc
  dsimp [generalMatchingPoleIndex]
  linear_combination hc

theorem generalMatchingPole_center (p m j : ℕ) [Fact p.Prime] (a : Fin p)
    (hp : 0 < p) (hm : m < p * p) (hj : j ≤ m)
    (hmod : j % p = a.val) :
    generalPoleCenters (generalMatchingPoleIndex p m j a hp hm hj hmod) =
      -((j / p : ℕ) : ℤ_[p]) := rfl

#print axioms generalMatchingPole_denominator
#print axioms generalMatchingPole_center

end
end CatalanCore.Li2.Port.Unified.Proofs.Hermite

end

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Hermite
noncomputable section

def generalTailPoleSet (n p : ℕ) (a : Fin p) : Finset (Fin p) :=
  Finset.univ.filter (fun k =>
    n < a.val + p * k.val ∧ a.val + p * k.val ≤ 4 * n)

theorem generalTailPoleSet_mem_iff (n p : ℕ) (a k : Fin p)
    (hp : 0 < p) :
    k ∈ generalTailPoleSet n p a ↔
      ∃ j ∈ (Finset.Icc (n + 1) (4 * n)).filter
        (fun j => j % p = a.val), j / p = k.val := by
  constructor
  · intro hk
    have hb := (Finset.mem_filter.mp hk).2
    let j := a.val + p * k.val
    have hmod : j % p = a.val := by
      dsimp [j]
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    have hdiv : j / p = k.val := by
      dsimp [j]
      rw [Nat.add_mul_div_left a.val k.val hp]
      simp [Nat.div_eq_of_lt a.isLt]
    refine ⟨j, ?_, hdiv⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hb.2⟩, hmod⟩
  · rintro ⟨j, hj, hdiv⟩
    have hb := (Finset.mem_filter.mp hj).1
    have hmod := (Finset.mem_filter.mp hj).2
    have hdec := pole_index_decompose p j
    rw [hmod, hdiv] at hdec
    simp only [generalTailPoleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hb
    omega

#print axioms generalTailPoleSet_mem_iff

end
end CatalanCore.Li2.Port.Unified.Proofs.Hermite

end


end
