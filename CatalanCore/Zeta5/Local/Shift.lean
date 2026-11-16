module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import CatalanCore.Zeta5.Local.Reflect

@[expose] public section

/-!
# Row ZC03 (continued): the shift identity for `τ_X` on rational functions

For `g = A / ∏_{r ∈ Pl} (x - r)` regular at `0` (`0 ∉ Pl`), `g(x+1) - g(x)` has numerator
`shiftNum Pl A` over the pole set `Pl ∪ (Pl - 1)`, and

`tauX (shiftNum Pl A) (Pl ∪ shiftPoles Pl) = C (g⁗(0)/24)`,

where `g⁗(0)/24` is the coefficient of `x⁴` in the Taylor series `A · (∏(x - r))⁻¹` at `0`
(`PowerSeries.coeff 4`).
-/

open Finset Polynomial

namespace Apery

/-- The poles of `g(x+1)`: `r - 1` for `r ∈ Pl`. -/
def shiftPoles (Pl : Finset ℤ) : Finset ℤ := Pl.image fun r => r - 1

lemma shift_injective : Function.Injective fun r : ℤ => r - 1 := fun a b h => by
  simp only at h; omega

lemma prod_image_pred (S : Finset ℤ) :
    ∏ s ∈ S.image (fun r : ℤ => r - 1), (X - C (s : ℚ)) =
      (∏ s ∈ S, (X - C (s : ℚ))).comp (X + 1) := by
  rw [Finset.prod_image (fun a _ b _ h => shift_injective h), Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [sub_comp, X_comp, C_comp]
  push_cast
  simp only [C_sub, C_1]
  ring

/-- The numerator of `g(x+1) - g(x)` over the pole set `Pl ∪ shiftPoles Pl`. -/
noncomputable def shiftNum (Pl : Finset ℤ) (A : ℚ[X]) : ℚ[X] :=
  A.comp (X + 1) * ∏ s ∈ (Pl ∪ shiftPoles Pl) \ shiftPoles Pl, (X - C (s : ℚ)) -
    A * ∏ s ∈ (Pl ∪ shiftPoles Pl) \ Pl, (X - C (s : ℚ))

/-! ### The harmonic increment -/

lemma H5_dd_pred {r : ℤ} (hr : r ≠ 0) :
    H5 (dd (r - 1)) - H5 (dd r) = -1 / (r : ℚ) ^ 5 := by
  rcases lt_or_gt_of_ne hr with h | h
  · -- r ≤ -1: dd r = -r-1, dd (r-1) = -r
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ r = -(m : ℤ) := ⟨(-r).toNat, by omega, by omega⟩
    obtain ⟨hm1, rfl⟩ := hm
    have e1 : dd (-(m : ℤ) - 1) = m := by unfold dd; split_ifs <;> omega
    have e2 : dd (-(m : ℤ)) = m - 1 := by unfold dd; split_ifs <;> omega
    rw [e1, e2, H5_succ_eq hm1]
    have : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    push_cast
    field_simp
    ring
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ r = (m : ℤ) := ⟨r.toNat, by omega, by omega⟩
    obtain ⟨hm1, rfl⟩ := hm
    have e1 : dd ((m : ℤ) - 1) = m - 1 := by unfold dd; split_ifs <;> omega
    have e2 : dd (m : ℤ) = m := by unfold dd; split_ifs <;> omega
    rw [e1, e2, H5_succ_eq hm1]
    have : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    push_cast
    field_simp
    ring

/-! ### The series `1/(x - r)` -/

lemma coe_X_sub_C (r : ℚ) :
    ((X - C r : ℚ[X]) : PowerSeries ℚ) = PowerSeries.X - PowerSeries.C r := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sub, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C]

lemma constantCoeff_coe_X_sub_C (r : ℚ) (hr : r ≠ 0) :
    PowerSeries.constantCoeff ((X - C r : ℚ[X]) : PowerSeries ℚ) ≠ 0 := by
  rw [coe_X_sub_C]; simpa using hr

lemma inv_coe_X_sub_C (r : ℚ) (hr : r ≠ 0) :
    (((X - C r : ℚ[X]) : PowerSeries ℚ)⁻¹) = PowerSeries.mk fun n => -(r⁻¹) ^ (n + 1) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (constantCoeff_coe_X_sub_C r hr), coe_X_sub_C]
  ext n
  rw [mul_sub]
  rcases n with _ | n
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    field_simp
  · simp only [map_sub, PowerSeries.coeff_succ_mul_X, mul_comm _ (PowerSeries.C r),
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have h1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    linear_combination (r⁻¹ ^ (n + 1)) * h1

lemma coeff_inv_X_sub (r : ℚ) (hr : r ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (((X - C r : ℚ[X]) : PowerSeries ℚ)⁻¹) = -(r⁻¹) ^ (n + 1) := by
  rw [inv_coe_X_sub_C r hr, PowerSeries.coeff_mk]

/-! ### Products over the union of the pole sets -/

lemma prod_erase_sdiff {T U : Finset ℤ} (hTU : T ⊆ U) {t : ℤ} (ht : t ∈ T) :
    ∏ s ∈ U.erase t, (X - C (s : ℚ)) =
      (∏ s ∈ U \ T, (X - C (s : ℚ))) * ∏ s ∈ T.erase t, (X - C (s : ℚ)) := by
  have hs : T.erase t ⊆ U.erase t := Finset.erase_subset_erase t hTU
  have e : (U.erase t) \ (T.erase t) = U \ T := by
    ext s
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h2, fun h => h3 ⟨h1, h⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun h => h2 (h ▸ ht), h1⟩, fun h => h2 h.2⟩
  rw [← Finset.prod_sdiff hs, e]

lemma sum_rho_bar (Pl U : Finset ℤ) (hPU : Pl ⊆ U) (ρ : ℤ → ℚ) (F : ℤ → ℚ[X]) :
    ∑ s ∈ U, C (if s ∈ Pl then ρ s else 0) * F s = ∑ r ∈ Pl, C (ρ r) * F r := by
  rw [← Finset.sum_subset hPU (f := fun s => C (if s ∈ Pl then ρ s else 0) * F s)
    (fun s _ hs => by simp [hs])]
  exact Finset.sum_congr rfl fun r hr => by simp [hr]

lemma sum_rho_bar_shift (Pl U : Finset ℤ) (hPU : shiftPoles Pl ⊆ U) (ρ : ℤ → ℚ) (F : ℤ → ℚ[X]) :
    ∑ s ∈ U, C (if s + 1 ∈ Pl then ρ (s + 1) else 0) * F s = ∑ r ∈ Pl, C (ρ r) * F (r - 1) := by
  have h1 : ∑ r ∈ Pl, C (ρ r) * F (r - 1) =
      ∑ s ∈ shiftPoles Pl, C (if s + 1 ∈ Pl then ρ (s + 1) else 0) * F s := by
    unfold shiftPoles
    rw [Finset.sum_image (fun a _ b _ h => shift_injective h)]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp [hr]
  rw [h1]
  refine (Finset.sum_subset hPU fun s _ hs => ?_).symm
  have : s + 1 ∉ Pl := fun h => hs (Finset.mem_image.mpr ⟨s + 1, h, by omega⟩)
  simp [this]

lemma tau_sub (P Q : ℚ[X]) : tau (P - Q) = tau P - tau Q := by
  rw [sub_eq_add_neg, tau_add, tau_neg]; ring

lemma tau_shift_coeff (Q : ℚ[X]) : tau (Q.comp (X + 1) - Q) = Q.coeff 4 := by
  rw [tau_sub, tau_shift, ← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
  simp [Nat.descFactorial]

/-- **ZC03, shift**: for `g = A / ∏_{r ∈ Pl}(x - r)` regular at `0`,
`τ_X(g(x+1) - g(x)) = g⁗(0)/24`, the `x⁴` coefficient of the Taylor series of `g` at `0`. -/
theorem tauX_shift (A : ℚ[X]) (Pl : Finset ℤ) (h0 : (0 : ℤ) ∉ Pl) :
    tauX (shiftNum Pl A) (Pl ∪ shiftPoles Pl) =
      C (PowerSeries.coeff 4 ((A : PowerSeries ℚ) * ((piPl Pl : ℚ[X]) : PowerSeries ℚ)⁻¹)) := by
  classical
  set U := Pl ∪ shiftPoles Pl with hU
  set Q := polyPart A Pl with hQ
  set ρ : ℤ → ℚ := resP A Pl with hρ
  have hA := partial_fractionsP A Pl
  rw [← hQ, ← hρ] at hA
  have hsub0 : Pl ⊆ U := Finset.subset_union_left
  have hsub1 : shiftPoles Pl ⊆ U := Finset.subset_union_right
  set E₁ := ∏ s ∈ U \ shiftPoles Pl, (X - C (s : ℚ)) with hE1
  set E₀ := ∏ s ∈ U \ Pl, (X - C (s : ℚ)) with hE0
  have hPU0 : piPl U = E₀ * piPl Pl := (Finset.prod_sdiff hsub0).symm
  have hPU1 : piPl U = E₁ * piPl (shiftPoles Pl) := (Finset.prod_sdiff hsub1).symm
  have hpiS : piPl (shiftPoles Pl) = (piPl Pl).comp (X + 1) := by
    unfold piPl shiftPoles; exact prod_image_pred Pl
  -- the numerator of `g(x+1)`
  have hA1 : A.comp (X + 1) = Q.comp (X + 1) * piPl (shiftPoles Pl) +
      ∑ r ∈ Pl, C (ρ r) * ∏ s ∈ (shiftPoles Pl).erase (r - 1), (X - C (s : ℚ)) := by
    conv_lhs => rw [hA]
    rw [add_comp, mul_comp, sum_comp', hpiS]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [mul_comp, C_comp]
    congr 1
    unfold shiftPoles
    rw [← Finset.image_erase shift_injective, prod_image_pred]
  have hB : shiftNum Pl A = (Q.comp (X + 1) - Q) * piPl U +
      (∑ r ∈ Pl, C (ρ r) * ∏ s ∈ U.erase (r - 1), (X - C (s : ℚ)) -
        ∑ r ∈ Pl, C (ρ r) * ∏ s ∈ U.erase r, (X - C (s : ℚ))) := by
    have hdef : shiftNum Pl A = A.comp (X + 1) * E₁ - A * E₀ := rfl
    have hAE : A * E₀ = (Q * piPl Pl + ∑ r ∈ Pl, C (ρ r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ))) * E₀ := by
      rw [← hA]
    rw [hdef, hA1, hAE]
    have e1 : ∀ r ∈ Pl, (C (ρ r) * ∏ s ∈ (shiftPoles Pl).erase (r - 1), (X - C (s : ℚ))) * E₁ =
        C (ρ r) * ∏ s ∈ U.erase (r - 1), (X - C (s : ℚ)) := by
      intro r hr
      rw [prod_erase_sdiff hsub1 (Finset.mem_image.mpr ⟨r, hr, rfl⟩)]
      ring
    have e0 : ∀ r ∈ Pl, (C (ρ r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ))) * E₀ =
        C (ρ r) * ∏ s ∈ U.erase r, (X - C (s : ℚ)) := by
      intro r hr
      rw [prod_erase_sdiff hsub0 hr]
      ring
    rw [add_mul, Finset.sum_mul, Finset.sum_congr rfl e1, add_mul, Finset.sum_mul,
      Finset.sum_congr rfl e0]
    have hEq : E₀ * piPl Pl = E₁ * piPl (shiftPoles Pl) := hPU0.symm.trans hPU1
    have h3 : Q * piPl Pl * E₀ = Q * (E₁ * piPl (shiftPoles Pl)) := by rw [← hEq]; ring
    rw [h3, hPU1]
    ring
  -- decomposition over `U`
  have hdec : shiftNum Pl A = (Q.comp (X + 1) - Q) * piPl U +
      ∑ s ∈ U, C ((if s + 1 ∈ Pl then ρ (s + 1) else 0) - (if s ∈ Pl then ρ s else 0)) *
        ∏ t ∈ U.erase s, (X - C (t : ℚ)) := by
    rw [hB]
    congr 1
    simp only [C_sub, sub_mul, Finset.sum_sub_distrib]
    rw [sum_rho_bar_shift Pl U hsub1, sum_rho_bar Pl U hsub0]
  rw [tauX_of_decomp U _ _ _ hdec, tau_shift_coeff]
  -- the sum of the pole terms
  have hG : ∑ s ∈ U, C ((if s + 1 ∈ Pl then ρ (s + 1) else 0) - (if s ∈ Pl then ρ s else 0)) *
      (C (H5 (dd s)) - X) = ∑ r ∈ Pl, C (ρ r * (-1 / (r : ℚ) ^ 5)) := by
    simp only [C_sub, sub_mul, Finset.sum_sub_distrib]
    rw [sum_rho_bar_shift Pl U hsub1, sum_rho_bar Pl U hsub0, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr0 : r ≠ 0 := fun h => h0 (h ▸ hr)
    have := H5_dd_pred hr0
    rw [C_mul, ← this, C_sub]
    ring
  rw [hG]
  -- the Taylor coefficient
  have hP0 : PowerSeries.constantCoeff ((piPl Pl : ℚ[X]) : PowerSeries ℚ) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      coeff_zero_eq_eval_zero]
    unfold piPl
    rw [eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun r hr => ?_
    have hr0 : r ≠ 0 := fun h => h0 (h ▸ hr)
    simp [hr0]
  have coe_sum : ∀ (s : Finset ℤ) (f : ℤ → ℚ[X]),
      ((∑ i ∈ s, f i : ℚ[X]) : PowerSeries ℚ) = ∑ i ∈ s, (f i : PowerSeries ℚ) := by
    intro s f
    have := map_sum Polynomial.coeToPowerSeries.ringHom f s
    simpa only [Polynomial.coeToPowerSeries.ringHom_apply] using this
  have hPr : ∀ r ∈ Pl, ((∏ s ∈ Pl.erase r, (X - C (s : ℚ)) : ℚ[X]) : PowerSeries ℚ) *
      ((piPl Pl : ℚ[X]) : PowerSeries ℚ)⁻¹ =
      (((X - C (r : ℚ) : ℚ[X]) : PowerSeries ℚ))⁻¹ := by
    intro r hr
    have hr0' : r ≠ 0 := fun h => h0 (h ▸ hr)
    have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr0'
    rw [PowerSeries.eq_inv_iff_mul_eq_one (constantCoeff_coe_X_sub_C _ hr0)]
    have hpi : ((piPl Pl : ℚ[X]) : PowerSeries ℚ) =
        ((X - C (r : ℚ) : ℚ[X]) : PowerSeries ℚ) *
          ((∏ s ∈ Pl.erase r, (X - C (s : ℚ)) : ℚ[X]) : PowerSeries ℚ) := by
      unfold piPl
      rw [← Polynomial.coe_mul, Finset.mul_prod_erase Pl (fun s : ℤ => (X - C (s : ℚ))) hr]
    calc ((∏ s ∈ Pl.erase r, (X - C (s : ℚ)) : ℚ[X]) : PowerSeries ℚ) *
          ((piPl Pl : ℚ[X]) : PowerSeries ℚ)⁻¹ * ((X - C (r : ℚ) : ℚ[X]) : PowerSeries ℚ)
        = ((piPl Pl : ℚ[X]) : PowerSeries ℚ)⁻¹ * ((piPl Pl : ℚ[X]) : PowerSeries ℚ) := by
          rw [hpi]; ring
      _ = 1 := PowerSeries.inv_mul_cancel _ hP0
  have hser : (A : PowerSeries ℚ) * ((piPl Pl : ℚ[X]) : PowerSeries ℚ)⁻¹ =
      (Q : PowerSeries ℚ) + ∑ r ∈ Pl, PowerSeries.C (ρ r) *
        (((X - C (r : ℚ) : ℚ[X]) : PowerSeries ℚ))⁻¹ := by
    conv_lhs => rw [hA]
    rw [Polynomial.coe_add, coe_sum, add_mul, Finset.sum_mul, Polynomial.coe_mul, mul_assoc,
      PowerSeries.mul_inv_cancel _ hP0, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Polynomial.coe_mul, Polynomial.coe_C, mul_assoc, hPr r hr]
  have hs : ∑ r ∈ Pl, C (ρ r * (-1 / (r : ℚ) ^ 5)) = C (∑ r ∈ Pl, ρ r * (-1 / (r : ℚ) ^ 5)) :=
    (map_sum C _ _).symm
  have key : PowerSeries.coeff 4 ((A : PowerSeries ℚ) * ((piPl Pl : ℚ[X]) : PowerSeries ℚ)⁻¹) =
      Q.coeff 4 + ∑ r ∈ Pl, ρ r * (-1 / (r : ℚ) ^ 5) := by
    rw [hser, map_add, map_sum, Polynomial.coeff_coe]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr0' : r ≠ 0 := fun h => h0 (h ▸ hr)
    have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr0'
    rw [PowerSeries.coeff_C_mul, coeff_inv_X_sub _ hr0]
    ring
  rw [key, C_add, hs]

end Apery
