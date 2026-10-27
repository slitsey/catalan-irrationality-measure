module
public import CatalanCore.Uniform.NV.Antidifference
@[expose] public section
open Polynomial Finset
open CatalanCore.Arith.Hybrid.FiniteFieldCorank
open CatalanCore.Rect.CharZeroNV
namespace CatalanCore.Uniform.NV

/-- Exact denominator and numerator of a finite nonzero-residue pole table. -/
noncomputable def poleDenominator (S : Finset ℚ) : ℚ[X] := rootProduct S
noncomputable def poleNumerator (S : Finset ℚ) (c : ℚ → ℚ) : ℚ[X] := numerator S c

theorem degree_poleDenominator (S : Finset ℚ) : (poleDenominator S).natDegree = S.card :=
  natDegree_rootProduct S

theorem top_coefficient_poleNumerator (S : Finset ℚ) (c : ℚ → ℚ) :
    (poleNumerator S c).coeff (S.card-1) = ∑ a ∈ S,c a := by
  unfold poleNumerator numerator
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a ha
  rw [coeff_C_mul]
  have hm : (punctured S a).Monic := rootProduct_monic (S.erase a)
  have hd : (punctured S a).natDegree = S.card-1 := by
    change (rootProduct (S.erase a)).natDegree = _
    rw [natDegree_rootProduct,Finset.card_erase_of_mem ha]
  rw [← hd,coeff_natDegree,hm.leadingCoeff,mul_one]

/-- Balance removes precisely the leading numerator coefficient. -/
theorem degree_poleNumerator (S : Finset ℚ) (c : ℚ → ℚ) (hc : ∑ a ∈ S,c a = 0) :
    (poleNumerator S c).natDegree ≤ S.card-2 := by
  have hd := natDegree_numerator_le S c
  have hz := top_coefficient_poleNumerator S c
  rw [hc] at hz
  have hp := natDegree_le_pred hd hz
  simpa [Nat.sub_sub,poleNumerator] using hp

/-- Every pole in the half-open fundamental strip is isolated in its step orbit. -/
theorem pole_table_isolated (S : Finset ℚ) (c : ℚ → ℚ) (L a : ℚ)
    (hL : 0 < L) (ha : a ∈ S) (hca : c a ≠ 0)
    (hstrip : ∀ b ∈ S, -L ≤ b ∧ b < 0) :
    IsolatedStepPole L a (poleDenominator S) (poleNumerator S c) where
  step_ne_zero := ne_of_gt hL
  pole := by
    change (rootProduct S).eval a = 0
    rw [rootProduct_factor S ha]
    simp
  residue := by
    change (numerator S c).eval a ≠ 0
    rw [eval_numerator_punctured S c ha]
    exact mul_ne_zero hca (punctured_eval_ne_zero S a)
  forward n := by
    apply rootProduct_eval_ne_zero S
    intro hx
    have hb := (hstrip _ hx).2
    have haa := (hstrip a ha).1
    have hn : 0 ≤ (n:ℚ)*L := mul_nonneg (Nat.cast_nonneg n) hL.le
    nlinarith
  backward n := by
    apply rootProduct_eval_ne_zero S
    intro hx
    have hb := (hstrip _ hx).1
    have haa := (hstrip a ha).2
    have hn : 0 ≤ (n:ℚ)*L := mul_nonneg (Nat.cast_nonneg n) hL.le
    nlinarith

/-- The exported pole table gives the actual cleared reciprocal sum. -/
theorem pole_value_cleared (S : Finset ℚ) (c : ℚ → ℚ) (x : ℚ) (hx : x ∉ S) :
    (poleDenominator S).eval x * (∑ a ∈ S,c a/(x-a)) = (poleNumerator S c).eval x := by
  unfold poleDenominator poleNumerator numerator
  simp only [eval_finsetSum,eval_mul,eval_C,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hxa : x ≠ a := by intro h;exact hx (h ▸ ha)
  rw [punctured_eval_quotient S ha hxa]
  ring

/-- Exact first-jet identity for the same pole table; no analytic derivative
or unproved rational-function residue assertion is used. -/
theorem pole_jet_cleared (S : Finset ℚ) (c : ℚ → ℚ) (x : ℚ) (hx : x ∉ S) :
    (poleDenominator S).derivative.eval x * (∑ a ∈ S,c a/(x-a)) -
      (poleDenominator S).eval x * (∑ a ∈ S,c a/(x-a)^2) =
      (poleNumerator S c).derivative.eval x := by
  unfold poleDenominator poleNumerator numerator
  simp only [derivative_sum,derivative_mul,derivative_C,zero_mul,zero_add,
    eval_finsetSum,eval_mul,eval_C,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hxa : x-a ≠ 0 := sub_ne_zero.mpr (by intro h;exact hx (h ▸ ha))
  have he : (rootProduct S).eval x = (x-a)*(punctured S a).eval x := by
    rw [rootProduct_factor S ha]
    simp
  have he' : (rootProduct S).derivative.eval x =
      (punctured S a).eval x+(x-a)*(punctured S a).derivative.eval x := by
    rw [rootProduct_factor S ha,derivative_mul]
    simp
  rw [he,he']
  field_simp
  ring
end CatalanCore.Uniform.NV


