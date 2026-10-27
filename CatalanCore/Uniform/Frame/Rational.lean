module
public import CatalanCore.Frame.Spec
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
@[expose] public section

namespace CatalanCore.Uniform
open Finset

/-- The paper's merged rational frame, with all normalization in `a`. -/
structure RationalFrame where
  d : ℕ
  hd : 2 ≤ d
  μ : Fin d → ℚ
  a : Fin d → ℚ
  hμ : ∀ i, 0 < μ i ∧ μ i ≤ 1
  hμinj : ∀ i j, i ≠ j → μ i ≠ μ j
  ha : ∀ i, a i ≠ 0
  hsum : ∑ i, a i = 0

namespace RationalFrame

def denominator (F : RationalFrame) : ℕ := ∏ i, (F.a i).den

theorem denominator_pos (F : RationalFrame) : 0 < F.denominator :=
  Finset.prod_pos fun i _ => (F.a i).den_pos

def weight (F : RationalFrame) (i : Fin F.d) : ℤ :=
  (F.a i).num * (F.denominator / (F.a i).den : ℕ)

theorem denominator_dvd (F : RationalFrame) (i : Fin F.d) :
    (F.a i).den ∣ F.denominator := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem weight_cast (F : RationalFrame) (i : Fin F.d) :
    (F.weight i : ℚ) = F.denominator * F.a i := by
  have hden : ((F.denominator / (F.a i).den : ℕ) : ℚ) * (F.a i).den = F.denominator := by
    exact_mod_cast Nat.div_mul_cancel (F.denominator_dvd i)
  have ha := Rat.num_div_den (F.a i)
  have hd : ((F.a i).den : ℚ) ≠ 0 := by exact_mod_cast (F.a i).den_ne_zero
  have hnum : (F.a i).num = F.a i * (F.a i).den :=
    (div_eq_iff hd).mp ha
  unfold weight
  push_cast
  rw [hnum]
  calc
    F.a i * (F.a i).den * (F.denominator / (F.a i).den : ℕ) =
        F.a i * ((F.denominator / (F.a i).den : ℕ) * (F.a i).den) := by ring
    _ = F.a i * F.denominator := by rw [hden]
    _ = F.denominator * F.a i := by ring

/-- Every rational coefficient frame has the existing integer-weight/positive
normalizer encoding. The unused contour fields are not asserted to satisfy
ContourGap; analytic adapters supply their own actual contour geometry. -/
def toFrame (F : RationalFrame) : Frame where
  d := F.d
  μ := F.μ
  w := F.weight
  norm := F.denominator
  xs := 0
  δ0 := 0
  n0off := 0
  hμ := F.hμ
  hμinj := F.hμinj
  hw := by
    have h : ∑ i, (F.weight i : ℚ) = 0 := by
      simp_rw [F.weight_cast]
      rw [← Finset.mul_sum, F.hsum, mul_zero]
    exact_mod_cast h
  hnorm := by exact_mod_cast F.denominator_pos

theorem coefficient (F : RationalFrame) (i : Fin F.d) :
    ((F.toFrame.w i : ℚ) / F.toFrame.norm) = F.a i := by
  change (F.weight i : ℚ) / F.denominator = _
  rw [F.weight_cast]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast F.denominator_pos.ne')

/-- No pole class is lost when transporting the merged rational frame. -/
theorem weight_ne_zero (F : RationalFrame) (i : Fin F.d) : F.toFrame.w i ≠ 0 := by
  intro h
  have := F.coefficient i
  rw [h, Int.cast_zero, zero_div] at this
  exact F.ha i this.symm

/-- The encoded frame has exactly the paper's target, including every rational
coefficient and companion term. -/
theorem const_eq (F : RationalFrame) :
    F.toFrame.const = ∑ i, (F.a i : ℝ) * hurwitzTail2 (F.μ i) := by
  unfold Frame.const
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hc : (F.toFrame.w i : ℝ) / (F.toFrame.norm : ℝ) = (F.a i : ℝ) := by
    exact_mod_cast F.coefficient i
  change (F.toFrame.w i : ℝ) * hurwitzTail2 (F.μ i) * (F.toFrame.norm : ℝ)⁻¹ = _
  calc
    _ = ((F.toFrame.w i : ℝ) / (F.toFrame.norm : ℝ)) * hurwitzTail2 (F.μ i) := by ring
    _ = _ := by rw [hc]

/-- Install any actual contour data without changing the exact normalized frame.
The analytic lane proves the required pole-gap predicates for these data. -/
def withContour (F : RationalFrame) (xs δ0 : ℚ) (offset : ℕ) : Frame :=
  { F.toFrame with xs := xs, δ0 := δ0, n0off := offset }

theorem withContour_const (F : RationalFrame) (xs δ0 : ℚ) (offset : ℕ) :
    (F.withContour xs δ0 offset).const =
      ∑ i, (F.a i : ℝ) * hurwitzTail2 (F.μ i) := F.const_eq

theorem withContour_Mn (F : RationalFrame) (xs δ0 : ℚ) (offset a b : ℕ) :
    (F.withContour xs δ0 offset).Mn a b = F.toFrame.Mn a b := rfl

end RationalFrame
end CatalanCore.Uniform




