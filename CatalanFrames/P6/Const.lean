module

public import CatalanCore.Frame.Spec
public import CatalanFrames.P6.Frame
public import CatalanFrames.P6.Series

/-!
# The constant of the P6 frame (WP9)

`p6Frame.const = L(2, χ₋₃) / 4`, with `L(2, χ₋₃)` the explicit series `chi3L2` of
`CatalanFrames.P6.Series`.

No Hurwitz zeta function and no value of `ζ(2)` is used.  Put `Z = ∑ 1/n²`, `a = ∑ 1/(3k+1)²`,
`b = ∑ 1/(3k+2)²`, `o = ∑ 1/(2k+1)²`.  Splitting `ℕ` into residue classes mod 3 and mod 2 gives
`Z = Z/9 + a + b` and `Z = Z/4 + o`, and then
`ζ(2,1) + 2ζ(2,1/3) - 3ζ(2,1/2) = Z + 18 a - 12 o = 18 a - 8 Z = 9 (a - b)`
(the `π²` terms cancel because `Z` is eliminated algebraically).
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.P6

/-- Residue-class splitting: if `f` sums to `s` over `ℕ` then `∑_k ∑_{j<n} f (k n + j) = s`. -/
theorem hasSum_split {f : ℕ → ℝ} {s : ℝ} (hf : HasSum f s) (n : ℕ) [NeZero n] :
    HasSum (fun k : ℕ => ∑ j : Fin n, f (k * n + j)) s := by
  have := (Nat.divModEquiv n).symm.hasSum_iff.mpr hf
  refine this.prod_fiberwise fun k => ?_
  exact hasSum_fintype _

private theorem S_zero_mul (k : ℕ) (n : ℕ) (hn : 0 < n) :
    1 / ((n * k : ℕ) : ℝ) ^ 2 = (1 / (n : ℝ) ^ 2) * (1 / (k : ℝ) ^ 2) := by
  push_cast; rw [mul_pow]; field_simp

/-- `∑ 1/(n k)² = (1/n²) ∑ 1/k²`. -/
private theorem tsum_mul_class (n : ℕ) (hn : 0 < n) :
    ∑' k : ℕ, 1 / ((n * k : ℕ) : ℝ) ^ 2 = (1 / (n : ℝ) ^ 2) * ∑' k : ℕ, 1 / (k : ℝ) ^ 2 := by
  rw [← tsum_mul_left]
  exact tsum_congr fun k => S_zero_mul k n hn

/-- `Z = Z/9 + a + b`. -/
theorem split_three :
    ∑' n : ℕ, 1 / (n : ℝ) ^ 2 = (1 / 9) * (∑' n : ℕ, 1 / (n : ℝ) ^ 2)
      + (∑' k : ℕ, 1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2) + ∑' k : ℕ, 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2 := by
  have h := hasSum_split summable_inv_sq.hasSum 3
  have e := h.tsum_eq
  simp only [Fin.sum_univ_three] at e
  have hs0 : Summable (fun k : ℕ => 1 / ((3 * k : ℕ) : ℝ) ^ 2) := by
    simpa using summable_inv_sq_three 0
  have key : ∀ k : ℕ, (1 / ((k * 3 + ((0 : Fin 3) : ℕ) : ℕ) : ℝ) ^ 2 +
      1 / ((k * 3 + ((1 : Fin 3) : ℕ) : ℕ) : ℝ) ^ 2 + 1 / ((k * 3 + ((2 : Fin 3) : ℕ) : ℕ) : ℝ) ^ 2)
      = 1 / ((3 * k : ℕ) : ℝ) ^ 2 + 1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2
        + 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2 := by
    intro k
    have : k * 3 = 3 * k := by ring
    simp [this]
  simp_rw [key] at e
  rw [(hs0.add (summable_inv_sq_three 1)).tsum_add (summable_inv_sq_three 2),
    hs0.tsum_add (summable_inv_sq_three 1), tsum_mul_class 3 (by norm_num)] at e
  rw [show (1 / ((3 : ℕ) : ℝ) ^ 2) = 1 / 9 by norm_num] at e
  linarith

/-- `Z = Z/4 + o`. -/
theorem split_two :
    ∑' n : ℕ, 1 / (n : ℝ) ^ 2 = (1 / 4) * (∑' n : ℕ, 1 / (n : ℝ) ^ 2)
      + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
  have h := hasSum_split summable_inv_sq.hasSum 2
  have e := h.tsum_eq
  simp only [Fin.sum_univ_two] at e
  have inj : ∀ r : ℕ, Summable (fun k : ℕ => 1 / ((2 * k + r : ℕ) : ℝ) ^ 2) := by
    intro r
    have hinj : Function.Injective (fun k : ℕ => 2 * k + r) := by
      intro a b h; simp at h; omega
    exact summable_inv_sq.comp_injective hinj
  have hs0 : Summable (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) := by simpa using inj 0
  have key : ∀ k : ℕ, (1 / ((k * 2 + ((0 : Fin 2) : ℕ) : ℕ) : ℝ) ^ 2 +
      1 / ((k * 2 + ((1 : Fin 2) : ℕ) : ℕ) : ℝ) ^ 2)
      = 1 / ((2 * k : ℕ) : ℝ) ^ 2 + 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
    intro k
    have : k * 2 = 2 * k := by ring
    simp [this]
  simp_rw [key] at e
  rw [hs0.tsum_add (inj 1), tsum_mul_class 2 (by norm_num)] at e
  rw [show (1 / ((2 : ℕ) : ℝ) ^ 2) = 1 / 4 by norm_num] at e
  linarith

/-- `ζ(2, 1) = Z`. -/
theorem hurwitz_one : hurwitzTail2 1 = ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
  unfold hurwitzTail2
  rw [summable_inv_sq.tsum_eq_zero_add]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
    zero_add]
  push_cast
  rfl

/-- `ζ(2, 1/3) = 9 a`. -/
theorem hurwitz_third : hurwitzTail2 (1 / 3) = 9 * ∑' k : ℕ, 1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 := by
  unfold hurwitzTail2
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  push_cast
  have : (3 : ℝ) * k + 1 ≠ 0 := by positivity
  have : (k : ℝ) + 1 / 3 ≠ 0 := by positivity
  field_simp
  norm_num

/-- `ζ(2, 1/2) = 4 o`. -/
theorem hurwitz_half : hurwitzTail2 (1 / 2) = 4 * ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
  unfold hurwitzTail2
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  push_cast
  have : (2 : ℝ) * k + 1 ≠ 0 := by positivity
  have : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
  field_simp
  norm_num

/-- **`F'(0) = 9 L(2, χ₋₃)`**: `ζ(2,1) + 2 ζ(2,1/3) - 3 ζ(2,1/2) = 9 L`. -/
theorem hurwitz_combo :
    hurwitzTail2 1 + 2 * hurwitzTail2 (1 / 3) - 3 * hurwitzTail2 (1 / 2) = 9 * chi3L2 := by
  rw [hurwitz_one, hurwitz_third, hurwitz_half, chi3L2_eq_sub]
  have h3 := split_three
  have h2 := split_two
  linarith

/-- **The P6 constant**: `p6Frame.const = L(2, χ₋₃) / 4`. -/
theorem p6Frame_const : p6Frame.const = chi3L2 / 4 := by
  have e : p6Frame.const = (∑ i : Fin 3, ((![1, 2, -3] i : ℤ) : ℝ) *
      hurwitzTail2 (![1, 1 / 3, 1 / 2] i)) / ((36 : ℚ) : ℝ) := rfl
  rw [e, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  have := hurwitz_combo
  linarith

end CatalanFrames.P6
