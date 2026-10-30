module

public import CatalanCore.Decay.Contour

@[expose] public section
set_option Elab.async false

/-!
# A Boolean check for contour separation (lane D2)

`Frame.ContourGap` asks `δ0 ≤ |n + μ_i - xs|` for every family `i` and every integer `n`. The
distance from a rational `x` to `ℤ` is `min (fract x) (1 - fract x)`, so the condition is a finite
rational check on the frame's data, closed by `decide`.

* `contourCheck Fr` : the check;
* `contourOK_of_check` : `contourCheck Fr = true → Fr.ContourOK`.
-/

namespace CatalanCore.Frame

/-- `|n + x| ≥ min (fract x) (1 - fract x)` for every integer `n`. -/
theorem le_abs_int_add (x : ℚ) (n : ℤ) : min (Int.fract x) (1 - Int.fract x) ≤ |(n : ℚ) + x| := by
  have hx : x = (⌊x⌋ : ℚ) + Int.fract x := (Int.floor_add_fract x).symm
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  set m : ℤ := n + ⌊x⌋ with hm
  have e : (n : ℚ) + x = (m : ℚ) + Int.fract x := by rw [hm]; push_cast; linarith
  rw [e]
  rcases le_or_gt 0 m with h | h
  · have hm0 : (0 : ℚ) ≤ m := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have hm1 : (m : ℚ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    rw [abs_of_neg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

/-- **The Boolean check.** -/
def contourCheck (Fr : Frame) : Bool :=
  decide (0 < Fr.xs) && decide (0 < Fr.δ0) &&
    (List.finRange Fr.d).all fun i =>
      decide (Fr.δ0 ≤ min (Int.fract (Fr.μ i - Fr.xs)) (1 - Int.fract (Fr.μ i - Fr.xs)))

/-- **Soundness.** -/
theorem contourOK_of_check {Fr : Frame} (h : contourCheck Fr = true) : Fr.ContourOK := by
  simp only [contourCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨hxs, hδ⟩, hall⟩ := h
  refine ⟨hxs, hδ, fun i n => ?_⟩
  have := le_abs_int_add (Fr.μ i - Fr.xs) n
  have e : (n : ℚ) + Fr.μ i - Fr.xs = (n : ℚ) + (Fr.μ i - Fr.xs) := by ring
  rw [e]
  exact (hall i).trans this

end CatalanCore.Frame
