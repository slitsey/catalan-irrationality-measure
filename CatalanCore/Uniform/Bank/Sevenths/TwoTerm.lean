module

public import CatalanCore.Uniform.Bank.Sevenths.Frame
public import CatalanFrames.Thirds.Frame
public import CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform.Content.Smith

/-- Exact rational increment data for each of the six norm-49 frames. -/
theorem sevenths_twoTerm (a : Fin 6) :
    TwoTermData (seventhsFrameAt a) 7 (7 - seventhNumerator a) := by
  have ha : seventhNumerator a ≤ 6 := by dsimp [seventhNumerator]; omega
  have ha0 : 1 ≤ seventhNumerator a := by dsimp [seventhNumerator]; omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro t ht
    have he : (t : ℚ) - 1 + (seventhNumerator a : ℚ) / 7 =
        (7 * (t : ℚ) - ((7 - seventhNumerator a : ℕ) : ℚ)) / 7 := by
      rw [Nat.cast_sub (by omega : seventhNumerator a ≤ 7)]
      push_cast
      ring
    change (CatalanFrames.Thirds.thirdsFrame ((seventhNumerator a : ℚ) / 7) 49 0 1 0
      (sevenths_shift_pos a) (sevenths_shift_lt_one a) (by norm_num)).Delta t = _
    rw [CatalanFrames.Thirds.Delta_eq, he, one_div_div]
    norm_num only [Nat.cast_ofNat]
  · intro t ht
    have he : (t : ℚ) - 1 + (seventhNumerator a : ℚ) / 7 =
        (7 * (t : ℚ) - ((7 - seventhNumerator a : ℕ) : ℚ)) / 7 := by
      rw [Nat.cast_sub (by omega : seventhNumerator a ≤ 7)]
      push_cast
      ring
    change (CatalanFrames.Thirds.thirdsFrame ((seventhNumerator a : ℚ) / 7) 49 0 1 0
      (sevenths_shift_pos a) (sevenths_shift_lt_one a) (by norm_num)).Dsq t = _
    rw [CatalanFrames.Thirds.Dsq_eq, he, div_pow, one_div_div]
    norm_num only [Nat.cast_ofNat]

#print axioms sevenths_twoTerm
end CatalanCore.Uniform.Bank.Sevenths
