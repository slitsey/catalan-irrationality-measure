import CatalanFrames.P6.Const
import CatalanCore.Decay.Atoms
import Mathlib.NumberTheory.ZetaValues
set_option Elab.async false

/-! The four fifths frames and their target constants (lane B, B5).

Self-contained copy of the definitions of `CatalanFrames.Fifths` (`fifths1 … fifths4`,
`fifthsTarget`), so that the bank does not import the old route's unbuilt modules.  The frames are
`F(z) = ψ(z+1) - ψ(z+a/5)` with normalisation `25` and the contour data of the old instances. -/

namespace CatalanCore.Uniform.Bank.Fifths
open CatalanCore

/-- The two-term shift frame `μ = ![s, 1]`, `w = ![-1, 1]`, normalisation `25`. -/
def fifthsFrame (s xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) : Frame where
  d := 2
  μ := ![s, 1]
  w := ![-1, 1]
  norm := 25
  xs := xs
  δ0 := δ0
  n0off := n0off
  hμ := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      exact ⟨hs0, hs1.le⟩
    · simp
  hμinj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all <;> intro h' <;> linarith
  hw := by simp [Fin.sum_univ_two]
  hnorm := by norm_num

def fifths1 : Frame := fifthsFrame (1 / 5) (3 / 5) (1 / 4) 1 (by norm_num) (by norm_num)
def fifths2 : Frame := fifthsFrame (2 / 5) (7 / 10) (1 / 4) 1 (by norm_num) (by norm_num)
def fifths3 : Frame := fifthsFrame (3 / 5) (3 / 10) (1 / 4) 0 (by norm_num) (by norm_num)
def fifths4 : Frame := fifthsFrame (4 / 5) (2 / 5) (1 / 4) 0 (by norm_num) (by norm_num)

/-- The requested target, defined directly by its convergent real series. -/
noncomputable def fifthsTarget (a : ℕ) : ℝ :=
  (∑' n : ℕ, 1 / ((n : ℝ) + (((a : ℚ) / 5 : ℚ) : ℝ)) ^ 2) - Real.pi ^ 2 / 6

theorem fifthsFrame_w_ne (s xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1)
    (i : Fin (fifthsFrame s xs δ0 n0off hs0 hs1).d) :
    (fifthsFrame s xs δ0 n0off hs0 hs1).w i ≠ 0 := by
  rcases i with ⟨k, hk⟩
  have hk2 : k < 2 := hk
  interval_cases k
  · exact (by decide : (-1 : ℤ) ≠ 0)
  · exact (by decide : (1 : ℤ) ≠ 0)

theorem fifthsFrame_const (s xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) :
    (fifthsFrame s xs δ0 n0off hs0 hs1).const =
      ((-1 / 25 : ℚ) : ℝ) * (hurwitzTail2 s - Real.pi ^ 2 / 6) := by
  have he : (fifthsFrame s xs δ0 n0off hs0 hs1).const =
      (∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℝ) * hurwitzTail2 (![s, 1] i)) / ((25 : ℚ) : ℝ) := rfl
  rw [he, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [CatalanFrames.P6.hurwitz_one, hasSum_zeta_two.tsum_eq]
  push_cast
  ring

theorem fifths1_const : fifths1.const = ((-1 / 25 : ℚ) : ℝ) * fifthsTarget 1 := by
  simpa [fifths1, fifthsTarget, hurwitzTail2] using
    fifthsFrame_const (1 / 5) (3 / 5) (1 / 4) 1 (by norm_num) (by norm_num)
theorem fifths2_const : fifths2.const = ((-1 / 25 : ℚ) : ℝ) * fifthsTarget 2 := by
  simpa [fifths2, fifthsTarget, hurwitzTail2] using
    fifthsFrame_const (2 / 5) (7 / 10) (1 / 4) 1 (by norm_num) (by norm_num)
theorem fifths3_const : fifths3.const = ((-1 / 25 : ℚ) : ℝ) * fifthsTarget 3 := by
  simpa [fifths3, fifthsTarget, hurwitzTail2] using
    fifthsFrame_const (3 / 5) (3 / 10) (1 / 4) 0 (by norm_num) (by norm_num)
theorem fifths4_const : fifths4.const = ((-1 / 25 : ℚ) : ℝ) * fifthsTarget 4 := by
  simpa [fifths4, fifthsTarget, hurwitzTail2] using
    fifthsFrame_const (4 / 5) (2 / 5) (1 / 4) 0 (by norm_num) (by norm_num)

end CatalanCore.Uniform.Bank.Fifths
