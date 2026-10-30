import CatalanFrames.P6.Const
import CatalanCore.Decay.Atoms
import Mathlib.NumberTheory.ZetaValues
set_option Elab.async false

/-! The six seventh frames with the exact contour offsets from the hypotheses receipt. -/

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore

/-- The two-term shift frame `μ = ![s, 1]`, `w = ![-1, 1]`, normalisation `49`. -/
def seventhsFrame (s xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) : Frame where
  d := 2
  μ := ![s, 1]
  w := ![-1, 1]
  norm := 49
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

def seventhNumerator (a : Fin 6) : ℕ := a.val + 1

def seventhsFrameAt (a : Fin 6) : Frame :=
  let s : ℚ := (seventhNumerator a : ℚ) / 7
  let xs : ℚ := if a.val < 3 then (1 + s) / 2 else s / 2
  let δ : ℚ := if a.val < 3 then (1 - s) / 2 else s / 2
  seventhsFrame s xs δ (if a.val < 3 then 1 else 0)
    (by dsimp [s, seventhNumerator]; positivity)
    (by
      have ha : (a.val : ℚ) < 6 := by exact_mod_cast a.isLt
      dsimp [s, seventhNumerator]
      push_cast
      linarith)

/-- The requested target, defined directly by its convergent real series. -/
noncomputable def seventhsTarget (a : ℕ) : ℝ :=
  (∑' n : ℕ, 1 / ((n : ℝ) + (((a : ℚ) / 7 : ℚ) : ℝ)) ^ 2) - Real.pi ^ 2 / 6

theorem seventhsFrame_w_ne (s xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1)
    (i : Fin (seventhsFrame s xs δ0 n0off hs0 hs1).d) :
    (seventhsFrame s xs δ0 n0off hs0 hs1).w i ≠ 0 := by
  rcases i with ⟨k, hk⟩
  have hk2 : k < 2 := hk
  interval_cases k
  · exact (by decide : (-1 : ℤ) ≠ 0)
  · exact (by decide : (1 : ℤ) ≠ 0)

theorem seventhsFrame_const (s xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) :
    (seventhsFrame s xs δ0 n0off hs0 hs1).const =
      ((-1 / 49 : ℚ) : ℝ) * (hurwitzTail2 s - Real.pi ^ 2 / 6) := by
  have he : (seventhsFrame s xs δ0 n0off hs0 hs1).const =
      (∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℝ) * hurwitzTail2 (![s, 1] i)) / ((49 : ℚ) : ℝ) := rfl
  rw [he, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [CatalanFrames.P6.hurwitz_one, hasSum_zeta_two.tsum_eq]
  push_cast
  ring

theorem seventhsFrameAt_const (a : Fin 6) :
    (seventhsFrameAt a).const = ((-1 / 49 : ℚ) : ℝ) * seventhsTarget (seventhNumerator a) := by
  have h0 : (0 : ℚ) < (seventhNumerator a : ℚ) / 7 := by
    dsimp [seventhNumerator]
    positivity
  have h1 : (seventhNumerator a : ℚ) / 7 < 1 := by
    have ha : (a.val : ℚ) < 6 := by exact_mod_cast a.isLt
    dsimp [seventhNumerator]
    push_cast
    linarith
  unfold seventhsFrameAt
  simpa [seventhsTarget, hurwitzTail2] using
    seventhsFrame_const ((seventhNumerator a : ℚ) / 7)
      (if a.val < 3 then (1 + (seventhNumerator a : ℚ) / 7) / 2 else ((seventhNumerator a : ℚ) / 7) / 2)
      (if a.val < 3 then (1 - (seventhNumerator a : ℚ) / 7) / 2 else ((seventhNumerator a : ℚ) / 7) / 2)
      (if a.val < 3 then 1 else 0) h0 h1


theorem sevenths_shift_pos (a : Fin 6) : (0 : ℚ) < (seventhNumerator a : ℚ) / 7 := by
  dsimp [seventhNumerator]
  positivity

theorem sevenths_shift_lt_one (a : Fin 6) : (seventhNumerator a : ℚ) / 7 < 1 := by
  have ha : (a.val : ℚ) < 6 := by exact_mod_cast a.isLt
  dsimp [seventhNumerator]
  push_cast
  linarith

theorem seventhsFrameAt_w_ne (a : Fin 6) (i : Fin (seventhsFrameAt a).d) :
    (seventhsFrameAt a).w i ≠ 0 := by
  rcases i with ⟨k, hk⟩
  have hk2 : k < 2 := hk
  interval_cases k
  · exact (by decide : (-1 : ℤ) ≠ 0)
  · exact (by decide : (1 : ℤ) ≠ 0)

end CatalanCore.Uniform.Bank.Sevenths
