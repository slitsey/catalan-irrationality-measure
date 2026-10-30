module

public import CatalanCore.Uniform.Decay.NearCells.Model
public import CatalanCore.Uniform.Decay.Tools.EvalSound

@[expose] public section
set_option Elab.async false

/-!
# Log and argument enclosures of Gaussian rationals (lane D, package D6b)

`logHalf w = some (ℓ̃, ε)` gives `|ℓ̃ - log ‖w‖| ≤ ε`; `argEnc w = some (ã, ε)` gives
`|ã - arg w| ≤ ε` (for `Im w ≠ 0`), both from the accepted evaluator `SignedPilot.evalInput`
(64-term series, scale `10^36 + 39`, checked binary exponents `m`).
-/

namespace CatalanCore.Uniform.Decay.NearCells

open CatalanCore.Uniform.Decay.SignedPilot CatalanCore.Uniform.Decay.Tools

def scQ : ℚ := (scale : ℚ)

def evalLogAux (n : ℤ) (d : ℕ) (m0 : ℤ) : Option (Int × Nat) :=
  match evalInput (1, n, d, m0) with
  | some r => some r
  | none =>
    match evalInput (1, n, d, m0 + 1) with
    | some r => some r
    | none => evalInput (1, n, d, m0 - 1)

/-- First success of `evalInput` for the log of `n/d` among three binary exponents. -/
def evalLogAny (n : ℤ) (d : ℕ) : Option (Int × Nat) :=
  evalLogAux n d ((Nat.log2 n.natAbs : ℤ) - (Nat.log2 d : ℤ))

theorem evalLogAny_sound {n : ℤ} {d : ℕ} {v : Int} {e : Nat} (h : evalLogAny n d = some (v, e)) :
    |(v : ℝ) - (scale : ℝ) * Real.log ((n : ℝ) / d)| ≤ e := by
  unfold evalLogAny evalLogAux at h
  split at h
  · rename_i r hr; cases h; exact evalInput_log hr
  · split at h
    · rename_i r hr; cases h; exact evalInput_log hr
    · exact evalInput_log h

/-- Enclosure of `log ‖w‖ = (1/2) log (nsq w)`. -/
def logHalf (w : CQ) : Option (ℚ × ℚ) :=
  match evalLogAny w.nsq.num w.nsq.den with
  | some (v, e) => some ((v : ℚ) / (2 * scQ), (e : ℚ) / (2 * scQ))
  | none => none

theorem scale_pos : (0 : ℝ) < (scale : ℝ) := by unfold scale; norm_num

theorem logHalf_sound {w : CQ} (hw : w.nsq ≠ 0) {l ε : ℚ} (h : logHalf w = some (l, ε)) :
    |(l : ℝ) - Real.log ‖w.toC‖| ≤ ε := by
  unfold logHalf at h
  split at h
  · rename_i v e hve
    cases h
    have h1 := evalLogAny_sound hve
    have hq : (w.nsq : ℝ) = (w.nsq.num : ℝ) / (w.nsq.den : ℝ) := by
      rw [Rat.cast_def]
    have hpos : 0 < w.nsq := by
      have : 0 ≤ w.nsq := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
      exact lt_of_le_of_ne this (Ne.symm hw)
    have hposR : (0 : ℝ) < (w.nsq : ℝ) := by exact_mod_cast hpos
    have hnorm : Real.log ‖w.toC‖ = Real.log (w.nsq : ℝ) / 2 := by
      have hn : ‖w.toC‖ ^ 2 = (w.nsq : ℝ) := by rw [Complex.sq_norm, ← CQ.nsq_cast]
      have hnp : 0 < ‖w.toC‖ := by
        rcases (norm_nonneg w.toC).lt_or_eq with h | h
        · exact h
        · exfalso; rw [← h] at hn; simp at hn; linarith
      rw [← hn, Real.log_pow]; push_cast; ring
    have hlg : Real.log ((w.nsq.num : ℝ) / (w.nsq.den : ℝ)) = Real.log (w.nsq : ℝ) := by rw [← hq]
    rw [hlg] at h1
    rw [hnorm]
    have hs := scale_pos
    have hsc : (scQ : ℝ) = (scale : ℝ) := by unfold scQ; push_cast; rfl
    push_cast
    rw [hsc]
    have e1 : (v : ℝ) / (2 * (scale : ℝ)) - Real.log (w.nsq : ℝ) / 2
        = ((v : ℝ) - (scale : ℝ) * Real.log (w.nsq : ℝ)) / (2 * (scale : ℝ)) := by
      field_simp
    have h2s : (0 : ℝ) < 2 * (scale : ℝ) := by linarith
    rw [e1, abs_div, abs_of_pos h2s]
    exact div_le_div_of_nonneg_right h1 h2s.le
  · cases h

/-- `arg w = ± π/2 - arctan (Re w / Im w)`. -/
theorem arg_eq_of_im_pos {w : ℂ} (h : 0 < w.im) :
    Complex.arg w = Real.pi / 2 - Real.arctan (w.re / w.im) := by
  have hw : w ≠ 0 := fun h0 => by simp [h0] at h
  have hpi := Real.pi_pos
  have h0 : 0 < Complex.arg w := by
    rcases (Complex.arg_nonneg_iff.2 h.le).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have := Complex.arg_eq_zero_iff.1 h1.symm
      linarith [this.2]
  have h1 : Complex.arg w < Real.pi := by
    rcases (Complex.arg_le_pi w).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have := (Complex.arg_eq_pi_iff.1 h1).2
      linarith
  have ht : Real.tan (Real.pi / 2 - Complex.arg w) = w.re / w.im := by
    rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, Complex.sin_arg, Complex.cos_arg hw,
      inv_div]
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    field_simp
  have := Real.arctan_tan (x := Real.pi / 2 - Complex.arg w) (by linarith) (by linarith)
  rw [ht] at this
  linarith

theorem arg_eq_of_im_neg {w : ℂ} (h : w.im < 0) :
    Complex.arg w = -(Real.pi / 2) - Real.arctan (w.re / w.im) := by
  have h1 := arg_eq_of_im_pos (w := (starRingEnd ℂ) w) (by simpa using h)
  have hne : Complex.arg w ≠ Real.pi := by
    intro h2; have := (Complex.arg_eq_pi_iff.1 h2).2; linarith
  have h2 := Complex.arg_conj w
  rw [if_neg hne] at h2
  simp only [Complex.conj_re, Complex.conj_im] at h1
  have : w.re / -w.im = -(w.re / w.im) := by rw [div_neg]
  rw [this, Real.arctan_neg] at h1
  linarith

/-- Enclosure of `arg w` for `Im w ≠ 0`. -/
def argEnc (w : CQ) : Option (ℚ × ℚ) :=
  if w.im = 0 then
    (if 0 < w.re then some (0, 0)
     else if w.re < 0 then some ((piLiteral : ℚ) / scQ, (1300 : ℚ) / scQ) else none)
  else
  let sg : ℤ := if 0 < w.im then 1 else -1
  let yn : ℤ := w.im.num
  let n : ℤ := w.re.num * (w.im.den : ℤ) * (if 0 < yn then 1 else -1)
  let d : ℕ := w.re.den * yn.natAbs
  match evalInput (2, n, d, 0) with
  | some (v, e) => some (((sg : ℚ) * (piLiteral : ℚ) / 2 - (v : ℚ)) / scQ,
      ((1000 : ℚ) + (e : ℚ)) / scQ)
  | none => none

theorem argEnc_sound_im {w : CQ} {a ε : ℚ} (h : argEnc w = some (a, ε)) (hpi : w.im ≠ 0) :
    |(a : ℝ) - Complex.arg w.toC| ≤ ε := by
  unfold argEnc at h
  rw [if_neg hpi] at h
  simp only at h
  split at h
  · rename_i v e hve
    cases h
    have hd : (w.re.den * (w.im.num).natAbs : ℕ) ≠ 0 := by
      have := w.re.den_nz
      have h2 : (w.im.num).natAbs ≠ 0 := by
        have := Rat.num_ne_zero.2 hpi; omega
      positivity
    have h1 := evalInput_atan hve
    have hq : ((w.re.num * (w.im.den : ℤ) * (if 0 < w.im.num then 1 else -1) : ℤ) : ℝ) /
        ((w.re.den * (w.im.num).natAbs : ℕ) : ℝ) = (w.re : ℝ) / (w.im : ℝ) := by
      have hre : (w.re : ℝ) = (w.re.num : ℝ) / (w.re.den : ℝ) := Rat.cast_def _
      have him : (w.im : ℝ) = (w.im.num : ℝ) / (w.im.den : ℝ) := Rat.cast_def _
      have hden : (w.re.den : ℝ) ≠ 0 := by exact_mod_cast w.re.den_nz
      have hden2 : (w.im.den : ℝ) ≠ 0 := by exact_mod_cast w.im.den_nz
      have hnum : (w.im.num : ℝ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.2 hpi
      rw [hre, him]
      by_cases hp : 0 < w.im.num
      · have : ((w.im.num).natAbs : ℝ) = (w.im.num : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hp)]
        simp only [hp, if_true]; push_cast; rw [this]; field_simp
      · have hn : w.im.num < 0 := lt_of_le_of_ne (not_lt.1 hp) (Rat.num_ne_zero.2 hpi)
        have : ((w.im.num).natAbs : ℝ) = -(w.im.num : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hn)]
        simp only [hp, if_false]; push_cast; rw [this]; field_simp
    rw [hq] at h1
    have hpl := piLiteral_enclosure
    have hs := scale_pos
    have hsc : (scQ : ℝ) = (scale : ℝ) := by unfold scQ; push_cast; rfl
    have hre : w.toC.re = (w.re : ℝ) := rfl
    have him : w.toC.im = (w.im : ℝ) := rfl
    rw [abs_le] at h1 hpl
    by_cases hp : 0 < w.im
    · have hpos : 0 < w.toC.im := by rw [him]; exact_mod_cast hp
      have ha := arg_eq_of_im_pos hpos
      rw [hre, him] at ha
      rw [ha]
      simp only [hp, if_true]
      push_cast
      rw [hsc]
      have hX : |(1 * (piLiteral : ℝ) / 2 - v) - (scale : ℝ) * (Real.pi / 2 - Real.arctan ((w.re : ℝ) / (w.im : ℝ)))| ≤ 1000 + e := by
        rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, hpl.1, hpl.2]
      have e1 : (1 * (piLiteral : ℝ) / 2 - v) / (scale : ℝ) - (Real.pi / 2 - Real.arctan ((w.re : ℝ) / (w.im : ℝ)))
          = ((1 * (piLiteral : ℝ) / 2 - v) - (scale : ℝ) * (Real.pi / 2 - Real.arctan ((w.re : ℝ) / (w.im : ℝ)))) / (scale : ℝ) := by
        field_simp
      rw [e1, abs_div, abs_of_pos hs]
      exact div_le_div_of_nonneg_right hX hs.le
    · have hneg : w.im < 0 := lt_of_le_of_ne (not_lt.1 hp) hpi
      have hn : w.toC.im < 0 := by rw [him]; exact_mod_cast hneg
      have ha := arg_eq_of_im_neg hn
      rw [hre, him] at ha
      rw [ha]
      simp only [hp, if_false]
      push_cast
      rw [hsc]
      have hX : |(-1 * (piLiteral : ℝ) / 2 - v) - (scale : ℝ) * (-(Real.pi / 2) - Real.arctan ((w.re : ℝ) / (w.im : ℝ)))| ≤ 1000 + e := by
        rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, hpl.1, hpl.2]
      have e1 : (-1 * (piLiteral : ℝ) / 2 - v) / (scale : ℝ) - (-(Real.pi / 2) - Real.arctan ((w.re : ℝ) / (w.im : ℝ)))
          = ((-1 * (piLiteral : ℝ) / 2 - v) - (scale : ℝ) * (-(Real.pi / 2) - Real.arctan ((w.re : ℝ) / (w.im : ℝ)))) / (scale : ℝ) := by
        field_simp
      rw [e1, abs_div, abs_of_pos hs]
      exact div_le_div_of_nonneg_right hX hs.le
  · cases h

theorem argEnc_sound {w : CQ} {a ε : ℚ} (h : argEnc w = some (a, ε)) :
    |(a : ℝ) - Complex.arg w.toC| ≤ ε := by
  by_cases hpi : w.im = 0
  · have hw : w.toC = ((w.re : ℝ) : ℂ) := Complex.ext (by simp [CQ.toC]) (by simp [CQ.toC, hpi])
    unfold argEnc at h
    rw [if_pos hpi] at h
    by_cases hp : 0 < w.re
    · rw [if_pos hp] at h
      cases h
      rw [hw, Complex.arg_ofReal_of_nonneg (by exact_mod_cast hp.le)]
      simp
    · rw [if_neg hp] at h
      by_cases hn : w.re < 0
      · rw [if_pos hn] at h
        cases h
        have hn' : (w.re : ℝ) < 0 := by exact_mod_cast hn
        rw [hw, Complex.arg_ofReal_of_neg hn']
        have hpl := piLiteral_enclosure
        have hs := scale_pos
        have hsc : (scQ : ℝ) = (scale : ℝ) := by unfold scQ; push_cast; rfl
        push_cast
        rw [hsc]
        have e1 : (piLiteral : ℝ) / (scale : ℝ) - Real.pi = ((piLiteral : ℝ) - (scale : ℝ) * Real.pi) / (scale : ℝ) := by
          field_simp
        rw [e1, abs_div, abs_of_pos hs]
        exact div_le_div_of_nonneg_right hpl hs.le
      · rw [if_neg hn] at h; cases h
  · exact argEnc_sound_im h hpi

end CatalanCore.Uniform.Decay.NearCells
