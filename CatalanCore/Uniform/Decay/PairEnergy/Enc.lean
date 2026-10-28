import CatalanCore.Uniform.Decay.PairEnergy.PairSound
import CatalanCore.Uniform.Decay.NearCells.Eval
set_option Elab.async false

/-!
# Directed rational bounds of the pair linear form (lane D, package D6c)

`encAtom` encloses an atom by the D6b evaluators `logHalf`/`argEnc` (accepted integer series,
scale `10^36 + 39`); `pairUb P` is the resulting rational upper bound of `P.pairLF.val`.
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open CatalanCore.Uniform.Decay.NearCells

def QC.toCQ (w : QC) : CQ := ⟨w.re, w.im⟩

theorem toCQ_toC (w : QC) : w.toCQ.toC = w.toC := rfl

/-- Centre and radius of an atom enclosure. -/
def encAtom : Atom → Option (ℚ × ℚ)
  | .logC w => if w.nsq = 0 then some (0, 0) else logHalf w.toCQ
  | .argC w => argEnc w.toCQ

theorem encAtom_sound {a : Atom} {c ε : ℚ} (h : encAtom a = some (c, ε)) :
    |(c : ℝ) - a.val| ≤ ε := by
  cases a with
  | logC w =>
    simp only [encAtom] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hre : w.re = 0 ∧ w.im = 0 := by
        unfold QC.nsq at hw
        constructor <;> nlinarith [mul_self_nonneg w.re, mul_self_nonneg w.im]
      have : w.toC = 0 := by apply Complex.ext <;> simp [QC.toC, hre.1, hre.2]
      simp [Atom.val, this]
    · have := logHalf_sound (w := w.toCQ) (by simpa [QC.toCQ, CQ.nsq, QC.nsq] using hw) h
      simpa [Atom.val, toCQ_toC] using this
  | argC w =>
    simp only [encAtom] at h
    have := argEnc_sound (w := w.toCQ) h
    simpa [Atom.val, toCQ_toC] using this

/-- Upper bound of a term list. -/
def termsUb : List (ℚ × Atom) → Option ℚ
  | [] => some 0
  | (q, a) :: l =>
    match encAtom a, termsUb l with
    | some (c, ε), some r => some (q * c + |q| * ε + r)
    | _, _ => none

theorem termsUb_sound {l : List (ℚ × Atom)} {u : ℚ} (h : termsUb l = some u) :
    termsVal l ≤ (u : ℝ) := by
  induction l generalizing u with
  | nil => simp [termsUb] at h; subst h; simp [termsVal]
  | cons p l ih =>
    obtain ⟨q, a⟩ := p
    simp only [termsUb] at h
    split at h
    · rename_i c ε r hce hr
      simp only [Option.some.injEq] at h; subst h
      have h1 := encAtom_sound hce
      have h2 := ih hr
      rw [abs_le] at h1
      simp only [termsVal]
      push_cast
      have hq : (q : ℝ) * a.val ≤ q * c + |(q : ℝ)| * ε := by
        rcases le_total 0 (q : ℝ) with h0 | h0
        · rw [abs_of_nonneg h0]; nlinarith [h1.1, h1.2]
        · rw [abs_of_nonpos h0]; nlinarith [h1.1, h1.2]
      linarith
    · simp at h

def LF.ub (f : LF) : Option ℚ :=
  match termsUb f.terms with
  | some r => some (f.c + r)
  | none => none

theorem LF.ub_sound {f : LF} {u : ℚ} (h : f.ub = some u) : f.val ≤ (u : ℝ) := by
  unfold LF.ub at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h; subst h
    unfold LF.val; push_cast
    linarith [termsUb_sound hr]
  · simp at h

end CatalanCore.Uniform.Decay.PairEnergy
