module

public import CatalanFrames.P6.Content
public import CatalanFrames.P6.NV.Final
public import CatalanFrames.P6.Const
public import CatalanCore.Cert.SigmaP6.Glue
public import CatalanCore.NT.Rules
public import CatalanCore.Measure.Statements

/-!
# P6 final instance (WP12): the measure of the P6 frame

Assembles `hasContent` (`Λ = 67/24`), the decay input, `hasNV` (`g₁ = g₂ = 1/2`) and the prime
window of `rule` into `Fam.MeasureLB` at the exact rational exponent `measureExp …`.

**Swapping the decay row.**  The decay input is isolated in the three declarations `decD`, `decC`
and `p6_decay`.  (Row D is now installed; row A was `Sigma300.p6_decay_rowA`, D = 30002/10000, c = 68726/10000.)  Everything
below (`p6_measure`, `p6_measure_exp`, the Final statements) is stated in terms of them.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.P6

/-- decay exponent `D` of the certificate in use (row D: `3.0408`; contour radius `r0 = 1/10`). -/
def decD : ℚ := 30408 / 10000

/-- decay rate `c` of the certificate in use (row D: `6.6510`). -/
def decC : ℚ := 66510 / 10000

/-- THE decay input: row D, P6's own sigma (K = 699, rho = 1/2048, r0 = 1/10, density 3). -/
theorem p6_decay : HasDecay (PolyFamily.ofFrame p6Frame) (decD : ℝ) (decC : ℝ) :=
  CatalanCore.Cert.SigmaP6.p6_decay_rowD

/-- content exponent `Λ`. -/
def contLam : ℚ := 67 / 24

theorem p6_content : HasContent (PolyFamily.ofFrame p6Frame) (contLam : ℝ) := by
  have := hasContent
  simpa [contLam] using this

theorem p6_nv : HasNV (PolyFamily.ofFrame p6Frame) rule (((1 / 2 : ℚ)) : ℝ) (((1 / 2 : ℚ)) : ℝ) := by
  have := hasNV
  simpa using this

theorem rule_s : rule.s = 1 := by
  unfold PrimeRule.s rule
  have : Nat.totient 6 = 2 := by decide
  simp [this]

theorem rule_hasWindow : rule.HasWindow :=
  PrimeRule.ofSqDvd_hasWindow 6 1 isUnit_mod6_one

theorem rule_hbad : ∀ q : ℕ, 0 < q → ∃ N : ℕ, ∀ l : ℕ, N < l → ¬ rule.Bad l q := by
  intro q hq
  refine ⟨q, fun l hl ⟨h2, _⟩ => ?_⟩
  have := Nat.le_of_dvd hq ((dvd_pow_self l two_ne_zero).trans h2)
  omega

/-- the exact exponent from the generic deduction. -/
def p6Exp : ℚ := measureExp decC contLam decD (1 / 2) (1 / 2) rule.s

/-- A rounded rational exponent. -/
theorem p6_measure_le {E : ℚ} (hE : p6Exp ≤ E) : (PolyFamily.ofFrame p6Frame).MeasureLB (E : ℝ) :=
  Measure.measure_of_frame_le p6Frame p6_content p6_decay
    (by norm_num [decD, contLam]) (by norm_num [decC]) rule (by rw [rule_s]; norm_num)
    (by norm_num) p6_nv rule_hasWindow hE

theorem p6_measure : (PolyFamily.ofFrame p6Frame).MeasureLB (p6Exp : ℝ) := p6_measure_le le_rfl

theorem p6_irrational : Irrational p6Frame.const :=
  Measure.irrational_of_frame p6Frame (Λ := (contLam : ℝ)) (D := (decD : ℝ)) (c := (decC : ℝ))
    (g₁ := ((1 / 2 : ℚ) : ℝ)) (g₂ := ((1 / 2 : ℚ) : ℝ))
    p6_content p6_decay (by exact_mod_cast (by norm_num [decD, contLam] : contLam < decD))
    rule (by simp [rule]) (by norm_num) rule_hbad p6_nv

end CatalanFrames.P6
