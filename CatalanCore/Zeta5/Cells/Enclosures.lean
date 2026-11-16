module

public import CatalanCore.Zeta5.Cells.Vfield
public import CatalanMeasure.GenD.Signed.LogEval
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# Z5-CELLS, part 3: enclosures at a cell centre (ZD21)

`V1Q n α y` and `VyQ n α y` are rational enclosures `(v, e)` (`|true - v| ≤ e`) of `V1 α y` and
`Vy α y` at a rational point `y`, built from the certified tools of `LogEval`:
`argQ` (`arctan (y/a) = arg (a + iy)`, octant reduction plus the node table `arctan (j/128)` and a
short series), `logQ` (node table `log (1 + j/256)`) and the Machin value of `π/4`.
The four transcendental values per cell centre of the ledger are `arctan y`, `arctan (y/α)`,
`log (y²+1)`, `log (y²+α²)`; `π` comes once from `PI4`.  `n` is the series length (the
truncation error is below `2·2^-7(2n+1)`); the table error is `2^-127`.
-/

namespace CatalanCore.Zeta5.Cells

open Real CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.Cert (qabs)

noncomputable section

theorem arg_eq_arctan_of_pos {a b : ℝ} (ha : 0 < a) :
    Complex.arg ⟨a, b⟩ = Real.arctan (b / a) := by
  have h1 : Complex.arg ⟨a, b⟩ = Real.arcsin (b / ‖(⟨a, b⟩ : ℂ)‖) := by
    have := Complex.arg_of_re_nonneg (x := ⟨a, b⟩) ha.le
    simpa using this
  rw [h1, Real.arctan_eq_arcsin]
  congr 1
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = √(a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]
    congr 1; ring
  rw [hn]
  have hs : √(1 + (b / a) ^ 2) = √(a ^ 2 + b ^ 2) / a := by
    rw [show 1 + (b / a) ^ 2 = (a ^ 2 + b ^ 2) / a ^ 2 by field_simp, Real.sqrt_div (by positivity),
      Real.sqrt_sq ha.le]
  rw [hs]
  have : 0 < √(a ^ 2 + b ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- `π` as an enclosure. -/
def piEnc : ℚ × ℚ := (4 * PI4, 4 * PI4E)

theorem enc_pi : Enc Real.pi piEnc := by
  have h := pi4_spec
  unfold Enc piEnc
  push_cast
  have : Real.pi - 4 * (PI4 : ℝ) = 4 * (Real.pi / 4 - (PI4 : ℝ)) := by ring
  rw [this, abs_mul]
  have h4 : |(4 : ℝ)| = 4 := abs_of_pos (by norm_num)
  rw [h4]
  linarith

/-- `arctan (y/a)` for rationals `a > 0`. -/
theorem enc_atan {n : ℕ} {a y v e : ℚ} (ha : 0 < a) (h : argQ n a y = some (v, e)) :
    Enc (Real.arctan ((y : ℝ) / (a : ℝ))) (v, e) := by
  have h1 := argQ_spec h
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  rw [arg_eq_arctan_of_pos haR] at h1
  exact h1

/-- an enclosure of `V1 α y = -3π - 2 arctan y + 12 arctan (y/α)` -/
def V1Q (n : ℕ) (α y : ℚ) : Option (ℚ × ℚ) :=
  match argQ n 1 y, argQ n α y with
  | some (a, ea), some (b, eb) =>
      some (-3 * piEnc.1 - 2 * a + 12 * b, 3 * piEnc.2 + 2 * ea + 12 * eb)
  | _, _ => none

theorem V1Q_spec {n : ℕ} {α y : ℚ} {p : ℚ × ℚ} (hα : 0 < α) (h : V1Q n α y = some p) :
    Enc (V1 (α : ℝ) (y : ℝ)) p := by
  unfold V1Q at h
  split at h
  · rename_i a ea b eb h1 h2
    simp only [Option.some.injEq] at h
    subst h
    have e1 := enc_atan (by norm_num : (0 : ℚ) < 1) h1
    have e2 := enc_atan hα h2
    have hp := enc_pi
    unfold Enc at *
    unfold V1
    push_cast at *
    simp only [div_one] at e1
    rw [abs_le] at *
    constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, hp.1, hp.2]
  · simp at h

/-- the enclosure of `Vy α y` from the enclosures `p1` of `V1 α y`, `l1` of `log (y²+1)` and `l2`
of `log (y²+α²)` -/
def VyOf (α y : ℚ) (p1 l1 l2 : ℚ × ℚ) : ℚ × ℚ :=
  (y * p1.1 + l1.1 - 2 - 6 * α * l2.1 + 12 * α, qabs y * p1.2 + l1.2 + qabs (6 * α) * l2.2)

theorem VyOf_spec {α y : ℚ} {p1 l1 l2 : ℚ × ℚ} (h1 : Enc (V1 (α : ℝ) (y : ℝ)) p1)
    (h2 : Enc (Real.log ((y ^ 2 + 1 : ℚ) : ℝ)) l1)
    (h3 : Enc (Real.log ((y ^ 2 + α ^ 2 : ℚ) : ℝ)) l2) :
    Enc (Vy (α : ℝ) (y : ℝ)) (VyOf α y p1 l1 l2) := by
  have a1 := h1.mulQ y
  have a2 := (a1.add h2).sub (Enc.const 2)
  have a3 := a2.sub (h3.mulQ (6 * α))
  have a4 := a3.add (Enc.const (12 * α))
  have e : Vy (α : ℝ) (y : ℝ) = (y : ℝ) * V1 (α : ℝ) (y : ℝ) + Real.log (((y ^ 2 + 1 : ℚ)) : ℝ)
      - ((2 : ℚ) : ℝ) - ((6 * α : ℚ) : ℝ) * Real.log (((y ^ 2 + α ^ 2 : ℚ)) : ℝ)
      + ((12 * α : ℚ) : ℝ) := by
    unfold Vy; push_cast; ring
  rw [e]
  exact Enc.mono a4 (by simp [VyOf])

end

end CatalanCore.Zeta5.Cells
