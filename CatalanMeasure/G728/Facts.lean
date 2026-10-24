module

public import CatalanMeasure.G728.FieldsS
public import CatalanMeasure.G728.Data

@[expose] public section

/-!
# Side facts of the 728 witness (split from `Glue`)

`first_lower` (`p_1 ≥ 9/50`) and the nonvanishing of the tail nodes, i.e. exactly what the three
covers `XCover`, `YCover`, `RCover` and the near-field cap use.  `Glue` itself (the old
`SecondTrialBoundsOn` glue) is deleted with the P20-specific analytic stack.
-/

open OAI.InternalCatalan Set Filter
open scoped Topology

namespace CatalanMeasure.G728
open CatalanMeasure.Cert
set_option maxRecDepth 100000
noncomputable section

/-! ### the first coefficient -/

/-- exact rational value of the first coefficient `trialSeqS cs tail 1` -/
def firstQ (cs : List ℤ) (tail : List TailQ) : ℚ :=
  (cs.getD 0 0 : ℚ) / 1099511627776 + (tail.map (fun t => t.rr * t.zr - t.ri * t.zi)).sum

theorem tailSum_one (tail : List TailQ) :
    (((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ 1)).sum).re =
      (((tail.map (fun t => t.rr * t.zr - t.ri * t.zi)).sum : ℚ) : ℝ) := by
  induction tail with
  | nil => simp
  | cons t tail ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re] at ih ⊢
    rw [ih]
    simp [TailQ.toC, barrierComplex, Complex.mul_re]

theorem trialSeqS_one (cs : List ℤ) (tail : List TailQ) :
    trialSeqS cs tail 1 = ((firstQ cs tail : ℚ) : ℝ) := by
  have h := trialSeqS_succ cs tail 0
  rw [zero_add] at h
  rw [h, tailSum_one]
  unfold firstQ
  push_cast
  rfl

theorem firstQ_data : (9 / 50 : ℚ) ≤ firstQ Pc P := by
  unfold firstQ; decide +kernel

/-- `p_1 ≥ 9/50` for the 728 witness -/
theorem first_lower : (9 / 50 : ℝ) ≤ trialSeqS Pc P 1 := by
  rw [trialSeqS_one]
  have h : (((9 / 50 : ℚ)) : ℝ) ≤ ((firstQ Pc P : ℚ) : ℝ) := Rat.cast_le.mpr firstQ_data
  push_cast at h
  exact h

/-! ### side conditions of the witness -/

theorem P_nonzero : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0 := by decide +kernel
theorem V_nonzero : ∀ t ∈ V, t.zr ≠ 0 ∨ t.zi ≠ 0 := by decide +kernel

end
end CatalanMeasure.G728
