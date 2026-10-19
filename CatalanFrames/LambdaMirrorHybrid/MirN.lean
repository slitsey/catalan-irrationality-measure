module

public import CatalanFrames.LambdaMirror.Frame
public import CatalanCore.Arith.Hybrid.LamEntries

@[expose] public section

/-!
# The mirror frame with the λ-like sign (`LamData mirNFrame 3`)

`mirNFrame` has `μ = ![1/4, 1]`, `w = ![-1, 1]`, i.e. `Δ_t = 1/t - 4/(4t-3)`, so it satisfies the generic
`LamData Fr 3` (offset `o = 3`).  The legacy `mirFrame` (`w = ![1, -1]`) has `Mn = - mirNFrame.Mn`
entrywise; all deficit machinery is stated for `mirNFrame` and transferred by `X ↦ -X`.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid

namespace CatalanFrames.LambdaMirrorHybrid

open CatalanFrames.LambdaMirror

/-- The mirror frame, λ-like sign. -/
def mirNFrame : Frame where
  d := 2
  μ := ![1 / 4, 1]
  w := ![-1, 1]
  norm := 16
  xs := 5 / 8
  δ0 := 3 / 8
  n0off := 1
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  hw := by simp [Fin.sum_univ_two]
  hnorm := by norm_num

lemma mirN_Delta (k : ℕ) (hk : 1 ≤ k) :
    mirNFrame.Delta k = 1 / (k : ℚ) - 4 / (4 * (k : ℚ) - (3 : ℕ)) := by
  have h1 : (k : ℚ) ≠ 0 := by positivity
  have h2 : 4 * (k : ℚ) - 3 ≠ 0 := by
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    intro h; linarith
  have h3 : (k : ℚ) - 1 + 1 / 4 ≠ 0 := by
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    intro h; linarith
  have e : mirNFrame.Delta k =
      ∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![1 / 4, 1] i) := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  have e1 : (k : ℚ) - 1 + 1 = k := by ring
  have e2 : (k : ℚ) - 1 + 1 / 4 = (4 * k - 3) / 4 := by ring
  rw [e1, e2]
  field_simp
  ring

lemma mirN_Dsq (k : ℕ) (hk : 1 ≤ k) :
    mirNFrame.Dsq k = 1 / (k : ℚ) ^ 2 - 16 / (4 * (k : ℚ) - (3 : ℕ)) ^ 2 := by
  have h1 : (k : ℚ) ≠ 0 := by positivity
  have h2 : 4 * (k : ℚ) - 3 ≠ 0 := by
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    intro h; linarith
  have e : mirNFrame.Dsq k =
      ∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![1 / 4, 1] i) ^ 2 := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  have e1 : (k : ℚ) - 1 + 1 = k := by ring
  have e2 : (k : ℚ) - 1 + 1 / 4 = (4 * k - 3) / 4 := by ring
  rw [e1, e2]
  field_simp
  ring

/-- **The mirror frame satisfies the generic λ-like data with offset `3`.** -/
theorem mirNData : LamData mirNFrame 3 where
  norm_eq := rfl
  o_pos := by norm_num
  o_le := le_rfl
  delta_eq := mirN_Delta
  dsq_eq := mirN_Dsq

lemma mir_Delta_neg (k : ℕ) : mirFrame.Delta k = -mirNFrame.Delta k := by
  unfold Frame.Delta
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  fin_cases i <;> simp [mirFrame, mirNFrame, neg_div]

lemma mir_Dsq_neg (k : ℕ) : mirFrame.Dsq k = -mirNFrame.Dsq k := by
  unfold Frame.Dsq
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  fin_cases i <;> simp [mirFrame, mirNFrame, neg_div]

/-- `Mn` of the legacy mirror frame is minus `Mn` of `mirNFrame`. -/
theorem mir_Mn_neg (a b : ℕ) : mirFrame.Mn a b = -mirNFrame.Mn a b := by
  unfold Frame.Mn
  have hn : mirFrame.norm = mirNFrame.norm := rfl
  by_cases h : a = b
  · simp only [if_pos h, hn, mir_Dsq_neg, Finset.sum_neg_distrib]
    ring
  · simp only [if_neg h, hn, mir_Delta_neg, Finset.sum_neg_distrib]
    ring

end CatalanFrames.LambdaMirrorHybrid
