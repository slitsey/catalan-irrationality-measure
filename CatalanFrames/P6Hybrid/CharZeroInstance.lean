module

public import CatalanCore.Rect.CharZeroNV.FrameAdapter
public import CatalanFrames.P6.Frame

@[expose] public section

/-! # P6 instance of the generic characteristic-zero frame adapter

Only the increment denominator, isolated pole and cleared value/jet identities
are P6 data. Prefix transport, Loewner identification and common-node selection
come from `FrameAdapter` at arbitrary border ratios and admissibility predicates.
-/

open Polynomial Finset Matrix CatalanCore.Rect CatalanCore.Rect.CharZeroNV
  CatalanFrames.P6

namespace CatalanFrames.P6Hybrid.CharZeroInstance

section Pole
variable {K : Type*} [Field K] [CharZero K]

noncomputable def incrementDen : K[X] :=
  216 * (X + 1) * (X + C (1 / 3)) * (X + C (1 / 2))

theorem isolatedPole : IsolatedIntegerPole (incrementDen : K[X]) (1 - X) where
  pole := by simp [incrementDen]
  residue := by norm_num
  nonneg n := by
    have hn : (n : K) + 1 ≠ 0 := by exact_mod_cast (show (n : ℤ) + 1 ≠ 0 by omega)
    have h3 : (n : K) + 1 / 3 ≠ 0 := by
      intro hz
      have hz' : (3 : K) * n + 1 = 0 := by linear_combination 3 * hz
      have : (3 : ℤ) * n + 1 = 0 := by exact_mod_cast hz'
      omega
    have h2 : (n : K) + 1 / 2 ≠ 0 := by
      intro hz
      have hz' : (2 : K) * n + 1 = 0 := by linear_combination 2 * hz
      have : (2 : ℤ) * n + 1 = 0 := by exact_mod_cast hz'
      omega
    simpa [incrementDen] using mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (216 : K) ≠ 0) hn) h3) h2
  negative n := by
    have hn : -((n : K) + 2) + 1 ≠ 0 := by
      intro hz
      have : (n : K) + 1 = 0 := by linear_combination -hz
      have : (n : ℤ) + 1 = 0 := by exact_mod_cast this
      omega
    have h3 : -((n : K) + 2) + 1 / 3 ≠ 0 := by
      intro hz
      have hz' : (3 : K) * n + 5 = 0 := by linear_combination -3 * hz
      have : (3 : ℤ) * n + 5 = 0 := by exact_mod_cast hz'
      omega
    have h2 : -((n : K) + 2) + 1 / 2 ≠ 0 := by
      intro hz
      have hz' : (2 : K) * n + 3 = 0 := by linear_combination -2 * hz
      have : (2 : ℤ) * n + 3 = 0 := by exact_mod_cast hz'
      omega
    simpa [incrementDen] using mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (216 : K) ≠ 0) hn) h3) h2


end Pole

lemma increment_value (i : ℕ) :
    (incrementDen : ℚ[X]).eval (i : ℚ) * (p6Frame.Delta (i + 1) / 36) = 1 - (i : ℚ) := by
  rw [Delta_eq (i + 1) (by omega)]
  have hi : (0 : ℚ) ≤ i := Nat.cast_nonneg i
  have h1 : (i : ℚ) + 1 ≠ 0 := by linarith
  have h3 : 3 * (i : ℚ) + 1 ≠ 0 := by linarith
  have h2 : 2 * (i : ℚ) + 1 ≠ 0 := by linarith
  simp only [incrementDen, eval_mul, eval_ofNat, eval_add, eval_X, eval_one, eval_C, Nat.cast_succ]
  simp only [show 3 * ((i : ℚ) + 1) - 2 = 3 * (i : ℚ) + 1 by ring,
    show 2 * ((i : ℚ) + 1) - 1 = 2 * (i : ℚ) + 1 by ring]
  field_simp [h1, h2, h3]
  <;> ring

lemma increment_jet (i : ℕ) :
    (incrementDen : ℚ[X]).derivative.eval (i : ℚ) * (p6Frame.Delta (i + 1) / 36) -
      incrementDen.eval (i : ℚ) * (p6Frame.Dsq (i + 1) / 36) = -1 := by
  rw [Delta_eq (i + 1) (by omega), Dsq_eq (i + 1) (by omega)]
  have hi : (0 : ℚ) ≤ i := Nat.cast_nonneg i
  have h1 : (i : ℚ) + 1 ≠ 0 := by linarith
  have h3 : 3 * (i : ℚ) + 1 ≠ 0 := by linarith
  have h2 : 2 * (i : ℚ) + 1 ≠ 0 := by linarith
  simp only [incrementDen, derivative_mul, derivative_add, derivative_X, derivative_one,
    derivative_C, derivative_ofNat, eval_add, eval_mul, eval_ofNat, eval_X, eval_one,
    eval_C, eval_zero, Nat.cast_succ]
  simp only [show 3 * ((i : ℚ) + 1) - 2 = 3 * (i : ℚ) + 1 by ring,
    show 2 * ((i : ℚ) + 1) - 1 = 2 * (i : ℚ) + 1 by ring]
  field_simp [h1, h2, h3]
  <;> ring


/-- The only P6 input to the shared nonvanishing adapter. -/
theorem frameIncrement :
    FrameAdapter.FrameIncrement p6Frame (incrementDen : ℚ[X]) (1 - X) where
  pole := isolatedPole
  deg_D := by unfold incrementDen; compute_degree
  deg_A := by compute_degree
  value i := by simpa [p6Frame] using increment_value i
  jet i := by simpa [p6Frame] using increment_jet i

theorem exists_common_deletion_fullN (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ s : Finset (Fin r), s.card ≤ 1 ∧
      (FullN p6Frame (fun i : {i // i ∉ s} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).det ≠ 0 :=
  FrameAdapter.exists_common_deletion_fullN frameIncrement U r m hr

theorem exists_commonMinor (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ s : Finset (Fin r), r - s.card ≤ 1 ∧
      (commonMinorPoly p6Frame r m s).eval U ≠ 0 :=
  FrameAdapter.exists_commonMinor frameIncrement U r m hr

theorem commonMinor_hasNVPinC (Adm : ℕ → ℕ → Prop)
    (hAdm : ∀ r, 1 ≤ r → ∃ m, Adm r m)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    CatalanCore.HasNVPinC (commonMinorFam p6Frame Adm 1) Cls Bad α β :=
  FrameAdapter.commonMinor_hasNVPinC frameIncrement Adm hAdm Cls Bad α β

#print axioms frameIncrement
#print axioms exists_common_deletion_fullN
#print axioms exists_commonMinor
#print axioms commonMinor_hasNVPinC

end CatalanFrames.P6Hybrid.CharZeroInstance
