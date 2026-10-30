module

public import CatalanFrames.P6Hybrid.CharZeroAntidifference
public import CatalanFrames.P6.Frame
public import CatalanCore.Rect.CharZeroNV.After
public import CatalanCore.Rect.Full
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! # The characteristic-zero interpolation data of the frozen P6 frame

This adapter uses the original rational prefixes and sign convention. It does
not change `Frame`, `Mn`, or any historical interface.
-/

open Polynomial Finset CatalanCore.Rect.CharZeroNV CatalanFrames.P6

namespace CatalanFrames.P6Hybrid.CharZeroNV

lemma increment_value (i : ℕ) :
    (incrementDen : ℚ[X]).eval (i : ℚ) * (p6Frame.Delta (i + 1) / 36) = 1 - (i : ℚ) :=
  CharZeroInstance.increment_value i

lemma increment_jet (i : ℕ) :
    (incrementDen : ℚ[X]).derivative.eval (i : ℚ) * (p6Frame.Delta (i + 1) / 36) -
      incrementDen.eval (i : ℚ) * (p6Frame.Dsq (i + 1) / 36) = -1 :=
  CharZeroInstance.increment_jet i

noncomputable abbrev frameData (U : ℚ) :=
  FrameAdapter.frameData CharZeroInstance.frameIncrement U

lemma prefix_sub (g : ℕ → ℚ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Icc 1 b, g k) - (∑ k ∈ Icc 1 a, g k) = ∑ k ∈ Ioc a b, g k :=
  FrameAdapter.prefix_sub g hab

/-- Extend a natural-node datum to the ambient field; only its natural-node
values enter any of the interpolation and matrix statements. -/
noncomputable def onNaturals (g : ℕ → ℚ) : ℚ → ℚ :=
  Function.extend (Nat.cast : ℕ → ℚ) g (fun _ => 0)

@[simp] lemma onNaturals_nat (g : ℕ → ℚ) (i : ℕ) : onNaturals g (i : ℚ) = g i :=
  Nat.cast_injective.extend_apply g _ i

lemma mn_offdiag (U : ℚ) (a b : ℕ) (hab : a ≠ b) :
    p6Frame.Mn a b = ((frameData U).f a - (frameData U).f b) / ((a : ℚ) - b) :=
  FrameAdapter.mn_offdiag CharZeroInstance.frameIncrement U a b hab

lemma loewnerEntry_nat (U : ℚ) (a b : ℕ) :
    loewnerEntry (onNaturals (frameData U).f) (onNaturals (frameData U).tau)
      (a : ℚ) (b : ℚ) = (if a = b then U else 0) + p6Frame.Mn a b :=
  FrameAdapter.loewnerEntry_nat CharZeroInstance.frameIncrement U a b

/-- The abstract matrix is precisely the frozen hybrid matrix after reindexing. -/
theorem fullN_eq_loewner (U : ℚ) (r m : ℕ) :
    CatalanCore.Rect.FullN p6Frame (fun i : Fin r => i.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U =
      (loewnerMatrix (after r m) (onNaturals (frameData U).f)
        (onNaturals (frameData U).tau)).submatrix (afterRowEquiv r m) (afterRowEquiv r m) :=
  FrameAdapter.fullN_eq_loewner CharZeroInstance.frameIncrement U r m

end CatalanFrames.P6Hybrid.CharZeroNV
