module

public import CatalanMeasure.Parametric.MarkedSheetExpansion
public import CatalanMeasure.Parametric.MixedMajorant

/-!
# The original marked amplitudes and their Laurent expansion

The marked entries are the actual polynomial P values used by the coefficient
functional, including on the positive half of the interval.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Set Finset OAI.InternalCatalan
open scoped BigOperators

noncomputable section

def markedAmplitudeMatrix (P : Parameters) (N : ℕ) (x : Fin (P.n N) → ℝ)
    (marked : Fin (P.n N) → Bool) : Matrix (Fin (P.n N)) (Fin (P.n N)) ℝ :=
  Matrix.of fun i r => if marked i then
    (realPoly (rowP P N r.val)).eval (realCoordinateInv (x i))
  else realRowAmplitude P N r.val (realCoordinateInv (x i))

theorem marked_amplitude_entry_factor {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (r : Fin (P.n N)) (marked : Bool)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    (if marked then (realPoly (rowP P N r.val)).eval (realCoordinateInv x)
      else realRowAmplitude P N r.val (realCoordinateInv x)) =
      ((1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1)) *
        (if marked then
          (1 / 2 : ℝ) * x ^ ((P.g N : ℤ) - r) +
            (1 / 2 : ℝ) * x ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r x) := by
  have hoff : -rowOffset P N r = ((P.g N : ℤ) - r) := by
    unfold rowOffset
    omega
  cases marked
  · change realRowAmplitude P N r.val (realCoordinateInv x) =
      ((1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1)) *
        actualLaurentEntry (P.g N) r x
    rw [realRowAmplitude_sheet hP hN r.isLt hx hx0]
    simp only [actualLaurentEntry, hoff, rowOffset, neg_sub]
  · change (realPoly (rowP P N r.val)).eval (realCoordinateInv x) =
      ((1 - realCoordinateInv x) ^ P.h N * realCoordinateInv x ^ (P.C N - 1)) *
        ((1 / 2 : ℝ) * x ^ ((P.g N : ℤ) - r) +
          (1 / 2 : ℝ) * x ^ ((r : ℤ) - P.g N))
    rw [rowP_realCoordinateInv_signed hP hN r.isLt hx0, hoff]
    unfold rowOffset
    ring

theorem marked_amplitude_det_factor {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (x : Fin (P.n N) → ℝ) (marked : Fin (P.n N) → Bool)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    |(markedAmplitudeMatrix P N x marked).det| =
      (∏ i, paramRowNodeWeight P N (x i)) *
        |(Matrix.of fun i r : Fin (P.n N) => if marked i then
          (1 / 2 : ℝ) * x i ^ ((P.g N : ℤ) - r) +
            (1 / 2 : ℝ) * x i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (x i)).det| := by
  let w : Fin (P.n N) → ℝ := fun i =>
    (1 - realCoordinateInv (x i)) ^ P.h N * realCoordinateInv (x i) ^ (P.C N - 1)
  let L : Matrix (Fin (P.n N)) (Fin (P.n N)) ℝ := Matrix.of fun i r =>
    if marked i then
      (1 / 2 : ℝ) * x i ^ ((P.g N : ℤ) - r) +
        (1 / 2 : ℝ) * x i ^ ((r : ℤ) - P.g N)
    else actualLaurentEntry (P.g N) r (x i)
  have hm : markedAmplitudeMatrix P N x marked = Matrix.of (fun i r => w i * L i r) := by
    ext i r
    exact marked_amplitude_entry_factor hP hN r (marked i) (hx i) (hx0 i)
  rw [hm, Matrix.det_mul_column, abs_mul, abs_prod]
  congr 1
  apply prod_congr rfl
  intro i _
  dsimp only [w]
  rw [abs_mul, abs_pow, abs_pow, abs_of_pos (one_sub_realCoordinateInv_pos (hx i))]
  unfold paramRowNodeWeight
  ring

theorem marked_amplitude_det_bound {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (x : Fin (P.n N) → ℝ) (marked : Fin (P.n N) → Bool)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) {M : ℝ} (hM : 0 ≤ M)
    (hV : ∀ t : Fin (P.n N) → Bool,
      |(Matrix.of fun i r : Fin (P.n N) =>
        if t i && marked i && decide (0 ≤ x i) then x i ^ ((r : ℤ) - P.g N)
        else actualLaurentEntry (P.g N) r (x i)).det| ≤ M) :
    |(markedAmplitudeMatrix P N x marked).det| ≤
      (∏ i, paramRowNodeWeight P N (x i)) *
        (M * ∏ i, (if marked i then (5 : ℝ) else 1)) := by
  rw [marked_amplitude_det_factor hP hN x marked hx hx0]
  exact mul_le_mul_of_nonneg_left (marked_laurent_det_bound x marked hM hV)
    (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hx i))

end

end CatalanMeasure.Parametric
