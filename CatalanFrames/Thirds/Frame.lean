module

public import CatalanCore.Frame.Spec

@[expose] public section

/-! # The thirds frames `F(z) = ψ(z+1) - ψ(z+s)`

One parametrised frame for every shift `s ∈ (0,1)` and normalisation `N > 0`.  The
two instances of interest are `s = 1/3` and `s = 2/3` with `N = 9/2`
(`L(2,χ₋₃) ± (2/3) ζ(2)`).  The contour data `xs`, `δ0`, `n0off` are parameters; none of
the algebra below depends on them.
-/

open CatalanCore

namespace CatalanFrames.Thirds

/-- The frame `μ = ![s, 1]`, `w = ![-1, 1]`, normalisation `N`. -/
def thirdsFrame (s N xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) (hN : 0 < N) :
    Frame where
  d := 2
  μ := ![s, 1]
  w := ![-1, 1]
  norm := N
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
  hnorm := hN

variable (s N xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) (hN : 0 < N)

/-- `Delta k = 1/k - 1/(k-1+s)`. -/
theorem Delta_eq (k : ℕ) :
    (thirdsFrame s N xs δ0 n0off hs0 hs1 hN).Delta k =
      1 / (k : ℚ) - 1 / ((k : ℚ) - 1 + s) := by
  have e : (thirdsFrame s N xs δ0 n0off hs0 hs1 hN).Delta k =
      ∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![s, 1] i) := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  push_cast
  have h1 : (k : ℚ) - 1 + 1 = k := by ring
  rw [h1]
  ring

/-- `Dsq k = 1/k^2 - 1/(k-1+s)^2`. -/
theorem Dsq_eq (k : ℕ) :
    (thirdsFrame s N xs δ0 n0off hs0 hs1 hN).Dsq k =
      1 / (k : ℚ) ^ 2 - 1 / ((k : ℚ) - 1 + s) ^ 2 := by
  have e : (thirdsFrame s N xs δ0 n0off hs0 hs1 hN).Dsq k =
      ∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) / ((k : ℚ) - 1 + ![s, 1] i) ^ 2 := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  push_cast
  have h1 : (k : ℚ) - 1 + 1 = k := by ring
  rw [h1]
  ring

end CatalanFrames.Thirds
