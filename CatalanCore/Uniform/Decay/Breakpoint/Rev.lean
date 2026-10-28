import CatalanCore.Uniform.Decay.NearCells.Agg
import CatalanCore.Uniform.Decay.Spline.PolyDensity
set_option Elab.async false

/-!
# Reversing a weighted segment (lane D, package D14)

`revWP P` is the same weighted segment traversed from `B` to `A`: endpoints swapped, density
`a(1 - t)`.  `PhiW_revWP : PhiW (revWP P) z = PhiW P z`.  It lets the breakpoint rule treat a piece
that *ends* at the breakpoint as one that starts there.
-/

namespace CatalanCore.Uniform.Decay.Breakpoint

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.NearCells

/-- Coefficients of `t ↦ a(1 - t)` (same length). -/
def revCoefs (l : List ℚ) : List ℚ :=
  (List.range l.length).map fun j =>
    (-1 : ℚ) ^ j * lsum (fun i => ((chooseFast (j + i) j : ℕ) : ℚ) * coeffs l (j + i)) (l.length - j)

/-- The same segment traversed backwards. -/
def revWP (P : WP) : WP := { P with a := revCoefs P.a, A := P.B, B := P.A }

theorem length_revCoefs (l : List ℚ) : (revCoefs l).length = l.length := by
  simp [revCoefs]

theorem coeffs_revCoefs (l : List ℚ) {j : ℕ} (hj : j < l.length) :
    coeffs (revCoefs l) j =
      (-1 : ℚ) ^ j * lsum (fun i => ((chooseFast (j + i) j : ℕ) : ℚ) * coeffs l (j + i)) (l.length - j) := by
  simp [coeffs, revCoefs, List.getD_eq_getElem?_getD, hj]

theorem ratPoly_rev (l : List ℚ) (t : ℝ) : ratPoly (revCoefs l) t = ratPoly l (1 - t) := by
  unfold ratPoly
  rw [length_revCoefs]
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · have : l = [] := List.length_eq_zero_iff.1 h0
    subst this
    simp [coeffs, revCoefs]
  · obtain ⟨d, hd⟩ : ∃ d, l.length = d + 1 := ⟨l.length - 1, by omega⟩
    have hd' : l.length - 1 + 1 = d + 1 := by omega
    rw [hd']
    have h1 : ∀ j ∈ range (d + 1), ((coeffs (revCoefs l) j : ℚ) : ℝ) * t ^ j
        = ∑ i ∈ range (d + 1 - j), (-1 : ℝ) ^ j * (((j + i).choose j : ℕ) : ℝ) *
            ((coeffs l (j + i) : ℚ) : ℝ) * t ^ j := by
      intro j hj
      have hjl : j < l.length := by have := Finset.mem_range.1 hj; omega
      rw [coeffs_revCoefs l hjl, hd, lsum_eq]
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [chooseFast_eq]
      ring
    rw [Finset.sum_congr rfl h1]
    rw [← Finset.sum_range_diag_flip (d + 1)
      (fun j i => (-1 : ℝ) ^ j * (((j + i).choose j : ℕ) : ℝ) * ((coeffs l (j + i) : ℚ) : ℝ) * t ^ j)]
    refine Finset.sum_congr rfl fun m hm => ?_
    have h2 : ∀ j ∈ range (m + 1), (-1 : ℝ) ^ j * (((j + (m - j)).choose j : ℕ) : ℝ) *
          ((coeffs l (j + (m - j)) : ℚ) : ℝ) * t ^ j
        = ((coeffs l m : ℚ) : ℝ) * ((-t) ^ j * (m.choose j : ℝ)) := by
      intro j hj
      have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
      rw [Nat.add_sub_cancel' hjm, neg_pow]
      ring
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
    congr 1
    have := add_pow (-t) (1 : ℝ) m
    simp only [one_pow, mul_one] at this
    rw [show 1 - t = -t + 1 by ring, this]

theorem PhiW_revWP (P : WP) (z : ℂ) : PhiW (revWP P) z = PhiW P z := by
  unfold PhiW revWP
  simp only []
  rw [length_revCoefs]
  have hp : ∀ t : ℝ, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs (revCoefs P.a) k : ℚ) : ℝ) * t ^ k)
      = ∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * (1 - t) ^ k := by
    intro t
    have := ratPoly_rev P.a t
    unfold ratPoly at this
    rw [length_revCoefs] at this
    exact this
  simp_rw [hp]
  let F : ℝ → ℝ := fun u =>
    (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * u ^ k) *
      Real.log ‖z - (P.A.toC + (u : ℂ) * (P.B.toC - P.A.toC))‖
  have hF : ∀ t : ℝ, (∑ k ∈ range (P.a.length - 1 + 1), ((coeffs P.a k : ℚ) : ℝ) * (1 - t) ^ k) *
      Real.log ‖z - (P.B.toC + (t : ℂ) * (P.A.toC - P.B.toC))‖ = F (1 - t) := by
    intro t
    simp only [F]
    congr 3
    push_cast
    ring
  simp_rw [hF]
  rw [intervalIntegral.integral_comp_sub_left F 1]
  simp only [sub_self, sub_zero]
  rfl
