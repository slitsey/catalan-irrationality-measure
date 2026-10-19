module

public import CatalanCore.Bordered.Hankel.Binomial
public import CatalanCore.ThmA.UnitLU
public import Mathlib.Data.Nat.Prime.Factorial

/-!
# `ℓ`-unit property of the binomial Hankel determinants (GD, κ is an `ℓ`-unit)

For `N ≤ M`, `N + M < ℓ` and `k ≤ N + 1`, `H_k(W_{N,M})` is an `ℓ`-unit: induction on `k` through
the step identity `CatalanCore.Bordered.Hankel.step`, all of whose integer factors are in
`[1, N+M]`.
-/

@[expose] public section

open Finset Matrix CatalanCore.ThmA

namespace CatalanCore.Bordered.Hankel

lemma hk_one (N M : ℕ) : hk N M 1 = ((N + M).choose N : ℚ) := by
  simp [hk, gram, Matrix.det_unique, mass]

variable {l : ℕ} [Fact l.Prime]

lemma LU_choose {N M : ℕ} (h : N + M < l) : LU l (((N + M).choose N : ℕ) : ℚ) := by
  refine LU_natCast (Nat.choose_pos (by omega)) fun hd => ?_
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right N M)
  rw [Nat.add_sub_cancel_left] at h1
  have h2 : l ∣ (N + M).factorial := by
    rw [← h1]; exact (hd.mul_right _).mul_right _
  have := (Nat.Prime.dvd_factorial (Fact.out : l.Prime)).1 h2
  omega

lemma LU_factorial {j : ℕ} (h : j < l) : LU l (j.factorial : ℚ) := by
  refine LU_natCast (Nat.factorial_pos j) fun hd => ?_
  have := (Nat.Prime.dvd_factorial (Fact.out : l.Prime)).1 hd
  omega

lemma lam_cast (n m i : ℕ) (hi : i ≤ n + m + 2) :
    lam (((n + 1 : ℕ) : ℚ) + ((m + 1 : ℕ) : ℚ) + 1) i =
      ((i + 1 : ℕ) : ℚ) * ((n + m + 2 - i : ℕ) : ℚ) := by
  unfold lam
  push_cast [Nat.cast_sub hi]
  ring

theorem LU_hk (l : ℕ) [Fact l.Prime] :
    ∀ j N M : ℕ, N ≤ M → j ≤ N + 1 → N + M < l → LU l (hk N M j) := by
  intro j
  induction j with
  | zero => intro N M _ _ _; rw [hk_zero]; exact LU.one
  | succ j ih =>
    intro N M hNM hj hl
    cases N with
    | zero =>
      have : j = 0 := by omega
      subst this
      rw [hk_one]; simpa using LU_choose (l := l) (N := 0) (M := M) hl
    | succ n =>
      obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
      have hstep := step n m j (by omega)
      have hprod : LU l (∏ i ∈ range j, lam (((n + 1 : ℕ) : ℚ) + ((m + 1 : ℕ) : ℚ) + 1) i) := by
        refine LU.prod _ _ fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        rw [lam_cast n m i (by omega)]
        refine LU.mul (LU_natCast_lt (by omega) (by omega)) (LU_natCast_lt (by omega) (by omega))
      have hrhs : LU l ((((n + 1) + (m + 1)).choose (n + 1) : ℚ) * (j.factorial : ℚ) ^ 2 *
          (((n + 1 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ)) ^ j * hk n m j) := by
        refine LU.mul (LU.mul (LU.mul ?_ ((LU_factorial (by omega)).pow 2)) ?_) (ih n m (by omega) (by omega) (by omega))
        · exact_mod_cast LU_choose (l := l) (N := n + 1) (M := m + 1) hl
        · exact ((LU_natCast_lt (by omega) (by omega)).mul (LU_natCast_lt (by omega) (by omega))).pow j
      rw [eq_div_of_mul_eq hprod.1 hstep]
      exact hrhs.div hprod
end CatalanCore.Bordered.Hankel
