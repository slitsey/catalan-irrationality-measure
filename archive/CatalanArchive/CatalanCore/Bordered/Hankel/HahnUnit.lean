module

public import CatalanCore.Bordered.Hankel.Hahn
public import CatalanCore.Bordered.Hankel.BinomialUnit

/-!
# `ℓ`-unit property of the Hahn Hankel determinants

For `k ≤ N + 1` and `α + β + N + k < ℓ`, `H_k(W_{α,β,N})` is an `ℓ`-unit: induction on `k`
through `stepH`, all of whose integer factors lie in `[1, α+β+N+k-1]`.
(The strict inequality is needed: for `k = 1`, `C(α+β+N+1, N)` with `α+β+N+1 = ℓ` is divisible
by `ℓ` unless `N = 0`.)  This gives the `ℓ`-unit property of the `H_k(v)` factors of `κ_S`
(`v = (2m+1)! · W_{2m+1,0,N}`).
-/

@[expose] public section

open Finset Matrix CatalanCore.ThmA

namespace CatalanCore.Bordered.Hankel

lemma hkH_one (α β N : ℕ) : hkH α β N 1 = ((α + β + N + 1).choose N : ℚ) := by
  simp [hkH, gramH, Matrix.det_unique, massH]

variable {l : ℕ} [Fact l.Prime]

lemma lamH_cast (α β i : ℕ) :
    lamH α β i = ((i + 1 : ℕ) : ℚ) * ((α + β + i + 2 : ℕ) : ℚ) := by
  unfold lamH; push_cast; ring

theorem LU_hkH (l : ℕ) [Fact l.Prime] :
    ∀ j α β N : ℕ, j ≤ N + 1 → α + β + N + j < l → LU l (hkH α β N j) := by
  intro j
  induction j with
  | zero => intro α β N _ _; rw [hkH_zero]; exact LU.one
  | succ j ih =>
    intro α β N hj hl
    cases N with
    | zero =>
      have : j = 0 := by omega
      subst this
      rw [hkH_one]; simp
      exact LU.one
    | succ n =>
      have hstep := stepH α β n j
      have hprod : LU l (∏ i ∈ range j, lamH α β i) := by
        refine LU.prod _ _ fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        rw [lamH_cast]
        exact LU.mul (LU_natCast_lt (by omega) (by omega)) (LU_natCast_lt (by omega) (by omega))
      have hrhs : LU l (((α + β + (n + 1) + 1).choose (n + 1) : ℚ) * (j.factorial : ℚ) ^ 2 *
          (((α : ℚ) + 1) * ((β : ℚ) + 1)) ^ j * hkH (α + 1) (β + 1) n j) := by
        have hc : LU l (((α + β + (n + 1) + 1).choose (n + 1) : ℚ)) := by
          have := LU_choose (l := l) (N := n + 1) (M := α + β + 1) (by omega)
          rwa [show n + 1 + (α + β + 1) = α + β + (n + 1) + 1 by omega] at this
        have hab : LU l (((α : ℚ) + 1) * ((β : ℚ) + 1)) := by
          have h1 := LU_natCast_lt (l := l) (n := α + 1) (by omega) (by omega)
          have h2 := LU_natCast_lt (l := l) (n := β + 1) (by omega) (by omega)
          push_cast at h1 h2
          exact h1.mul h2
        exact LU.mul (LU.mul (LU.mul hc ((LU_factorial (by omega)).pow 2)) (hab.pow j))
          (ih (α + 1) (β + 1) n (by omega) (by omega))
      rw [eq_div_of_mul_eq hprod.1 hstep]
      exact hrhs.div hprod

end CatalanCore.Bordered.Hankel
