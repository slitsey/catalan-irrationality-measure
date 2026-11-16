module

public import CatalanCore.Zeta5.Local.SmallPrimeF

@[expose] public section

/-!
# Row ZC07 (first half): the difference bound (I6)

An integer-valued polynomial `A` of degree `≤ d` satisfies, for integers `x, y`,

`v_p(A(x) - A(y)) ≥ v_p(x - y) - ⌊log_p max(1, d)⌋`     (`VG_poly_diff`).

Proof: Newton expansion of `A(y + z)` in the binomial basis in `z`, and
`bin_k(z) = (z/k) bin_{k-1}(z - 1)` with `bin_{k-1}(z-1)` integral.
-/

open Finset Polynomial

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

lemma bin_eval_succ (k : ℕ) (y : ℚ) :
    (bin (k + 1)).eval y = y / ((k : ℚ) + 1) * (bin k).eval (y - 1) := by
  rw [bin_eval_eq, bin_eval_eq, Finset.prod_range_succ' (fun i : ℕ => y - (i : ℚ)),
    Nat.factorial_succ]
  have : ∏ i ∈ range k, (y - ((i + 1 : ℕ) : ℚ)) = ∏ i ∈ range k, ((y - 1) - (i : ℚ)) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  rw [this]
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hf : (k.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma VG_bin_eval_val {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (z : ℤ) :
    VG p ((bin k).eval (z : ℚ)) ((padicValRat p (z : ℚ) : ℚ) - Nat.log p n) := by
  by_cases hz : z = 0
  · subst hz
    left
    simpa using bin_eval_zero hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [bin_eval_succ, div_eq_mul_inv]
  have h1 : VG p (z : ℚ) (padicValRat p (z : ℚ)) := VG.of_eq _ (fun _ => le_rfl)
  have h2 : VG p (((j : ℚ) + 1)⁻¹) (-(Nat.log p n : ℚ)) := by
    have := VG.inv_nat (p := p) (j := j + 1) (n := n) (by omega) hkn
    push_cast at this
    exact this
  have h3 : VG p ((bin j).eval ((z : ℚ) - 1)) 0 := by
    have := VG_bin_eval_int (p := p) j (z - 1)
    push_cast at this
    exact this
  have := (h1.mul h2).mul h3
  refine this.mono ?_
  linarith

/-- **ZC07, (I6)**: for integer-valued `A` of degree `≤ d`,
`v_p(A(x) - A(y)) ≥ v_p(x - y) - ⌊log_p max(1, d)⌋`. -/
theorem VG_poly_diff {A : ℚ[X]} {d : ℕ} (hd : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0) (x y : ℤ) :
    VG p (A.eval (x : ℚ) - A.eval (y : ℚ))
      ((padicValRat p ((x - y : ℤ) : ℚ) : ℚ) - Nat.log p (max 1 d)) := by
  by_cases hxy : x = y
  · subst hxy
    left
    simp
  set Q := A.comp (X + C (y : ℚ)) with hQ
  have hQd : Q.natDegree ≤ d := by
    rw [hQ]
    refine (natDegree_comp_le).trans ?_
    have : (X + C (y : ℚ)).natDegree ≤ 1 := by rw [natDegree_X_add_C]
    calc A.natDegree * (X + C (y : ℚ)).natDegree ≤ d * 1 := Nat.mul_le_mul hd this
      _ = d := mul_one d
  have hQv : ∀ m ≤ d, VG p (Q.eval (m : ℚ)) 0 := by
    intro m _
    have := hint ((m : ℤ) + y)
    rw [hQ, eval_comp]
    simp only [eval_add, eval_X, eval_C]
    push_cast at this ⊢
    simpa [add_comm] using this
  obtain ⟨e, he, hev⟩ := binRep_of_values hQd hQv
  have hx : A.eval (x : ℚ) = Q.eval ((x - y : ℤ) : ℚ) := by
    rw [hQ, eval_comp]; simp
  have hy : A.eval (y : ℚ) = Q.eval 0 := by
    rw [hQ, eval_comp]; simp
  rw [hx, hy, he]
  simp only [eval_finsetSum, eval_mul, eval_C]
  rw [← Finset.sum_sub_distrib]
  refine VG.sum _ fun m hm => ?_
  have hmd : m ≤ d := by have := Finset.mem_range.mp hm; omega
  rcases m with _ | m
  · left; simp [bin_zero]
  · rw [bin_eval_zero (by omega), ← mul_sub, sub_zero]
    have := (hev (m + 1) hmd).mul
      (VG_bin_eval_val (p := p) (k := m + 1) (n := max 1 d) (by omega) (by omega) (x - y))
    simpa using this

end Apery
