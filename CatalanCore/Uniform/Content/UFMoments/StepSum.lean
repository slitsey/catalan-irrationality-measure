module

public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# UF moments, step (c): the cyclic-step Cauchy sum is the regular prefix

Over `𝔽_p` (`p` odd):

* `sum_inv_univ`, `sum_inv_sub`: `Σ_c (c - z)⁻¹ = 0` (with `0⁻¹ = 0`, so the term `c = z` is
  absent).  Hence constants may be added to Cauchy weights freely (`sum_mul_inv_sub_const`).
* `cauchy_shift`: `H(z+1) - H(z) = Σ_c (w(c+1) - w(c)) (c - z)⁻¹` for `H(z) = Σ_c w(c)(c - z)⁻¹`.
* `step_identity`: if `w` is a cyclic step, `w(z+1) - w(z) = -[z ∈ P] κ(z)`, and `h` has increments
  `h(z+1) - h(z) = Σ_{a ∈ P} κ(a) (z - a)⁻¹`, then `h - H` is constant on `𝔽_p`.

This replaces the polynomial-differentiation proof of (S5) (`h = -w' + const`): the regular part
of the frame prefix has exactly these increments (the pole term is the excluded one).
-/

open Finset

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [hp : Fact p.Prime]

/-- `Σ_{x ∈ 𝔽_p} x⁻¹ = 0` for odd `p`. -/
theorem sum_inv_univ (hp2 : p ≠ 2) : ∑ x : ZMod p, x⁻¹ = 0 := by
  rw [Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun x => x⁻¹) (fun x => x) (fun _ => rfl)]
  have h2 := hp.out.two_le
  have h := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 1
    (by rw [ZMod.card]; omega)
  simpa using h

/-- `Σ_c (c - z)⁻¹ = 0` for odd `p`. -/
theorem sum_inv_sub (hp2 : p ≠ 2) (z : ZMod p) : ∑ c : ZMod p, (c - z)⁻¹ = 0 := by
  rw [Fintype.sum_equiv (Equiv.subRight z) (fun c => (c - z)⁻¹) (fun x => x⁻¹) (fun _ => rfl)]
  exact sum_inv_univ hp2

/-- Constant shifts of Cauchy weights are invisible (any ring receiving `𝔽_p`). -/
theorem sum_mul_inv_sub_const {R : Type*} [CommRing R] (f : ZMod p →+* R) (hp2 : p ≠ 2)
    (w : ZMod p → R) (w0 : R) (z : ZMod p) :
    ∑ c : ZMod p, (w c - w0) * f (c - z)⁻¹ = ∑ c : ZMod p, w c * f (c - z)⁻¹ := by
  have h0 : ∑ c : ZMod p, f (c - z)⁻¹ = 0 := by rw [← map_sum, sum_inv_sub hp2, map_zero]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h0, mul_zero, sub_zero]

/-- The Cauchy sum of a weight function on `𝔽_p`. -/
def cauchyH (w : ZMod p → ZMod p) (z : ZMod p) : ZMod p := ∑ c : ZMod p, w c * (c - z)⁻¹

/-- Shift rule for the Cauchy sum. -/
theorem cauchy_shift (w : ZMod p → ZMod p) (z : ZMod p) :
    cauchyH w (z + 1) - cauchyH w z = ∑ c : ZMod p, (w (c + 1) - w c) * (c - z)⁻¹ := by
  unfold cauchyH
  have e : ∑ c : ZMod p, w c * (c - (z + 1))⁻¹ = ∑ c : ZMod p, w (c + 1) * (c - z)⁻¹ := by
    refine Fintype.sum_equiv (Equiv.subRight 1) _ _ fun c => ?_
    simp only [Equiv.subRight_apply, sub_add_cancel]
    congr 2
    ring
  rw [e, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- A function on `𝔽_p` with zero increments is constant. -/
theorem eq_of_succ {α : Type*} (D : ZMod p → α) (hD : ∀ z, D (z + 1) = D z) (z : ZMod p) :
    D z = D 0 := by
  have hn : ∀ n : ℕ, D (n : ZMod p) = D 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hD, ih]
  have := hn z.val
  rwa [ZMod.natCast_zmod_val] at this

/-- **Step identity.**  A cyclic step `w` with jumps `-κ` on `P` and a function `h` with
increments `Σ_{a ∈ P} κ(a)/(z - a)` differ, after the Cauchy transform of `w`, by a constant. -/
theorem step_identity (w h κ : ZMod p → ZMod p) (P : Finset (ZMod p))
    (hw : ∀ z, w (z + 1) - w z = -(if z ∈ P then κ z else 0))
    (hh : ∀ z, h (z + 1) - h z = ∑ a ∈ P, κ a * (z - a)⁻¹) (z : ZMod p) :
    h z - cauchyH w z = h 0 - cauchyH w 0 := by
  refine eq_of_succ (fun z => h z - cauchyH w z) (fun z => ?_) z
  have h1 := cauchy_shift w z
  have h2 : ∑ c : ZMod p, (w (c + 1) - w c) * (c - z)⁻¹ = ∑ a ∈ P, κ a * (z - a)⁻¹ := by
    simp_rw [hw]
    have e : ∀ c : ZMod p, -(if c ∈ P then κ c else 0) * (c - z)⁻¹ =
        if c ∈ P then κ c * (z - c)⁻¹ else 0 := by
      intro c
      split_ifs
      · rw [← neg_sub z c, inv_neg]; ring
      · simp
    simp_rw [e]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h3 := hh z
  linear_combination h3 - h1 - h2

end CatalanCore.Uniform.Content.UFMoments
