module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Harmonic reflection modulo `p` (DQ Lemma 3.1, steps 2-4)

`Gs f n = ∑_{j<n} f(j+1)` in `ZMod p`.  For `f = inv` (harmonic numbers) and `f = inv²`
(`H2`), `∑_{j<p-1} f(j+1) = 0` (power sums over the field) and the reflection
`H_{p-1-n} = H_n`, `H2_{p-1-n} = -H2_n` follows from `f(-x) = ± f(x)`.
These are the two congruences behind the scalar Schur complement `S̄ = s₀ I`.
-/

open Finset

namespace CatalanCore.Arith.Hybrid.LemmaE

variable (p : ℕ) [Fact p.Prime]

/-- `∑_{j<n} f(j+1)` in `ZMod p`. -/
def Gs (f : ZMod p → ZMod p) (n : ℕ) : ZMod p := ∑ j ∈ range n, f ((j + 1 : ℕ) : ZMod p)

lemma sum_range_cast (f : ZMod p → ZMod p) :
    ∑ k ∈ range p, f ((k : ℕ) : ZMod p) = ∑ x : ZMod p, f x := by
  have himg : (range p).image (fun k : ℕ => (k : ZMod p)) = Finset.univ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
    exact ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod p)) (range p : Finset ℕ) := by
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    have := congrArg ZMod.val hab
    simpa [ZMod.val_cast_of_lt ha', ZMod.val_cast_of_lt hb'] using this
  rw [← himg, Finset.sum_image hinj]

lemma sum_range_pow (i : ℕ) (hi : i < p - 1) : ∑ k ∈ range p, ((k : ℕ) : ZMod p) ^ i = 0 := by
  rw [sum_range_cast p (fun x => x ^ i)]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) i (by rwa [ZMod.card])

lemma inv_eq_pow' (x : ZMod p) (hx : x ≠ 0) : x⁻¹ = x ^ (p - 2) := by
  have h1 : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
  have hp2 := (Fact.out : p.Prime).two_le
  have : x * x ^ (p - 2) = 1 := by
    rw [← pow_succ']; rwa [show p - 2 + 1 = p - 1 by omega]
  exact inv_eq_of_mul_eq_one_right this

lemma inv_sq_eq_pow (x : ZMod p) (hx : x ≠ 0) (hp : 3 ≤ p) : (x⁻¹) ^ 2 = x ^ (p - 3) := by
  have h1 : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
  have : x ^ (p - 3) * x ^ 2 = 1 := by
    rw [← pow_add]; rwa [show p - 3 + 2 = p - 1 by omega]
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  rw [inv_pow]
  exact inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact this)

lemma cast_succ_ne_zero {j : ℕ} (hj : j + 1 < p) : (((j + 1 : ℕ)) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd (Nat.succ_pos j) h) (by omega)

lemma sum_shift (g : ℕ → ZMod p) (hg : g 0 = 0) (hp : 1 ≤ p) :
    ∑ k ∈ range p, g k = ∑ j ∈ range (p - 1), g (j + 1) := by
  have hr : range p = range ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp]
  rw [hr, Finset.sum_range_succ', hg, add_zero]

/-- Total harmonic sum: `H_{p-1} = 0`. -/
lemma Gs_inv_top (hp : 3 ≤ p) : Gs p (fun x => x⁻¹) (p - 1) = 0 := by
  have h := sum_range_pow p (p - 2) (by omega)
  rw [sum_shift p (fun k => ((k : ℕ) : ZMod p) ^ (p - 2)) (by simp [show p - 2 ≠ 0 by omega])
    (by omega)] at h
  rw [← h]
  unfold Gs
  refine Finset.sum_congr rfl fun j hj => ?_
  exact inv_eq_pow' p _ (cast_succ_ne_zero p (by have := Finset.mem_range.mp hj; omega))

/-- Total `H2` sum: `H2_{p-1} = 0` for `p ≥ 5`. -/
lemma Gs_inv_sq_top (hp : 5 ≤ p) : Gs p (fun x => (x⁻¹) ^ 2) (p - 1) = 0 := by
  have h := sum_range_pow p (p - 3) (by omega)
  rw [sum_shift p (fun k => ((k : ℕ) : ZMod p) ^ (p - 3)) (by simp [show p - 3 ≠ 0 by omega])
    (by omega)] at h
  rw [← h]
  unfold Gs
  refine Finset.sum_congr rfl fun j hj => ?_
  exact inv_sq_eq_pow p _ (cast_succ_ne_zero p (by have := Finset.mem_range.mp hj; omega))
    (by omega)

/-- **Reflection.**  If `f(-x) = ε f(x)` and the total sum vanishes, then
`G_{p-1-n} = -ε G_n`. -/
lemma Gs_refl (f : ZMod p → ZMod p) (ε : ZMod p) (hf : ∀ x, f (-x) = ε * f x)
    (htop : Gs p f (p - 1) = 0) {n : ℕ} (hn : n ≤ p - 1) :
    Gs p f (p - 1 - n) = -ε * Gs p f n := by
  have hsplit : Gs p f (p - 1) = Gs p f (p - 1 - n) +
      ∑ j ∈ range n, f ((((p - 1 - n) + j + 1 : ℕ)) : ZMod p) := by
    unfold Gs
    have := Finset.sum_range_add (fun x : ℕ => f ((x + 1 : ℕ) : ZMod p)) (p - 1 - n) n
    rw [show p - 1 - n + n = p - 1 by omega] at this
    rw [this]
  have hterm : ∀ j ∈ range n, f ((((p - 1 - n) + j + 1 : ℕ)) : ZMod p) =
      ε * f ((((n - 1 - j) + 1 : ℕ)) : ZMod p) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have h1 : ((((p - 1 - n) + j + 1 : ℕ)) : ZMod p) = -((((n - 1 - j) + 1 : ℕ)) : ZMod p) := by
      apply eq_neg_of_add_eq_zero_left
      have : ((p - 1 - n) + j + 1) + ((n - 1 - j) + 1) = p := by omega
      rw [← Nat.cast_add, this]
      exact ZMod.natCast_self p
    rw [h1, hf]
  have hsum : ∑ j ∈ range n, f ((((p - 1 - n) + j + 1 : ℕ)) : ZMod p) = ε * Gs p f n := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_range_reflect (fun j : ℕ => f ((j + 1 : ℕ) : ZMod p)) n
  rw [hsum, htop] at hsplit
  linear_combination -hsplit

lemma H_refl (hp : 3 ≤ p) {n : ℕ} (hn : n ≤ p - 1) :
    Gs p (fun x => x⁻¹) (p - 1 - n) = Gs p (fun x => x⁻¹) n := by
  have := Gs_refl p (fun x => x⁻¹) (-1) (fun x => by simp [inv_neg]) (Gs_inv_top p hp) hn
  simpa using this

lemma H2_refl (hp : 5 ≤ p) {n : ℕ} (hn : n ≤ p - 1) :
    Gs p (fun x => (x⁻¹) ^ 2) (p - 1 - n) = -Gs p (fun x => (x⁻¹) ^ 2) n := by
  have := Gs_refl p (fun x => (x⁻¹) ^ 2) 1 (fun x => by simp [inv_neg]) (Gs_inv_sq_top p hp) hn
  simpa using this

end CatalanCore.Arith.Hybrid.LemmaE
