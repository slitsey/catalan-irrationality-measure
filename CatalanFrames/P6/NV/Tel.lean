module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import CatalanCore.Basic.ZModGood

/-!
# P6 NV: telescoping potentials (WP11)

For `ℓ = 6t+1` the low block of the P6 Loewner matrix modulo `ℓ` is a two-weight Gram matrix:
weight `+1` on `y ∈ [1, 3t]` and weight `-2` on `y ∈ [3t+1, 4t]`.  `Pot f t n` is the potential
`∑_y w_y f(n+y)`; its `n`-difference telescopes to `f(n+1) - 3 f(n+3t+1) + 2 f(n+4t+1)`.
All statements here are pure algebra in any field.
-/

@[expose] public section

open Finset

namespace CatalanFrames.P6.NV

variable {F : Type*} [CommRing F]

/-- the potential `∑_{j<3t} f(n+1+j) - 2 ∑_{j<t} f(n+3t+1+j)`. -/
def Pot (f : ℕ → F) (t n : ℕ) : F :=
  ∑ j ∈ range (3 * t), f (n + 1 + j) - 2 * ∑ j ∈ range t, f (n + 3 * t + 1 + j)

/-- the three-term difference `f(k) - 3 f(k+3t) + 2 f(k+4t)`. -/
def Tri (f : ℕ → F) (t k : ℕ) : F := f k - 3 * f (k + 3 * t) + 2 * f (k + 4 * t)

lemma Pot_step (f : ℕ → F) (t n : ℕ) : Pot f t n - Pot f t (n + 1) = Tri f t (n + 1) := by
  have h1 := Finset.sum_range_sub' (fun j : ℕ => f (n + 1 + j)) (3 * t)
  have h2 := Finset.sum_range_sub' (fun j : ℕ => f (n + 3 * t + 1 + j)) t
  have hA : ∑ j ∈ range (3 * t), f (n + 1 + 1 + j) = ∑ j ∈ range (3 * t), f (n + 1 + (j + 1)) :=
    Finset.sum_congr rfl fun j _ => by congr 1; omega
  have hB : ∑ j ∈ range t, f (n + 3 * t + 1 + 1 + j) = ∑ j ∈ range t, f (n + 3 * t + 1 + (j + 1)) :=
    Finset.sum_congr rfl fun j _ => by congr 1; omega
  have e1 : n + 1 + 0 = n + 1 := by omega
  have e2 : n + 1 + 3 * t = n + 3 * t + 1 := by omega
  have e3 : n + 3 * t + 1 + 0 = n + 3 * t + 1 := by omega
  have e4 : n + 3 * t + 1 + t = n + 1 + 4 * t := by omega
  rw [Finset.sum_sub_distrib] at h1 h2
  simp only [Pot, Tri, hA, hB, e2]
  simp only [e1, e2, e3, e4] at h1 h2
  linear_combination h1 - 2 * h2

/-- Telescoping over a node interval. -/
lemma sum_Ioc_Tri (f : ℕ → F) (t a b : ℕ) (hab : a ≤ b) :
    ∑ k ∈ Ioc a b, Tri f t k = Pot f t a - Pot f t b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih, ← Pot_step]; ring

end CatalanFrames.P6.NV
