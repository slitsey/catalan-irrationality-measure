module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Leonard-type tridiagonal `T~` for the hybrid `k^gen` (package H1)

Definitions of the off-diagonals `σ, τ`, the pivots `μ`, the diagonal `D` of the node-basis
tridiagonal `T~` (spec `HC-caps-algebraic/lean-spec.md` §1) and the product-simplification lemmas
that every later package uses:

* `sigma_mul_tau`: `σ(a) τ(a) = p(a)² A₁(a) A_{2m+1}(a)` (the symbolic-`m` products telescope),
* `sigma_tau_div_mu`: `σ(a) τ(a) / μ(a) = -((a+1)(a+1+θ))²`, so the diagonal `D` is a quartic.

The pattern for products over symbolic `m`: write each product as `∏ i ∈ range m, B (f i)`, split
with `Finset.prod_range_succ` / `prod_range_succ'` and cancel equal blocks (`prod_div_distrib`).
-/

@[expose] public section

open Finset

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- `θ` is generic: no `θ + z`, `z ∈ ℤ`, vanishes. -/
def Gen (θ : F) : Prop := ∀ z : ℤ, θ + (z : F) ≠ 0

/-- `p(a) = (a+1)(a+1+θ)(K-1-a)`. -/
def pp (K : ℕ) (θ a : F) : F := (a + 1) * (a + 1 + θ) * ((K : F) - 1 - a)

/-- Numerator product of `σ`: `∏_{i=1}^m (θ+S+2i+a)`. -/
def Pe (m S : ℕ) (θ a : F) : F := ∏ i ∈ range m, (θ + S + 2 * ((i : F) + 1) + a)

/-- Odd product `∏_{i=1}^{m-1} (θ+S+2i+1+a)`. -/
def Qo (m S : ℕ) (θ a : F) : F := ∏ i ∈ range (m - 1), (θ + S + 2 * ((i : F) + 1) + 1 + a)

/-- Full odd product `∏_{i=0}^{m} (θ+S+2i+1+a)`. -/
def Qf (m S : ℕ) (θ a : F) : F := ∏ i ∈ range (m + 1), (θ + S + 2 * (i : F) + 1 + a)

/-- `σ(a)`. -/
def sigma (K m S : ℕ) (θ a : F) : F := pp K θ a * Pe m S θ a / Qo m S θ a

/-- `τ(a)`. -/
def tau (K m S : ℕ) (θ a : F) : F := pp K θ a * Qf m S θ a / Pe m S θ a

/-- `μ(a)`. -/
def mu (K m S : ℕ) (θ a : F) : F :=
  -(((K : F) - 1 - a) ^ 2 * (θ + S + 1 + a) * (θ + S + 2 * m + 1 + a))

/-- `g = S - n + 1` with `n = K - m`. -/
def gg (K m S : ℕ) : F := (S : F) - K + m + 1

/-- `c₀`. -/
def cc0 (K m : ℕ) (θ g : F) : F := -2 * ((K : F) - 1) * (θ + g) - 2 * K ^ 2 + 2 * K - m ^ 2

/-- Diagonal `D(a) = μ(a) + σ(a-1)τ(a-1)/μ(a-1) + g(g+1)a² + g c₀ a`. -/
def Dd (K m S : ℕ) (θ a : F) : F :=
  mu K m S θ a + sigma K m S θ (a - 1) * tau K m S θ (a - 1) / mu K m S θ (a - 1)
    + gg K m S * (gg K m S + 1) * a ^ 2 + gg K m S * cc0 K m θ (gg K m S) * a

/-! ### Product simplification -/

lemma Qf_eq (m S : ℕ) (θ a : F) (hm : 1 ≤ m) :
    Qf m S θ a = (θ + S + 1 + a) * (θ + S + 2 * m + 1 + a) * Qo m S θ a := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Qf, Qo, Nat.add_sub_cancel]
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  push_cast
  ring

lemma sigma_mul_tau (K m S : ℕ) (θ a : F) (hm : 1 ≤ m)
    (hP : Pe m S θ a ≠ 0) (hQ : Qo m S θ a ≠ 0) :
    sigma K m S θ a * tau K m S θ a =
      pp K θ a ^ 2 * ((θ + S + 1 + a) * (θ + S + 2 * m + 1 + a)) := by
  unfold sigma tau
  rw [Qf_eq m S θ a hm]
  field_simp

end CatalanCore.Star.Leonard
