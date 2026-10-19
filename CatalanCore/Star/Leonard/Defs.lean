module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

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


/-! ### Genericity -/

/-- `a` is a generic point: `θ + a + z ≠ 0` for every integer `z`. -/
def GenAt (θ a : F) : Prop := ∀ z : ℤ, θ + a + (z : F) ≠ 0

lemma GenAt.of_gen {θ : F} (h : Gen θ) (i : ℤ) : GenAt θ (i : F) := fun z => by
  have := h (i + z); push_cast at this; rwa [← add_assoc] at this

lemma GenAt.shift {θ a : F} (h : GenAt θ a) (k : ℤ) : GenAt θ (a + k) := fun z => by
  have := h (k + z); push_cast at this
  intro h0; apply this; linear_combination h0

lemma GenAt.ne {θ a : F} (h : GenAt θ a) (z : ℤ) : θ + a + z ≠ 0 := h z

lemma Pe_ne_zero (m S : ℕ) {θ a : F} (h : GenAt θ a) : Pe m S θ a ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  have := h (S + 2 * ((i : ℤ) + 1))
  push_cast at this
  intro h0; apply this; linear_combination h0

lemma Qo_ne_zero (m S : ℕ) {θ a : F} (h : GenAt θ a) : Qo m S θ a ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  have := h (S + 2 * ((i : ℤ) + 1) + 1)
  push_cast at this
  intro h0; apply this; linear_combination h0


/-! ### The quartic diagonal -/

lemma sigma_tau_div_mu (K m S : ℕ) (θ a : F) (hm : 1 ≤ m) (h : GenAt θ a)
    (hK : (K : F) - 1 - a ≠ 0) :
    sigma K m S θ a * tau K m S θ a / mu K m S θ a = -(((a + 1) * (a + 1 + θ)) ^ 2) := by
  have h1 : θ + S + 1 + a ≠ 0 := by
    have := h (S + 1); push_cast at this; intro h0; apply this; linear_combination h0
  have h2 : θ + S + 2 * m + 1 + a ≠ 0 := by
    have := h (S + 2 * m + 1); push_cast at this; intro h0; apply this; linear_combination h0
  rw [sigma_mul_tau K m S θ a hm (Pe_ne_zero m S h) (Qo_ne_zero m S h)]
  unfold mu pp
  field_simp

/-- The diagonal is a quartic polynomial. -/
lemma Dd_eq (K m S : ℕ) (θ a : F) (hm : 1 ≤ m) (h : GenAt θ (a - 1)) (hK : (K : F) - a ≠ 0) :
    Dd K m S θ a = mu K m S θ a - (a * (a + θ)) ^ 2 + gg K m S * (gg K m S + 1) * a ^ 2
      + gg K m S * cc0 K m θ (gg K m S) * a := by
  unfold Dd
  rw [sigma_tau_div_mu K m S θ (a - 1) hm h (by intro h0; apply hK; linear_combination h0)]
  ring

/-! ### Shift `S → S + 1` -/

lemma Pe_shift (m S : ℕ) (θ a : F) : Pe m (S + 1) θ a = Pe m S θ (a + 1) := by
  unfold Pe; push_cast
  exact Finset.prod_congr rfl fun i _ => by ring

lemma Qo_shift (m S : ℕ) (θ a : F) : Qo m (S + 1) θ a = Qo m S θ (a + 1) := by
  unfold Qo; push_cast
  exact Finset.prod_congr rfl fun i _ => by ring

/-! ### Darboux scalars (K-step, `K = K' + 1`) -/

/-- `D_i = (K-1)/(K-1-i) · ∏(θ+S+2i')/(θ+S+2i'+i) · ∏(θ+S+2i'+1+i)/(θ+S+2i'+1)`. -/
def Dfac (K m S : ℕ) (θ : F) (i : F) : F :=
  ((K : F) - 1) / ((K : F) - 1 - i) * (Pe m S θ 0 / Pe m S θ i) * (Qo m S θ i / Qo m S θ 0)

lemma genAt_nat {θ : F} (h : Gen θ) (i : ℕ) : GenAt θ (i : F) := by
  simpa using GenAt.of_gen h (i : ℤ)

lemma genAt_nat_succ {θ : F} (h : Gen θ) (i : ℕ) : GenAt θ ((i : F) + 1) := by
  simpa using genAt_nat h (i + 1)

lemma natsub_ne {F : Type*} [Field F] [CharZero F] {a b : ℕ} (h : a ≠ b) :
    (a : F) - (b : F) ≠ 0 := fun h0 => h (by exact_mod_cast sub_eq_zero.1 h0)

/-- (K2a): `σ'(i) D_{i+1}/D_i = σ(i)`, with the primed instance `(K', m, S+1)`. -/
lemma sigma_darboux [CharZero F] (K' m S : ℕ) (θ : F) (hθ : Gen θ) (i : ℕ) (hi : i + 2 ≤ K') :
    sigma K' m (S + 1) θ i * (Dfac (K' + 1) m S θ ((i : F) + 1) / Dfac (K' + 1) m S θ i) =
      sigma (K' + 1) m S θ i := by
  have hA : (K' : F) - i ≠ 0 := natsub_ne (by omega)
  have hB : (K' : F) - i - 1 ≠ 0 := by
    have := natsub_ne (F := F) (a := K') (b := i + 1) (by omega)
    push_cast at this; intro h0; apply this; linear_combination h0
  have hK : (K' : F) ≠ 0 := by
    have := natsub_ne (F := F) (a := K') (b := 0) (by omega); simpa using this
  have hA2 : (K' : F) + 1 - 1 - i ≠ 0 := by intro h0; apply hA; linear_combination h0
  have hB2 : (K' : F) + 1 - 1 - (i + 1) ≠ 0 := by intro h0; apply hB; linear_combination h0
  have h0 : Pe m S θ 0 ≠ 0 := by simpa using Pe_ne_zero m S (genAt_nat hθ 0)
  have q0 : Qo m S θ 0 ≠ 0 := by simpa using Qo_ne_zero m S (genAt_nat hθ 0)
  have hP := Pe_ne_zero m S (genAt_nat hθ i)
  have hQ := Qo_ne_zero m S (genAt_nat hθ i)
  have hP1 := Pe_ne_zero m S (genAt_nat_succ hθ i)
  have hQ1 := Qo_ne_zero m S (genAt_nat_succ hθ i)
  unfold sigma Dfac pp
  rw [Pe_shift, Qo_shift]
  push_cast
  field_simp
  ring_nf
  field_simp
  ring


lemma genAt_nat_sub_one {θ : F} (h : Gen θ) (i : ℕ) : GenAt θ ((i : F) - 1) := by
  simpa using GenAt.of_gen h ((i : ℤ) - 1)

/-- (K2b): `σ'(i) τ'(i) = μ(i+1) τ(i) σ(i) / μ(i)`. -/
lemma sigma_tau_darboux [CharZero F] (K' m S : ℕ) (θ : F) (hθ : Gen θ) (hm : 1 ≤ m) (i : ℕ)
    (hi : i + 2 ≤ K') :
    sigma K' m (S + 1) θ i * tau K' m (S + 1) θ i =
      mu (K' + 1) m S θ ((i : F) + 1) * (sigma (K' + 1) m S θ i * tau (K' + 1) m S θ i) /
        mu (K' + 1) m S θ i := by
  have hA : (K' : F) - i ≠ 0 := natsub_ne (by omega)
  have hB : (K' : F) - i - 1 ≠ 0 := by
    have := natsub_ne (F := F) (a := K') (b := i + 1) (by omega)
    push_cast at this; intro h0; apply this; linear_combination h0
  have h1 : θ + S + 1 + i ≠ 0 := by
    have := genAt_nat hθ i (S + 1); push_cast at this; intro h0; apply this; linear_combination h0
  have h2 : θ + S + 2 * m + 1 + i ≠ 0 := by
    have := genAt_nat hθ i (S + 2 * m + 1); push_cast at this; intro h0; apply this
    linear_combination h0
  have hP := Pe_ne_zero m (S + 1) (genAt_nat hθ i)
  have hQ := Qo_ne_zero m (S + 1) (genAt_nat hθ i)
  have hP' := Pe_ne_zero m S (genAt_nat hθ i)
  have hQ' := Qo_ne_zero m S (genAt_nat hθ i)
  rw [sigma_mul_tau K' m (S + 1) θ i hm hP hQ, sigma_mul_tau (K' + 1) m S θ i hm hP' hQ']
  unfold mu pp
  push_cast
  have h3 : (K' : F) + 1 - 1 - i ≠ 0 := by intro h0; apply hA; linear_combination h0
  field_simp
  ring

/-- the `i`-independent shift `β` of (K2c) is the value at `i = 0`. -/
lemma darboux_diag_poly (K' m S : ℕ) (θ : F) (hS : S + m = K') (i : F) :
    (mu (K' + 1) m S θ i - ((i + 1) * (i + 1 + θ)) ^ 2) -
      (mu K' m (S + 1) θ i - (i * (i + θ)) ^ 2 + gg K' m (S + 1) * (gg K' m (S + 1) + 1) * i ^ 2
        + gg K' m (S + 1) * cc0 K' m θ (gg K' m (S + 1)) * i) =
    (mu (K' + 1) m S θ 0 - ((0 + 1) * (0 + 1 + θ)) ^ 2) -
      (mu K' m (S + 1) θ 0 - (0 * (0 + θ)) ^ 2 + gg K' m (S + 1) * (gg K' m (S + 1) + 1) * 0 ^ 2
        + gg K' m (S + 1) * cc0 K' m θ (gg K' m (S + 1)) * 0) := by
  have h : (S : F) = K' - m := by
    have : ((S + m : ℕ) : F) = K' := congrArg (Nat.cast : ℕ → F) hS
    push_cast at this
    linear_combination this
  unfold mu gg cc0
  push_cast
  rw [h]
  ring


/-! ### (Z) border zeros -/

/-- `l(t) = -τ(-θ-t) = 0` for the border points `t = S + 2j + 1 ∈ Y`. -/
lemma tau_border (K m S : ℕ) (θ : F) (j : ℕ) (hj : j < m) :
    tau K m S θ (-θ - ((S : F) + 2 * j + 1)) = 0 := by
  have : Qf m S θ (-θ - ((S : F) + 2 * j + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := j) (by simp; omega) (by ring)
  simp [tau, this]

/-- `r(t) = -σ(-θ-t-1) = 0` for `t ∈ Y`. -/
lemma sigma_border (K m S : ℕ) (θ : F) (j : ℕ) (hj : j < m) :
    sigma K m S θ (-θ - ((S : F) + 2 * j + 1) - 1) = 0 := by
  have : Pe m S θ (-θ - ((S : F) + 2 * j + 1) - 1) = 0 := by
    refine Finset.prod_eq_zero (i := j) (by simp; omega) (by ring)
  simp [sigma, this]

end CatalanCore.Star.Leonard
