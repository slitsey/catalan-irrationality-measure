module

public import CatalanCore.Star.Leonard.CCExist
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Partial fractions over the border `Y` (package H2)

`N / Q̂ = Σ_{j<m} κ_j / (z + t_j)` for `deg N < m`, `Q̂ = ∏_{j<m}(z + t_j)`, `t_j = S + 2j + 1`.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- Border points `t_j = S + 2j + 1` (as nodes `-t_j`). -/
def vY (S : F) (j : ℕ) : F := -(S + 2 * (j : F) + 1)

lemma Qh_eq_nodal (m : ℕ) (S : F) :
    Qh m S = Lagrange.nodal (Finset.range m) (vY S) := by
  unfold Qh PPf Lagrange.nodal vY
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [lin_one]; congr 2; ring

lemma vY_injOn [CharZero F] (m : ℕ) (S : F) : Set.InjOn (vY S) (Finset.range m : Set ℕ) := by
  intro i _ j _ h
  unfold vY at h
  have : (2 : F) * (i : F) = 2 * (j : F) := by linear_combination -h
  have := mul_left_cancel₀ (two_ne_zero) this
  exact_mod_cast this

theorem partial_frac [CharZero F] (m : ℕ) (S : F) (N : F[X]) (hN : N.natDegree < m) :
    ∃ κ : ℕ → F, ∀ z : F, (Qh m S).eval z ≠ 0 →
      N.eval z / (Qh m S).eval z = ∑ j ∈ Finset.range m, κ j / (z - vY S j) := by
  classical
  have hinj := vY_injOn m S
  have hdeg : N.degree < (Finset.range m).card := by
    rw [Finset.card_range]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast hN)
  have hN' := Lagrange.eq_interpolate hinj hdeg
  refine ⟨fun j => Lagrange.nodalWeight (Finset.range m) (vY S) j * N.eval (vY S j), fun z hz => ?_⟩
  have hx : ∀ i ∈ Finset.range m, z ≠ vY S i := by
    intro i hi h
    apply hz
    rw [Qh_eq_nodal, Lagrange.eval_nodal]
    exact Finset.prod_eq_zero hi (by rw [h]; ring)
  have := Lagrange.eval_interpolate_not_at_node (fun i => N.eval (vY S i)) hx
  rw [← hN'] at this
  rw [Qh_eq_nodal] at hz ⊢
  rw [this, mul_div_cancel_left₀ _ hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [div_eq_mul_inv]; ring

end CatalanCore.Star.Leonard
