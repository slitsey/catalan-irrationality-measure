module

public import CatalanCore.Star.Leonard.GDelta
public import CatalanCore.Star.Leonard.NumCB

/-!
# `G · Δ` in closed form (package H6)

For the `g = 0` instance `(m + n, m, S)` with `n = S + 1`, `N = S + m = K - 1`, `x₀ = θ - S + 1`:
`G · Δ = V(A) V(B) V_K² ∏_{b<K} 1/(x₀+b)_{2N} · C(2N,N) ((x₀+N)_N)² / N!²`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- the shifts of `A ∪ B` are the `2N` consecutive values `x₀, …, x₀ + 2N - 1` -/
lemma union_prod (t : F) (S m : ℕ) :
    (∏ j ∈ Finset.range S, ((t + ((j : F) + 1)) * (t - (j : F)))) *
        (∏ i ∈ Finset.range m, ((t + ((S : F) + 2 + 2 * (i : F))) * (t + ((S : F) + 1 + 2 * (i : F))))) =
      ∏ i ∈ Finset.range (2 * (S + m)), (t - (S : F) + 1 + (i : F)) := by
  have hA : ∀ S : ℕ, ∏ j ∈ Finset.range S, ((t + ((j : F) + 1)) * (t - (j : F))) =
      ∏ i ∈ Finset.range (2 * S), (t - (S : F) + 1 + (i : F)) := by
    intro S
    induction S with
    | zero => simp
    | succ S ih =>
      rw [Finset.prod_range_succ, ih]
      have hR : ∏ i ∈ Finset.range (2 * (S + 1)), (t - ((S + 1 : ℕ) : F) + 1 + (i : F)) =
          (t - (S : F)) * ((∏ i ∈ Finset.range (2 * S), (t - (S : F) + 1 + (i : F))) *
            (t + (S : F) + 1)) := by
        rw [show 2 * (S + 1) = (2 * S + 1) + 1 by ring, Finset.prod_range_succ',
          Finset.prod_range_succ]
        have hc : ∏ x ∈ Finset.range (2 * S), (t - ((S + 1 : ℕ) : F) + 1 + (((x + 1 : ℕ)) : F)) =
            ∏ i ∈ Finset.range (2 * S), (t - (S : F) + 1 + (i : F)) :=
          Finset.prod_congr rfl fun i _ => by push_cast; ring
        rw [hc]
        push_cast
        ring
      rw [hR]
      ring
  have hB : ∀ m : ℕ, ∏ i ∈ Finset.range m, ((t + ((S : F) + 2 + 2 * (i : F))) * (t + ((S : F) + 1 + 2 * (i : F)))) =
      ∏ i ∈ Finset.range (2 * m), (t + (S : F) + 1 + (i : F)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
        Finset.prod_range_succ, Finset.prod_range_succ]
      push_cast; ring
  rw [hA, hB, show 2 * (S + m) = 2 * S + 2 * m by ring, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast; ring

section Inst

variable [CharZero F] (m S : ℕ) (θ : F)

lemma hrho_inst (b : ℕ) :
    ∏ j : Fin (S + m), (((b : F) + asv m S θ j) * ((b : F) + bsv m S θ j)) =
      ∏ i ∈ Finset.range (2 * (S + m)), ((θ - (S : F) + 1) + (b : F) + (i : F)) := by
  rw [Fin.prod_univ_add]
  simp only [asv, bsv, Fin.addCases_left, Fin.addCases_right]
  have h1 : ∏ j : Fin S, (((b : F) + (θ + ((((j : ℕ) + 1 : ℕ) : ℤ) : F))) *
      ((b : F) + (θ + (((-((j : ℕ) : ℤ)) : ℤ) : F)))) =
      ∏ j ∈ Finset.range S, (((θ + b) + ((j : F) + 1)) * ((θ + b) - (j : F))) := by
    rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => (((b : F) + (θ + (((j + 1 : ℕ) : ℤ) : F))) *
      ((b : F) + (θ + (((-(j : ℤ)) : ℤ) : F))))) S]
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring
  have h2 : ∏ i : Fin m, (((b : F) + (θ + ((bX m (S : ℤ) i : ℤ) : F))) *
      ((b : F) + (θ + ((bY m (S : ℤ) i : ℤ) : F)))) =
      ∏ i ∈ Finset.range m, (((θ + b) + ((S : F) + 2 + 2 * (i : F))) *
        ((θ + b) + ((S : F) + 1 + 2 * (i : F)))) := by
    simp only [bX, bY]
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => (((b : F) + (θ + (((S : ℤ) + 2 + 2 * (i : ℤ) : ℤ) : F))) *
      ((b : F) + (θ + (((S : ℤ) + 1 + 2 * (i : ℤ) : ℤ) : F))))) m]
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast; ring
  rw [h1, h2, union_prod]
  refine Finset.prod_congr rfl fun i _ => by ring


/-- **`G · Δ` in closed form.**  `n = S + 1`, `N = S + m`, `x₀ = θ - S + 1`. -/
theorem G_mul_Delta_closed (hm : 1 ≤ m) (n : ℕ) (hn : n = S + 1) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det) :
    (CatalanCore.colMat fun j => zvec m n S θ j).det *
        ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det =
      Vprod (asv m S θ) * Vprod (bsv m S θ) *
        Vprod (fun i : Fin (m + n) => ((i : ℕ) : F)) ^ 2 *
        (∏ b : Fin (m + n), (∏ i ∈ Finset.range (2 * (S + m)),
          ((θ - (S : F) + 1) + ((b : ℕ) : F) + (i : F)))⁻¹) *
        ((((2 * (S + m)).choose (S + m) : ℕ) : F) *
          (∏ i ∈ Finset.range (S + m), ((θ - (S : F) + 1) + ((S + m : ℕ) : F) + (i : F))) ^ 2 /
          (((S + m).factorial : ℕ) : F) ^ 2) := by
  rw [G_mul_Delta m n S θ hΔ, CA_eq, CB_eq]
  have key : ∀ (a : Fin (m + n)) (z : ℤ), ((a : ℕ) : F) + (θ + (z : F)) ≠ 0 := fun a z h =>
    gen_add hθ a z (by linear_combination h)
  refine Num_closed' (by omega) (by omega) (asv m S θ) (bsv m S θ) (θ - (S : F) + 1) ?_ ?_
    (fun b => hrho_inst m S θ b)
  · intro a j
    induction j using Fin.addCases with
    | left j' => simp only [asv, Fin.addCases_left]; exact key a _
    | right i => simp only [asv, Fin.addCases_right]; exact key a _
  · intro a j
    induction j using Fin.addCases with
    | left j' => simp only [bsv, Fin.addCases_left]; exact key a _
    | right i => simp only [bsv, Fin.addCases_right]; exact key a _

end Inst

end CatalanCore.Star.Leonard
