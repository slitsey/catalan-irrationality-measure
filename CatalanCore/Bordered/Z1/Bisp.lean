module

public import CatalanCore.Bordered.Z1.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination

/-!
# Z1.2 (part 1): the bispectral identity and the intertwining `Lag · X = L̃ · Lag`

Everything is over `ℚ` at a rational `θ > 0` (so that no Cauchy pole is met).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

/-- **The bispectral identity** (FT §1), `K = s + m`, `z = x + y`. -/
theorem bispectral {F : Type*} [Field F] (s m : ℕ) (θ x y : F) (h0 : x + y ≠ 0) (h1 : x + y + 1 ≠ 0) (h2 : x + y - 1 ≠ 0) :
    Fq s m θ x / (x + y + 1) + Dq s m θ x / (x + y) + Gq θ x / (x + y - 1) =
      rq s m θ y / (x + y + 1) + Dq s m θ (-y) / (x + y) + lq θ y / (x + y - 1) := by
  simp only [Fq, Gq, rq, lq, Dq, Nat.cast_add]
  field_simp
  ring

/-- `∏_{i<s} (x + i + 1)`. -/
def Pn (s : ℕ) (x : ℚ) : ℚ := ∏ i ∈ range s, (x + ((i + 1 : ℕ) : ℚ))

lemma lag_mul (s : ℕ) (x : ℚ) {j : ℕ} (hj : j < s) :
    lag s x j * (x + ((j + 1 : ℕ) : ℚ)) = Pn s x := by
  rw [mul_comm]
  exact Finset.mul_prod_erase (range s) (fun i => x + ((i + 1 : ℕ) : ℚ)) (mem_range.2 hj)

lemma lag_eq (s : ℕ) (x : ℚ) {j : ℕ} (hj : j < s) (h : x + ((j + 1 : ℕ) : ℚ) ≠ 0) :
    lag s x j = Pn s x / (x + ((j + 1 : ℕ) : ℚ)) := by
  rw [eq_div_iff h]; exact lag_mul s x hj

lemma Pn_succ (s : ℕ) (x : ℚ) : Pn (s + 1) x = Pn s x * (x + s + 1) := by
  unfold Pn; rw [prod_range_succ]; push_cast; ring

lemma Pn_shift (s : ℕ) (x : ℚ) : Pn s (x + 1) * (x + 1) = Pn s x * (x + s + 1) := by
  induction s with
  | zero => simp [Pn]
  | succ s ih =>
    rw [Pn_succ, Pn_succ]
    push_cast
    linear_combination (x + s + 2) * ih

lemma lag_eq' (s : ℕ) (y : ℚ) {j : ℕ} (hj : j < s) (d : ℚ) (hd : d = y + ((j + 1 : ℕ) : ℚ))
    (h : d ≠ 0) : lag s y j = Pn s y / d := by
  subst hd; exact lag_eq s y hj h

/-- Pointwise form of `Lag X = L̃ Lag`, after substituting `lag = P/(x+j+1)`, `x = θ + a`. -/
lemma pointwise (s m : ℕ) (θ a jj P : ℚ) (hx : 0 < θ + a) (hj : 0 ≤ jj) :
    Dq s m θ (-(jj + 1)) * (P / (θ + a + jj + 1)) + rq s m θ (jj + 1) * (P / (θ + a + (jj + 1) + 1))
      + lq θ (jj + 1) * (P / (θ + a + (jj - 1) + 1)) =
    Dq s m θ (θ + a) * (P / (θ + a + jj + 1))
      + ((θ + a + 1) * (θ + a + 1 + s + 2 * m) * (((s + m : ℕ) : ℚ) - 1 - a) ^ 2)
          * (P * (θ + a + s + 1) / (θ + a + 1) / (θ + a + 1 + jj + 1))
      + (((θ + a) * a ^ 2 * (θ + a + s)) * (P * (θ + a) / (θ + a + s) / (θ + a - 1 + jj + 1))) := by
  have hs : (0 : ℚ) ≤ s := Nat.cast_nonneg s
  have e1 : θ + a + jj + 1 ≠ 0 := by linarith
  have e2 : θ + a + (jj + 1) + 1 ≠ 0 := by linarith
  have e3 : θ + a + (jj - 1) + 1 ≠ 0 := by linarith
  have e4 : θ + a - 1 + jj + 1 ≠ 0 := by linarith
  have e5 : θ + a + 1 ≠ 0 := by linarith
  have e6 : θ + a + s ≠ 0 := by linarith
  have e7 : θ + a + 1 + jj + 1 ≠ 0 := by linarith
  simp only [Dq, rq, lq, Nat.cast_add]
  field_simp
  ring


lemma natCast_pred (j : ℕ) (h : 0 < j) : ((j - 1 : ℕ) : ℚ) = (j : ℚ) - 1 := by
  rw [Nat.cast_sub h]; simp

/-- Left side: `(Lag · X)(a,j)` as a three-term sum. -/
lemma Lag_Xmat_apply (s m : ℕ) (θ : ℚ) (a : Fin (s + m)) (j : Fin s) :
    (Lag s m θ * Xmat s m θ) a j =
      Dq s m θ (-(((j : ℕ) : ℚ) + 1)) * lag s (θ + ((a : ℕ) : ℚ)) j
      + rq s m θ (((j : ℕ) : ℚ) + 1) * lag s (θ + ((a : ℕ) : ℚ)) (j + 1)
      + lq θ (((j : ℕ) : ℚ) + 1) * lag s (θ + ((a : ℕ) : ℚ)) ((j : ℕ) - 1) := by
  rw [Matrix.mul_apply]
  have hT : ∀ y : Fin s, Lag s m θ a y * Xmat s m θ y j =
      (tri3 s (fun k : ℕ => rq s m θ ((k : ℚ) + 1)) (fun k : ℕ => Dq s m θ (-((k : ℚ) + 1)))
        (fun k : ℕ => lq θ ((k : ℚ) + 2))) j y * lag s (θ + ((a : ℕ) : ℚ)) (y : ℕ) := by
    intro y
    have h := congrFun (congrFun (tri3_transpose (n := s) (fun k : ℕ => lq θ ((k : ℚ) + 2))
      (fun k : ℕ => Dq s m θ (-((k : ℚ) + 1))) (fun k : ℕ => rq s m θ ((k : ℚ) + 1))) j) y
    simp only [Matrix.transpose_apply] at h
    have h' : Xmat s m θ y j = (tri3 s (fun k : ℕ => rq s m θ ((k : ℚ) + 1))
        (fun k : ℕ => Dq s m θ (-((k : ℚ) + 1))) (fun k : ℕ => lq θ ((k : ℚ) + 2))) j y := h
    rw [h', mul_comm]; rfl
  rw [Finset.sum_congr rfl (fun y _ => hT y)]
  have := tri3_sum (n := s) (fun k : ℕ => rq s m θ ((k : ℚ) + 1))
    (fun k : ℕ => Dq s m θ (-((k : ℚ) + 1))) (fun k : ℕ => lq θ ((k : ℚ) + 2)) j
    (fun y => lag s (θ + ((a : ℕ) : ℚ)) y) (lag s (θ + ((a : ℕ) : ℚ)) ((j : ℕ) - 1))
    (lq θ (((j : ℕ) : ℚ) + 1))
    (fun h => by
      have : (s : ℚ) = ((j : ℕ) : ℚ) + 1 := by exact_mod_cast h.symm
      simp [rq, this])
    (fun h => by simp [lq, h])
    (fun h => by
      refine ⟨?_, rfl⟩
      rw [natCast_pred _ h]; congr 1; ring)
  beta_reduce at this
  rw [this]

lemma Ltil_apply (s m : ℕ) (θ : ℚ) (a : Fin (s + m)) (j : Fin s) :
    (Ltil s m θ * Lag s m θ) a j =
      Dq s m θ (θ + (a : ℕ)) * lag s (θ + ((a : ℕ) : ℚ)) j
      + ((θ + a + 1) * (θ + a + 1 + s + 2 * m) * (((s + m : ℕ) : ℚ) - 1 - a) ^ 2)
          * lag s (θ + (((a : ℕ) + 1 : ℕ) : ℚ)) j
      + ((θ + a) * (a : ℚ) ^ 2 * (θ + a + s)) * lag s (θ + (((a : ℕ) - 1 : ℕ) : ℚ)) j := by
  rw [Matrix.mul_apply]
  have := tri3_sum (n := s + m)
    (fun a : ℕ => (θ + a + 1) * (θ + a + 1 + s + 2 * m) * (((s + m : ℕ) : ℚ) - 1 - a) ^ 2)
    (fun a : ℕ => Dq s m θ (θ + a))
    (fun a : ℕ => (θ + a + 1) * ((a : ℚ) + 1) ^ 2 * (θ + a + 1 + s)) a
    (fun b => lag s (θ + (b : ℚ)) j) (lag s (θ + (((a : ℕ) - 1 : ℕ) : ℚ)) j)
    ((θ + a) * (a : ℚ) ^ 2 * (θ + a + s))
    (fun h => by
      have : ((s + m : ℕ) : ℚ) = ((a : ℕ) : ℚ) + 1 := by exact_mod_cast h.symm
      simp [this])
    (fun h => by simp [h])
    (fun h => by
      refine ⟨?_, rfl⟩
      rw [natCast_pred _ h]; ring)
  beta_reduce at this
  exact this

/-- **(1a)**: `Lag · X = L̃ · Lag`. -/
theorem Lag_mul_Xmat (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    Lag s m θ * Xmat s m θ = Ltil s m θ * Lag s m θ := by
  ext a j
  rw [Lag_Xmat_apply, Ltil_apply]
  have ha0 : (0 : ℚ) ≤ ((a : ℕ) : ℚ) := Nat.cast_nonneg _
  have hj0 : (0 : ℚ) ≤ ((j : ℕ) : ℚ) := Nat.cast_nonneg _
  have hs0 : (0 : ℚ) ≤ (s : ℚ) := Nat.cast_nonneg _
  have hx : 0 < θ + ((a : ℕ) : ℚ) := by linarith
  set P := Pn s (θ + ((a : ℕ) : ℚ)) with hP
  have hjs : (j : ℕ) < s := j.2
  have g0 : lag s (θ + ((a : ℕ) : ℚ)) j = P / (θ + a + (j : ℚ) + 1) := by
    exact lag_eq' s _ hjs _ (by push_cast; ring) (by linarith)
  have hA : rq s m θ (((j : ℕ) : ℚ) + 1) * lag s (θ + ((a : ℕ) : ℚ)) (j + 1) =
      rq s m θ (((j : ℕ) : ℚ) + 1) * (P / (θ + a + ((j : ℚ) + 1) + 1)) := by
    by_cases h : (j : ℕ) + 1 < s
    · rw [lag_eq' s _ h (θ + a + ((j : ℚ) + 1) + 1) (by push_cast; ring) (by linarith)]
    · have : (s : ℚ) = ((j : ℕ) : ℚ) + 1 := by
        have : (j : ℕ) + 1 = s := by omega
        exact_mod_cast this.symm
      simp [rq, this]
  have hB : lq θ (((j : ℕ) : ℚ) + 1) * lag s (θ + ((a : ℕ) : ℚ)) ((j : ℕ) - 1) =
      lq θ (((j : ℕ) : ℚ) + 1) * (P / (θ + a + ((j : ℚ) - 1) + 1)) := by
    by_cases h : (j : ℕ) = 0
    · simp [lq, h]
    · have hj1 : (j : ℕ) - 1 < s := by omega
      rw [lag_eq' s _ hj1 (θ + a + ((j : ℚ) - 1) + 1)
        (by rw [Nat.sub_add_cancel (by omega)]; ring) (by linarith)]
  have g1 : lag s (θ + (((a : ℕ) + 1 : ℕ) : ℚ)) j =
      P * (θ + a + s + 1) / (θ + a + 1) / (θ + a + 1 + (j : ℚ) + 1) := by
    have e : θ + (((a : ℕ) + 1 : ℕ) : ℚ) = (θ + a) + 1 := by push_cast; ring
    rw [e, lag_eq' s _ hjs (θ + a + 1 + (j : ℚ) + 1) (by push_cast; ring) (by linarith)]
    have := Pn_shift s (θ + ((a : ℕ) : ℚ))
    have h1 : Pn s (θ + a + 1) = P * (θ + a + s + 1) / (θ + a + 1) := by
      rw [eq_div_iff (by linarith)]; exact this
    rw [h1]
  have hD : ((θ + a) * (a : ℚ) ^ 2 * (θ + a + s)) * lag s (θ + (((a : ℕ) - 1 : ℕ) : ℚ)) j =
      ((θ + a) * (a : ℚ) ^ 2 * (θ + a + s)) * (P * (θ + a) / (θ + a + s) / (θ + a - 1 + (j : ℚ) + 1)) := by
    by_cases h : (a : ℕ) = 0
    · simp [h]
    · have e : θ + (((a : ℕ) - 1 : ℕ) : ℚ) = (θ + a) - 1 := by rw [natCast_pred _ (by omega)]; ring
      rw [e, lag_eq' s _ hjs (θ + a - 1 + (j : ℚ) + 1) (by push_cast; ring) (by linarith)]
      have := Pn_shift s (θ + a - 1)
      have h1 : Pn s (θ + a - 1) = P * (θ + a) / (θ + a + s) := by
        rw [eq_div_iff (by linarith)]
        have e2 : θ + a - 1 + 1 = θ + a := by ring
        rw [e2] at this
        linear_combination (-1 : ℚ) * this
      rw [h1]
  have key := pointwise s m θ (a : ℚ) (j : ℚ) P hx hj0
  rw [g0, hA, hB, g1, hD]
  exact key

end CatalanCore.Bordered.Z1
