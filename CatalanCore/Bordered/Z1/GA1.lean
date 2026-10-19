module

public import CatalanCore.Bordered.Z1.GAdefs

/-!
# Z1.5: Lemma 3 in vector form, `L (C v) = C (X v)` for `v` supported on the first `d` columns.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

theorem star (s m d a j : ℕ) (θ : ℝ) (hθ : θ = -((s + m + d : ℕ) : ℝ)) (ha : a < s + m) (hj : j < d)
    (hds : d < s) :
    Dq s m θ (θ + a) * ccf θ a j
      + (if a + 1 < s + m then Fq s m θ (θ + a) * ccf θ (a + 1) j else 0)
      + (if 0 < a then Gq θ (θ + ((a - 1 : ℕ) : ℝ) + 1) * ccf θ (a - 1) j else 0) =
    Dq s m θ (-((j : ℝ) + 1)) * ccf θ a j
      + (if j + 1 < s then rq s m θ ((j : ℝ) + 1) * ccf θ a (j + 1) else 0)
      + (if 0 < j then lq θ (((j - 1 : ℕ) : ℝ) + 2) * ccf θ a (j - 1) else 0) := by
  have uF : (if a + 1 < s + m then Fq s m θ (θ + a) * ccf θ (a + 1) j else 0) =
      Fq s m θ (θ + a) * (1 / (θ + a + (j + 1) + 1)) := by
    by_cases h : a + 1 < s + m
    · rw [if_pos h, ccf_succ]
    · rw [if_neg h]
      have h1 : ((s + m : ℕ) : ℝ) = (a : ℝ) + 1 := by
        have : s + m = a + 1 := by omega
        rw [this]; push_cast; ring
      have : Fq s m θ (θ + a) = 0 := by unfold Fq; rw [h1]; ring
      rw [this]; simp
  have uG : (if 0 < a then Gq θ (θ + ((a - 1 : ℕ) : ℝ) + 1) * ccf θ (a - 1) j else 0) =
      Gq θ (θ + a) * (1 / (θ + a + (j + 1) - 1)) := by
    by_cases h : 0 < a
    · rw [if_pos h, ccf_pred θ a j h]
      have : θ + ((a - 1 : ℕ) : ℝ) + 1 = θ + a := by rw [Nat.cast_sub h]; push_cast; ring
      rw [this]
    · rw [if_neg h]
      have : a = 0 := by omega
      subst this
      simp [Gq]
  have uR : (if j + 1 < s then rq s m θ ((j : ℝ) + 1) * ccf θ a (j + 1) else 0) =
      rq s m θ ((j : ℝ) + 1) * (1 / (θ + a + (j + 1) + 1)) := by
    rw [if_pos (by omega), ccf_col_succ]
  have uL : (if 0 < j then lq θ (((j - 1 : ℕ) : ℝ) + 2) * ccf θ a (j - 1) else 0) =
      lq θ ((j : ℝ) + 1) * (1 / (θ + a + (j + 1) - 1)) := by
    by_cases h : 0 < j
    · rw [if_pos h, ccf_col_pred θ a j h]
      have : ((j - 1 : ℕ) : ℝ) + 2 = (j : ℝ) + 1 := by rw [Nat.cast_sub h]; push_cast; ring
      rw [this]
    · rw [if_neg h]
      have : j = 0 := by omega
      subst this
      simp [lq]
  rw [uF, uG, uR, uL, ccf_def]
  exact star_core s m d a j θ hθ ha hj

/-- **Lemma 3**: `L(−c) (C v) = λ (C v)` when `X v = λ v`, `v` supported on `k < d`. -/
theorem L_Cv (s m d : ℕ) (θ : ℝ) (hθ : θ = -((s + m + d : ℕ) : ℝ)) (hds : d < s)
    (v : ℕ → ℝ) (hv : ∀ k, d ≤ k → v k = 0) (lam : ℝ)
    (hXv : ∀ k : Fin s, (Xmat s m θ *ᵥ (fun j : Fin s => v j)) k = lam * v k) (a : Fin (s + m)) :
    (Lmat s m θ *ᵥ (fun b : Fin (s + m) => uvec s θ v b)) a = lam * uvec s θ v a := by
  -- left side
  rw [Lmat, tri3_row]
  have hL : Dq s m θ (θ + ((a : ℕ) : ℝ)) * uvec s θ v a
      + (if (a : ℕ) + 1 < s + m then Fq s m θ (θ + ((a : ℕ) : ℝ)) * uvec s θ v (a + 1) else 0)
      + (if 0 < (a : ℕ) then Gq θ (θ + (((a : ℕ) - 1 : ℕ) : ℝ) + 1) * uvec s θ v ((a : ℕ) - 1) else 0)
      = ∑ j ∈ range s, v j * (Dq s m θ (θ + ((a : ℕ) : ℝ)) * ccf θ a j
        + (if (a : ℕ) + 1 < s + m then Fq s m θ (θ + ((a : ℕ) : ℝ)) * ccf θ (a + 1) j else 0)
        + (if 0 < (a : ℕ) then Gq θ (θ + (((a : ℕ) - 1 : ℕ) : ℝ) + 1) * ccf θ ((a : ℕ) - 1) j
            else 0)) := by
    simp only [uvec, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · by_cases h : (a : ℕ) + 1 < s + m
        · simp only [h, if_true, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        · simp [h]
    · by_cases h : 0 < (a : ℕ)
      · simp only [h, if_true, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · simp [h]
  rw [hL]
  -- right side
  have hR : lam * uvec s θ v a = ∑ j ∈ range s, v j * (Dq s m θ (-((j : ℝ) + 1)) * ccf θ a j
      + (if j + 1 < s then rq s m θ ((j : ℝ) + 1) * ccf θ a (j + 1) else 0)
      + (if 0 < j then lq θ (((j - 1 : ℕ) : ℝ) + 2) * ccf θ a (j - 1) else 0)) := by
    have h1 : lam * uvec s θ v a = ∑ k : Fin s, (lam * v k) * ccf θ a k := by
      rw [uvec, Finset.mul_sum, Finset.sum_range]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : ∑ k : Fin s, (lam * v k) * ccf θ a k =
        ∑ k : Fin s, (Xmat s m θ *ᵥ (fun j : Fin s => v j)) k * ccf θ a k :=
      Finset.sum_congr rfl fun k _ => by rw [hXv k]
    have h3 : ∑ k : Fin s, (Xmat s m θ *ᵥ (fun j : Fin s => v j)) k * ccf θ a k =
        ∑ j : Fin s, v j * ((Xmat s m θ)ᵀ *ᵥ (fun k : Fin s => ccf θ a k)) j := by
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have h4 : ∀ j : Fin s, ((Xmat s m θ)ᵀ *ᵥ (fun k : Fin s => ccf θ a k)) j =
        Dq s m θ (-((j : ℝ) + 1)) * ccf θ a j
          + (if (j : ℕ) + 1 < s then rq s m θ ((j : ℝ) + 1) * ccf θ a (j + 1) else 0)
          + (if 0 < (j : ℕ) then lq θ ((((j : ℕ) - 1 : ℕ) : ℝ) + 2) * ccf θ a ((j : ℕ) - 1) else 0) := by
      intro j
      rw [Xmat, tri3_transpose, tri3_row]
    rw [h1, h2, h3, Finset.sum_range]
    exact Finset.sum_congr rfl fun j _ => by rw [h4 j]
  rw [hR]
  rw [Finset.sum_range, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : (j : ℕ) < d
  · rw [star s m d a j θ hθ a.2 hj hds]
  · rw [hv j (by omega)]; simp

end CatalanCore.Bordered.Z1
