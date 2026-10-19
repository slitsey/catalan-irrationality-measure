module

public import CatalanCore.Bordered.Z1.Block
public import CatalanCore.Bordered.Z1.Seg

/-!
# Z1.5: node operator `L`, Cauchy vectors, Lemma 3 (`L C = C X` on a column range).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

/-- The node operator `L` (`K × K`, tridiagonal): `L_{a,a+1} = F(x_a)`, `L_{a+1,a} = G(x_{a+1})`,
`L_{aa} = D(x_a)`, `x_a = θ + a`. -/
noncomputable def Lmat (s m : ℕ) (θ : ℝ) : Matrix (Fin (s + m)) (Fin (s + m)) ℝ :=
  tri3 (s + m) (fun a => Fq s m θ (θ + a)) (fun a => Dq s m θ (θ + a))
    (fun a => Gq θ (θ + a + 1))

/-- Cauchy entry `1 / (x_b + k + 1)`. -/
noncomputable def ccf (θ : ℝ) (b k : ℕ) : ℝ := 1 / (θ + b + (k + 1))

/-- `u_b = ∑_{k<s} v_k / (x_b + k + 1)`. -/
noncomputable def uvec (s : ℕ) (θ : ℝ) (v : ℕ → ℝ) (b : ℕ) : ℝ := ∑ k ∈ range s, v k * ccf θ b k

lemma ccf_succ (θ : ℝ) (a j : ℕ) : ccf θ (a + 1) j = 1 / (θ + a + (j + 1) + 1) := by
  unfold ccf; push_cast; congr 1; ring

lemma ccf_pred (θ : ℝ) (a j : ℕ) (h : 0 < a) : ccf θ (a - 1) j = 1 / (θ + a + (j + 1) - 1) := by
  unfold ccf; rw [Nat.cast_sub h]; push_cast; congr 1; ring

lemma ccf_col_succ (θ : ℝ) (a j : ℕ) : ccf θ a (j + 1) = 1 / (θ + a + (j + 1) + 1) := by
  unfold ccf; push_cast; congr 1; ring

lemma ccf_col_pred (θ : ℝ) (a j : ℕ) (h : 0 < j) : ccf θ a (j - 1) = 1 / (θ + a + (j + 1) - 1) := by
  unfold ccf; rw [Nat.cast_sub h]; push_cast; congr 1; ring

lemma ccf_def (θ : ℝ) (a j : ℕ) : ccf θ a j = 1 / (θ + a + (j + 1)) := rfl

/-- The corner `0/0` identity. -/
lemma corner_id (s m d : ℕ) (θ : ℝ) (hθ : θ = -((s + m + d : ℕ) : ℝ)) (h1 : 1 ≤ s + m) :
    Dq s m θ (θ + ((s + m - 1 : ℕ) : ℝ)) / (-1) + Gq θ (θ + ((s + m - 1 : ℕ) : ℝ)) / (-2) =
      Dq s m θ (-(d : ℝ)) / (-1) + lq θ (d : ℝ) / (-2) := by
  subst hθ
  rw [Nat.cast_sub h1]
  simp only [Dq, Gq, lq, Nat.cast_add, Nat.cast_one]
  ring

/-- Core identity at `z = x + y`. -/
lemma star_core (s m d a j : ℕ) (θ : ℝ) (hθ : θ = -((s + m + d : ℕ) : ℝ)) (ha : a < s + m)
    (hj : j < d) :
    Dq s m θ (θ + a) * (1 / (θ + a + (j + 1))) + Fq s m θ (θ + a) * (1 / (θ + a + (j + 1) + 1))
      + Gq θ (θ + a) * (1 / (θ + a + (j + 1) - 1)) =
    Dq s m θ (-((j : ℝ) + 1)) * (1 / (θ + a + (j + 1)))
      + rq s m θ ((j : ℝ) + 1) * (1 / (θ + a + (j + 1) + 1))
      + lq θ ((j : ℝ) + 1) * (1 / (θ + a + (j + 1) - 1)) := by
  have ha' : (a : ℝ) + 1 ≤ s + m := by exact_mod_cast ha
  have hj' : (j : ℝ) + 1 ≤ d := by exact_mod_cast hj
  have hd0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hθ' : θ = -((s : ℝ) + m + d) := by rw [hθ]; push_cast; ring
  by_cases hz1 : θ + a + (j + 1) + 1 = 0
  · -- corner
    have hA : a = s + m - 1 := by
      have : (a : ℝ) + 1 = s + m := by linarith
      have : a + 1 = s + m := by exact_mod_cast this
      omega
    have hJ : (j : ℝ) + 1 = d := by linarith
    have e1 : (1 : ℝ) / (θ + a + (j + 1) + 1) = 0 := by rw [hz1]; simp
    have hz : θ + a + (j + 1) = -1 := by linarith
    have hz2 : θ + a + (j + 1) - 1 = -2 := by linarith
    rw [e1, hz2, hz]
    simp only [mul_zero, add_zero]
    have := corner_id s m d θ hθ (by omega)
    rw [← hA] at this
    have hjd : lq θ ((j : ℝ) + 1) = lq θ (d : ℝ) := by rw [hJ]
    have hjd2 : Dq s m θ (-((j : ℝ) + 1)) = Dq s m θ (-(d : ℝ)) := by rw [hJ]
    rw [hjd, hjd2]
    simp only [one_div, div_eq_mul_inv] at this ⊢
    linear_combination this
  · have h0 : θ + a + (j + 1) ≠ 0 := by
      intro h; apply hz1; linarith
    have h2 : θ + a + (j + 1) - 1 ≠ 0 := by
      intro h; linarith
    have key := bispectral s m θ (θ + a) ((j : ℝ) + 1) (by intro h; apply h0; linarith)
      hz1 (by intro h; apply h2; linarith)
    simp only [mul_one_div]
    linarith [key]

end CatalanCore.Bordered.Z1
