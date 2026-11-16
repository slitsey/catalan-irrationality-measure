module

public import CatalanCore.Zeta5.Potential.Basic

/-!
# Z5-POTENTIAL, part 5: positivity by an exact sum of squares (ZD15) and the bound `F` (ZD16)

`f(cos θ) = |Σ_{j ≤ N} h_j e^{ijθ}|²` for `f = Σ a_k T_k`, `a_0 = Σ h_j²`,
`a_k = 2 Σ_j h_j h_{j+k}`: an exact identity (`chebF_sos`), hence `f ≥ 0` on `[-1, 1]` for
`s ≥ 0` (`chebF_sos_nonneg`) and `c_0 = s a_0 = λ` for `s = λ/a_0` (`sos_const_eq`).
`sup_le_sumAbs`: `Σ|c_k| ≥ sup f`.
-/

@[expose] public section

open Set Polynomial CatalanMeasure.Signed OAI.InternalCatalan

namespace CatalanCore.Zeta5.Potential

noncomputable section

/-! ### ZD15: positivity by an exact sum of squares -/

/-- `a_0 = Σ h_j²`, `a_k = 2 Σ_j h_j h_{j+k}` (`1 ≤ k ≤ N`). -/
def sosCoef (h : ℕ → ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  if k = 0 then ∑ j ∈ Finset.range (N + 1), h j ^ 2
  else 2 * ∑ j ∈ Finset.range (N + 1 - k), h j * h (j + k)

theorem sos_step (h : ℕ → ℝ) (n : ℕ) (θ : ℝ) :
    (∑ j ∈ Finset.range (n + 1), h j * Real.cos ((j : ℝ) * θ)) ^ 2 +
      (∑ j ∈ Finset.range (n + 1), h j * Real.sin ((j : ℝ) * θ)) ^ 2 =
    ((∑ j ∈ Finset.range n, h j * Real.cos ((j : ℝ) * θ)) ^ 2 +
      (∑ j ∈ Finset.range n, h j * Real.sin ((j : ℝ) * θ)) ^ 2) + h n ^ 2 +
      2 * ∑ k ∈ Finset.range n, h (n - 1 - k) * h n * Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hr : ∑ k ∈ Finset.range n, h (n - 1 - k) * h n * Real.cos (((k + 1 : ℕ) : ℝ) * θ) =
      ∑ j ∈ Finset.range n, h j * h n * Real.cos (((n - j : ℕ) : ℝ) * θ) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have e1 : n - 1 - (n - 1 - k) = k := by omega
    have e3 : n - 1 - k + 1 = n - k := by omega
    rw [e1, e3]
  rw [hr]
  have hc : ∀ j ∈ Finset.range n, h j * h n * Real.cos (((n - j : ℕ) : ℝ) * θ) =
      h n * (h j * Real.cos ((j : ℝ) * θ)) * Real.cos ((n : ℝ) * θ) +
      h n * (h j * Real.sin ((j : ℝ) * θ)) * Real.sin ((n : ℝ) * θ) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [Nat.cast_sub hj'.le, sub_mul, Real.cos_sub]
    ring
  rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have := Real.sin_sq_add_cos_sq ((n : ℝ) * θ)
  set S := ∑ j ∈ Finset.range n, h j * Real.cos ((j : ℝ) * θ)
  set T := ∑ j ∈ Finset.range n, h j * Real.sin ((j : ℝ) * θ)
  nlinarith [this]

theorem sos_identity (h : ℕ → ℝ) (n : ℕ) (θ : ℝ) :
    (∑ j ∈ Finset.range n, h j * Real.cos ((j : ℝ) * θ)) ^ 2 +
      (∑ j ∈ Finset.range n, h j * Real.sin ((j : ℝ) * θ)) ^ 2 =
    ∑ j ∈ Finset.range n, h j ^ 2 + 2 * ∑ k ∈ Finset.range n,
      (∑ j ∈ Finset.range (n - 1 - k), h j * h (j + k + 1)) *
        Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sos_step, ih, Finset.sum_range_succ (fun j => h j ^ 2)]
    have e : ∀ k ∈ Finset.range n, (∑ j ∈ Finset.range (n + 1 - 1 - k), h j * h (j + k + 1)) =
        (∑ j ∈ Finset.range (n - 1 - k), h j * h (j + k + 1)) + h (n - 1 - k) * h n := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have h1 : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      have h2 : n - 1 - k + k + 1 = n := by omega
      rw [h1, Finset.sum_range_succ, h2]
    have e0 : n + 1 - 1 - n = 0 := by omega
    have hsum : ∑ k ∈ Finset.range n, (∑ j ∈ Finset.range (n + 1 - 1 - k), h j * h (j + k + 1)) *
        Real.cos (((k + 1 : ℕ) : ℝ) * θ) =
        ∑ k ∈ Finset.range n, (∑ j ∈ Finset.range (n - 1 - k), h j * h (j + k + 1)) *
          Real.cos (((k + 1 : ℕ) : ℝ) * θ) +
        ∑ k ∈ Finset.range n, h (n - 1 - k) * h n * Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k hk => by rw [e k hk, add_mul]
    rw [Finset.sum_range_succ (fun k => (∑ j ∈ Finset.range (n + 1 - 1 - k), h j * h (j + k + 1)) *
      Real.cos (((k + 1 : ℕ) : ℝ) * θ)), e0, Finset.sum_range_zero, zero_mul, add_zero, hsum]
    ring

/-- **ZD15.**  `f(cos θ) = |Σ_{j ≤ N} h_j e^{ijθ}|²` for `f = Σ a_k T_k`, with
`a_0 = Σ h_j²`, `a_k = 2 Σ_j h_j h_{j+k}`: an exact identity, no inequality. -/
theorem chebF_sos (h : ℕ → ℝ) (N : ℕ) (θ : ℝ) :
    chebF (sosCoef h N) N (Real.cos θ) =
      (∑ j ∈ Finset.range (N + 1), h j * Real.cos ((j : ℝ) * θ)) ^ 2 +
        (∑ j ∈ Finset.range (N + 1), h j * Real.sin ((j : ℝ) * θ)) ^ 2 := by
  rw [sos_identity, chebF_cos, Finset.sum_range_succ' (fun k => sosCoef h N k * Real.cos ((k : ℝ) * θ)),
    Finset.sum_range_succ (fun k => (∑ j ∈ Finset.range (N + 1 - 1 - k), h j * h (j + k + 1)) *
      Real.cos (((k + 1 : ℕ) : ℝ) * θ)) N]
  have hlast : N + 1 - 1 - N = 0 := by omega
  rw [hlast, Finset.sum_range_zero, zero_mul, add_zero, Finset.mul_sum]
  simp only [sosCoef, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, ite_true,
    Nat.succ_ne_zero, ite_false]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have : N + 1 - (k + 1) = N + 1 - 1 - k := by omega
  rw [this]
  have e : ∀ j, j + (k + 1) = j + k + 1 := fun j => by ring
  simp_rw [e]
  ring

theorem chebF_smul (s : ℝ) (c : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    chebF (fun k => s * c k) N x = s * chebF c N x := by
  unfold chebF; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **ZD15, positivity**: for `s ≥ 0`, the density `f = s · Σ a_k T_k` is nonnegative on `[-1, 1]`,
and `f`'s constant coefficient is `s · Σ h_j²`. -/
theorem chebF_sos_nonneg (h : ℕ → ℝ) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 ≤ chebF (fun k => s * sosCoef h N k) N x := by
  rw [chebF_smul]
  have : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  rw [← this, chebF_sos]
  positivity

theorem sos_const (h : ℕ → ℝ) (N : ℕ) (s : ℝ) :
    (fun k => s * sosCoef h N k) 0 = s * ∑ j ∈ Finset.range (N + 1), h j ^ 2 := by
  simp [sosCoef]

/-- With `s = λ / a_0` the constant coefficient is exactly `λ`. -/
theorem sos_const_eq (h : ℕ → ℝ) (N : ℕ) (lam : ℝ) (ha : ∑ j ∈ Finset.range (N + 1), h j ^ 2 ≠ 0) :
    (fun k => lam / (∑ j ∈ Finset.range (N + 1), h j ^ 2) * sosCoef h N k) 0 = lam := by
  rw [sos_const]; field_simp

/-! ### ZD16: the rational bound `F = Σ |c_k| ≥ sup f` -/

theorem sup_le_sumAbs (c : ℕ → ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    chebF c N x ≤ ∑ k ∈ Finset.range (N + 1), |c k| :=
  (le_abs_self _).trans (abs_chebF_le c N hx)

end

end CatalanCore.Zeta5.Potential
