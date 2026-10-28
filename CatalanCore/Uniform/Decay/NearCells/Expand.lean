module

public import CatalanCore.Uniform.Decay.NearCells.CQ
public import CatalanCore.Uniform.Decay.NearCells.Branch
public import CatalanCore.Uniform.Decay.Tools.PotentialReal
public import CatalanCore.Uniform.Decay.Tools.LogJet

@[expose] public section

/-!
# Order-`n` expansion of the potential of one segment along a line (lane D, package D6b)

For a segment `A + t (B - A)` with polynomial density `∑ a_k t^k` and a field point
`z = z₀ + s d` (`s` real), `ζ(s) = ζ₀ + e s` with `ζ₀ = (z₀ - A)/(B - A)`, `e = d/(B - A)`:

`∫ density · log‖z - p(t)‖ = mass · log‖B - A‖ + Re( PA(ζ) Log(1-ζ) + PB(ζ) Log(-ζ) + R(ζ) )`

with `PB = ∑ w_k ζ^{k+1}`, `PA = mass - PB`, `R = - ∑ w_k ∑_{i≤k} ζ^{k-i}/(i+1)`, `w_k = a_k/(k+1)`
(from D1's `segment_potential_nonreal`).  Expanding `Log(1-ζ(s)) = L₁ + Log(1 - q₁ s)` etc. and
applying D1's `norm_jet_remainder_le` gives a polynomial model in `s` with an explicit remainder.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset Complex CatalanCore.Uniform.Decay.Tools

/-- Binomial expansion of `(z₀ + e s)^j` in powers of `s` (any `n > j`). -/
theorem binom_expand (z0 e s : ℂ) (j n : ℕ) (hj : j < n) :
    (z0 + e * s) ^ j = ∑ m ∈ range n, (e ^ m * (j.choose m : ℂ) * z0 ^ (j - m)) * s ^ m := by
  rw [add_comm, add_pow]
  have : ∑ m ∈ range (j + 1), (e * s) ^ m * z0 ^ (j - m) * (j.choose m : ℂ)
      = ∑ m ∈ range n, (e * s) ^ m * z0 ^ (j - m) * (j.choose m : ℂ) := by
    apply Finset.sum_subset
    · intro x hx; simp only [mem_range] at hx ⊢; omega
    · intro x hx hx'
      simp only [mem_range] at hx hx'
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [this]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- Coefficient weights `w_k = a_k/(k+1)`. -/
def wq (a : ℕ → ℚ) (k : ℕ) : ℚ := a k / ((k : ℚ) + 1)

/-- Mass of the density. -/
def massQ (a : ℕ → ℚ) (d : ℕ) : ℚ := ∑ k ∈ range (d + 1), wq a k

/-- `PB(ζ) = ∑ w_k ζ^{k+1}`. -/
noncomputable def PBf (a : ℕ → ℚ) (d : ℕ) (ζ : ℂ) : ℂ := ∑ k ∈ range (d + 1), (wq a k : ℂ) * ζ ^ (k + 1)

/-- `R(ζ) = - ∑ w_k ∑_{i≤k} ζ^{k-i}/(i+1)`. -/
noncomputable def Rf (a : ℕ → ℚ) (d : ℕ) (ζ : ℂ) : ℂ :=
  -∑ k ∈ range (d + 1), (wq a k : ℂ) * ∑ i ∈ range (k + 1), ζ ^ (k - i) / ((i : ℂ) + 1)

/-- **Closed form**, complex identity. -/
theorem closed_form_complex (a : ℕ → ℚ) (d : ℕ) (ζ : ℂ) :
    ∑ k ∈ range (d + 1), (a k : ℂ) * (Gk k ζ 1 - Gk k ζ 0)
      = ((massQ a d : ℚ) - PBf a d ζ) * Complex.log (1 - ζ) + PBf a d ζ * Complex.log (-ζ)
        + Rf a d ζ := by
  have hk : ∀ k : ℕ, ((k : ℂ) + 1) ≠ 0 := fun k => by exact_mod_cast Nat.succ_ne_zero k
  have step : ∀ k ∈ range (d + 1), (a k : ℂ) * (Gk k ζ 1 - Gk k ζ 0)
      = ((wq a k : ℂ) - (wq a k : ℂ) * ζ ^ (k + 1)) * Complex.log (1 - ζ)
        + (wq a k : ℂ) * ζ ^ (k + 1) * Complex.log (-ζ)
        - (wq a k : ℂ) * ∑ i ∈ range (k + 1), ζ ^ (k - i) / ((i : ℂ) + 1) := by
    intro k _
    unfold Gk GkL wq
    have h0 : ∑ j ∈ range (k + 1), ζ ^ (k - j) * (0 : ℂ) ^ (j + 1) / ((j : ℂ) + 1) = 0 := by
      apply Finset.sum_eq_zero; intro j _; simp
    have h1 : ∑ j ∈ range (k + 1), ζ ^ (k - j) * (1 : ℂ) ^ (j + 1) / ((j : ℂ) + 1)
        = ∑ j ∈ range (k + 1), ζ ^ (k - j) / ((j : ℂ) + 1) := by
      apply Finset.sum_congr rfl; intro j _; simp
    simp only [zero_sub, one_pow, h0, h1, zero_pow (Nat.succ_ne_zero k), mul_zero, sub_zero]
    push_cast
    have := hk k
    field_simp
    ring
  rw [Finset.sum_congr rfl step]
  simp only [PBf, Rf, massQ, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
  push_cast
  simp only [Finset.mul_sum]
  ring

/-- On the real axis, the real part of `Gk` is D1's `Hk`. -/
theorem re_Gk_real (k : ℕ) (r t : ℝ) : (Gk k (r : ℂ) (t : ℂ)).re = Hk k r t := by
  unfold Gk GkL Hk
  have h1 : (((t : ℂ) ^ (k + 1) - (r : ℂ) ^ (k + 1)) / ((k : ℂ) + 1)) =
      (((t ^ (k + 1) - r ^ (k + 1)) / ((k : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
  have h2 : (1 / ((k : ℂ) + 1)) * ∑ j ∈ range (k + 1), (r : ℂ) ^ (k - j) * (t : ℂ) ^ (j + 1) / ((j : ℂ) + 1)
      = (((1 / ((k : ℝ) + 1)) * ∑ j ∈ range (k + 1), r ^ (k - j) * t ^ (j + 1) / ((j : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h1, h2, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  show _ - _ = _
  have : ((Complex.log ((t : ℂ) - (r : ℂ))).re) = Real.log (t - r) := by
    rw [← Complex.ofReal_sub, Complex.log_re, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
  rw [this]

/-- **Closed form**, real potential (any field point). -/
theorem potential_closed (a : ℕ → ℚ) (d : ℕ) (A B z : ℂ) (hAB : B - A ≠ 0) :
    ∫ t in (0 : ℝ)..1, (∑ k ∈ range (d + 1), (a k : ℝ) * t ^ k) *
        Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = (massQ a d : ℝ) * Real.log ‖B - A‖ +
        (((massQ a d : ℚ) - PBf a d ((z - A) / (B - A))) * Complex.log (1 - (z - A) / (B - A))
          + PBf a d ((z - A) / (B - A)) * Complex.log (-((z - A) / (B - A)))
          + Rf a d ((z - A) / (B - A))).re := by
  set ζ := (z - A) / (B - A) with hζdef
  have hint : ∫ t in (0 : ℝ)..1, (∑ k ∈ range (d + 1), (a k : ℝ) * t ^ k) *
        Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = ∑ k ∈ range (d + 1), (a k : ℝ) * (Real.log ‖B - A‖ / ((k : ℝ) + 1) +
          (Gk k ζ 1 - Gk k ζ 0).re) := by
    by_cases him : ζ.im = 0
    · have hz : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simpa using him)
      rw [segment_potential_real (fun k => (a k : ℝ)) d A B z ζ.re hAB hz.symm.symm]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      have e1 : Gk k ζ 1 = Gk k (ζ.re : ℂ) ((1 : ℝ) : ℂ) := by rw [← hz]; simp
      have e0 : Gk k ζ 0 = Gk k (ζ.re : ℂ) ((0 : ℝ) : ℂ) := by rw [← hz]; simp
      rw [e1, e0, Complex.sub_re, re_Gk_real, re_Gk_real]
    · exact segment_potential_nonreal (fun k => (a k : ℝ)) d A B z hAB him
  rw [hint]
  rw [← closed_form_complex a d ζ]
  have e1 : ∑ k ∈ range (d + 1), (a k : ℝ) * (Real.log ‖B - A‖ / ((k : ℝ) + 1)
      + (Gk k ζ 1 - Gk k ζ 0).re)
      = ∑ k ∈ range (d + 1), (wq a k : ℝ) * Real.log ‖B - A‖
        + ∑ k ∈ range (d + 1), (a k : ℝ) * (Gk k ζ 1 - Gk k ζ 0).re := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold wq; push_cast
    have : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [e1, ← Finset.sum_mul]
  have e2 : (massQ a d : ℝ) = ∑ k ∈ range (d + 1), (wq a k : ℝ) := by
    unfold massQ; push_cast; rfl
  rw [e2]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (a k : ℂ) = ((a k : ℝ) : ℂ) by simp, Complex.re_ofReal_mul]

end CatalanCore.Uniform.Decay.NearCells
