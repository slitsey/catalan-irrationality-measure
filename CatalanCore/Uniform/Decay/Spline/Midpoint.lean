module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import CatalanLambda.Decay.ThmNEnergy

@[expose] public section

/-!
# Midpoint atomisation of a segment-polynomial trial measure (lane D, package D2)

A trial measure is a finite family of pieces `i : Fin n`: the segment `pt i t = A i + t (B i - A i)`,
`t ∈ [0,1]`, with a continuous (polynomial) real density `f i` in the parameter `t`.
Atoms: each piece is cut into `N` equal parameter cells, and the atom of cell `j` sits at the cell
midpoint carrying the exact integral of `f i` over the cell (`wAt`, `cAt`).

* `krho_lip` : `|k_ρ(z,w) - k_ρ(z,w')| ≤ ‖w - w'‖ / (2ρ)`.
* `midpoint_err` : for a `Λ`-Lipschitz kernel `κ`,
  `|∑ wAt κ(cAt) - ∑_i ∫ f_i κ(pt_i)| ≤ Λ ∑_i (L_i/(2N)) ∫|f_i|` (signed `f` allowed).
-/

namespace CatalanCore.Uniform.Decay.Spline

open Finset intervalIntegral CatalanLambda.Decay

section Krho

/-- `φ_ρ(s) = (1/2) log (s² + ρ²)`. -/
noncomputable def phiR (ρ s : ℝ) : ℝ := (1 / 2) * Real.log (s ^ 2 + ρ ^ 2)

theorem hasDerivAt_phiR {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    HasDerivAt (phiR ρ) (s / (s ^ 2 + ρ ^ 2)) s := by
  have hpos : s ^ 2 + ρ ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ρ ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (ρ ^ 2)
  have h2 := (h1.log hpos).const_mul (1 / 2 : ℝ)
  have h3 : HasDerivAt (fun s : ℝ => (1 / 2) * Real.log (s ^ 2 + ρ ^ 2))
      (1 / 2 * (2 * s / (s ^ 2 + ρ ^ 2))) s := h2
  have e : 1 / 2 * (2 * s / (s ^ 2 + ρ ^ 2)) = s / (s ^ 2 + ρ ^ 2) := by field_simp
  rw [e] at h3
  exact h3

theorem phiR_lip {ρ : ℝ} (hρ : 0 < ρ) (a b : ℝ) :
    |phiR ρ a - phiR ρ b| ≤ (1 / (2 * ρ)) * |a - b| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := phiR ρ) (s := Set.univ)
    (C := 1 / (2 * ρ)) (fun x _ => (hasDerivAt_phiR hρ x).differentiableAt)
    (fun x _ => by
      rw [(hasDerivAt_phiR hρ x).deriv, Real.norm_eq_abs, abs_div,
        abs_of_pos (by positivity : 0 < x ^ 2 + ρ ^ 2)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (|x| - ρ), sq_abs x])
    convex_univ (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using this

theorem krho_eq_phiR (ρ : ℝ) (z w : ℂ) : krho ρ z w = - phiR ρ ‖z - w‖ := by
  unfold krho phiR; ring

/-- **Lipschitz bound** for `k_ρ` in the second argument. -/
theorem krho_lip {ρ : ℝ} (hρ : 0 < ρ) (z w w' : ℂ) :
    |krho ρ z w - krho ρ z w'| ≤ (1 / (2 * ρ)) * ‖w - w'‖ := by
  rw [krho_eq_phiR, krho_eq_phiR]
  have h1 := phiR_lip hρ ‖z - w'‖ ‖z - w‖
  have h2 : |‖z - w'‖ - ‖z - w‖| ≤ ‖w - w'‖ := by
    have := abs_norm_sub_norm_le (z - w') (z - w)
    have e : z - w' - (z - w) = w - w' := by ring
    rwa [e] at this
  rw [show -phiR ρ ‖z - w‖ - -phiR ρ ‖z - w'‖ = phiR ρ ‖z - w'‖ - phiR ρ ‖z - w‖ by ring]
  have : (0 : ℝ) ≤ 1 / (2 * ρ) := by positivity
  exact h1.trans (mul_le_mul_of_nonneg_left h2 this)

/-- Lipschitz bound in the first argument. -/
theorem krho_lip_left {ρ : ℝ} (hρ : 0 < ρ) (z z' w : ℂ) :
    |krho ρ z w - krho ρ z' w| ≤ (1 / (2 * ρ)) * ‖z - z'‖ := by
  rw [krho_comm, krho_comm ρ z' w]; exact krho_lip hρ w z z'

theorem continuous_of_lip {κ : ℂ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hκ : ∀ w w', |κ w - κ w'| ≤ Λ * ‖w - w'‖) : Continuous κ := by
  have : LipschitzWith ⟨Λ, hΛ⟩ κ := LipschitzWith.of_dist_le_mul (fun x y => by
    have := hκ x y
    rw [Real.dist_eq, dist_eq_norm]
    exact this)
  exact this.continuous

end Krho

section Pieces

variable {n : ℕ}

/-- The point `A + t (B - A)` of piece `i`. -/
noncomputable def pt (A B : Fin n → ℂ) (i : Fin n) (t : ℝ) : ℂ := A i + (t : ℂ) * (B i - A i)

theorem continuous_pt (A B : Fin n → ℂ) (i : Fin n) : Continuous (pt A B i) := by
  unfold pt; fun_prop

theorem pt_dist (A B : Fin n → ℂ) (i : Fin n) (t s : ℝ) :
    ‖pt A B i t - pt A B i s‖ = |t - s| * ‖B i - A i‖ := by
  have : pt A B i t - pt A B i s = ((t - s : ℝ) : ℂ) * (B i - A i) := by
    unfold pt; push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Atom position: the midpoint of cell `j` of `N`. -/
noncomputable def cAt (A B : Fin n → ℂ) (N : ℕ) (i : Fin n) (j : Fin N) : ℂ :=
  pt A B i (((j : ℝ) + 1 / 2) / N)

/-- Atom weight: the exact integral of the density over the cell. -/
noncomputable def wAt (f : Fin n → ℝ → ℝ) (N : ℕ) (i : Fin n) (j : Fin N) : ℝ :=
  ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), f i t

/-- Sum over the `N` equal cells equals the integral over `[0,1]`. -/
theorem sum_cells {g : ℝ → ℝ} (hg : Continuous g) {N : ℕ} (hN : 0 < N) :
    ∑ j : Fin N, ∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), g t = ∫ t in (0 : ℝ)..1, g t := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (f := g) (μ := MeasureTheory.volume) (a := fun k : ℕ => (k : ℝ) / N) (n := N)
    (fun k _ => hg.intervalIntegrable _ _)
  have e1 : ((0 : ℕ) : ℝ) / N = 0 := by simp
  have e2 : ((N : ℕ) : ℝ) / N = 1 := by field_simp
  rw [e1, e2] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range (fun k => ∫ t in ((k : ℝ) / N)..((((k + 1 : ℕ)) : ℝ) / N), g t) N]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast; rfl

/-- One cell: the exact-integral atom at the midpoint versus the integral. -/
theorem cell_err {f : ℝ → ℝ} (hf : Continuous f) {κ : ℝ → ℝ} (hκ : Continuous κ) {a b k0 δ : ℝ}
    (hab : a ≤ b) (hk : ∀ t ∈ Set.Icc a b, |κ t - k0| ≤ δ) :
    |(∫ t in a..b, f t) * k0 - ∫ t in a..b, f t * κ t| ≤ δ * ∫ t in a..b, |f t| := by
  have e : (∫ t in a..b, f t) * k0 - ∫ t in a..b, f t * κ t
      = ∫ t in a..b, f t * (k0 - κ t) := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub]
    · congr 1; funext t; ring
    · exact (hf.mul continuous_const).intervalIntegrable _ _
    · exact (hf.mul hκ).intervalIntegrable _ _
  rw [e, ← Real.norm_eq_abs]
  have hint : IntervalIntegrable (fun t => δ * |f t|) MeasureTheory.volume a b :=
    (continuous_const.mul hf.abs).intervalIntegrable _ _
  have := intervalIntegral.norm_integral_le_of_norm_le hab (f := fun t => f t * (k0 - κ t))
    (g := fun t => δ * |f t|)
    (Filter.Eventually.of_forall (fun t ht => by
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (by rw [abs_sub_comm]; exact hk t (Set.Ioc_subset_Icc_self ht)) (abs_nonneg _))) hint
  rw [intervalIntegral.integral_const_mul] at this
  exact this

variable (A B : Fin n → ℂ) (f : Fin n → ℝ → ℝ)

/-- **Midpoint atomisation error** for a Lipschitz kernel. -/
theorem midpoint_err {κ : ℂ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hκ : ∀ w w', |κ w - κ w'| ≤ Λ * ‖w - w'‖) (hf : ∀ i, Continuous (f i))
    {N : ℕ} (hN : 0 < N) :
    |∑ i, ∑ j : Fin N, wAt f N i j * κ (cAt A B N i j) - ∑ i, ∫ t in (0 : ℝ)..1, f i t * κ (pt A B i t)|
      ≤ Λ * ∑ i, (‖B i - A i‖ / (2 * N)) * ∫ t in (0 : ℝ)..1, |f i t| := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hκc := continuous_of_lip hΛ hκ
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  have hci : Continuous (fun t => f i t * κ (pt A B i t)) := (hf i).mul (hκc.comp (continuous_pt A B i))
  have hκi : Continuous (fun t => κ (pt A B i t)) := hκc.comp (continuous_pt A B i)
  rw [← sum_cells hci hN, ← sum_cells (hf i).abs hN, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  have hab : ((j : ℝ) / N) ≤ ((j : ℝ) + 1) / N := by
    apply div_le_div_of_nonneg_right (by linarith) hN'.le
  have hk : ∀ t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N),
      |κ (pt A B i t) - κ (cAt A B N i j)| ≤ Λ * (‖B i - A i‖ / (2 * N)) := by
    intro t ht
    have h1 := hκ (pt A B i t) (cAt A B N i j)
    have h2 : ‖pt A B i t - cAt A B N i j‖ = |t - ((j : ℝ) + 1 / 2) / N| * ‖B i - A i‖ :=
      pt_dist A B i t _
    have h3 : |t - ((j : ℝ) + 1 / 2) / N| ≤ 1 / (2 * N) := by
      rw [abs_le]
      obtain ⟨l1, l2⟩ := ht
      have e1 : ((j : ℝ) + 1 / 2) / N - 1 / (2 * N) = (j : ℝ) / N := by field_simp; ring
      have e2 : ((j : ℝ) + 1 / 2) / N + 1 / (2 * N) = ((j : ℝ) + 1) / N := by field_simp; ring
      constructor <;> linarith
    have h4 : ‖pt A B i t - cAt A B N i j‖ ≤ ‖B i - A i‖ / (2 * N) := by
      rw [h2]
      calc |t - ((j : ℝ) + 1 / 2) / N| * ‖B i - A i‖ ≤ 1 / (2 * N) * ‖B i - A i‖ :=
            mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = ‖B i - A i‖ / (2 * N) := by ring
    exact h1.trans (mul_le_mul_of_nonneg_left h4 hΛ)
  have hcell := cell_err (f := f i) (hf i) hκi hab hk
  have e3 : wAt f N i j * κ (cAt A B N i j) = (∫ t in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), f i t) * κ (cAt A B N i j) := rfl
  rw [e3]
  refine hcell.trans (le_of_eq ?_)
  ring

end Pieces

end CatalanCore.Uniform.Decay.Spline
