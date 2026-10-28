module

public import CatalanCore.Uniform.Decay.Spline.Errors

@[expose] public section

/-!
# Mesh form of the midpoint losses (lane D, package D2)

If every physical cell has length `‖B_i - A_i‖ / N ≤ h`, the midpoint losses are
`etaN ≤ Vp · h / (4ρ)` (potential; the stated bound `V h/(2ρ)` is weaker) and the energy loss
`2 Vp etaN ≤ Vp² h / (2ρ)` (the stated `V² h/ρ` is weaker).
-/

namespace CatalanCore.Uniform.Decay.Spline

open Finset CatalanLambda.Decay

variable {n : ℕ} {A B : Fin n → ℂ} {f : Fin n → ℝ → ℝ}

theorem etaN_le_mesh {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) {h : ℝ}
    (hh : ∀ i, ‖B i - A i‖ / N ≤ h) : etaN A B f ρ N ≤ Vp f * h / (4 * ρ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold etaN Vp
  have h1 : ∀ i, (‖B i - A i‖ / (2 * N)) * ∫ t in (0 : ℝ)..1, |f i t|
      ≤ (h / 2) * ∫ t in (0 : ℝ)..1, |f i t| := by
    intro i
    apply mul_le_mul_of_nonneg_right _ (intervalIntegral.integral_nonneg zero_le_one
      (fun t _ => abs_nonneg _))
    have := hh i
    have e : ‖B i - A i‖ / (2 * N) = (‖B i - A i‖ / N) / 2 := by field_simp
    rw [e]; linarith
  have h2 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => h1 i)
  rw [← Finset.mul_sum] at h2
  calc (1 / (2 * ρ)) * ∑ i, (‖B i - A i‖ / (2 * N)) * ∫ t in (0 : ℝ)..1, |f i t|
      ≤ (1 / (2 * ρ)) * ((h / 2) * ∑ i, ∫ t in (0 : ℝ)..1, |f i t|) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (∑ i, ∫ t in (0 : ℝ)..1, |f i t|) * h / (4 * ρ) := by field_simp; ring

theorem energy_atom_err_mesh {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) {h : ℝ}
    (hh : ∀ i, ‖B i - A i‖ / N ≤ h) (hf : ∀ i, Continuous (f i)) :
    |Irho ρ (cK A B N) (wK f N) - Irho0 A B f ρ| ≤ Vp f ^ 2 * h / (2 * ρ) := by
  refine (energy_atom_err hf hρ hN).trans ?_
  have := etaN_le_mesh (A := A) (B := B) (f := f) hρ hN hh
  have hV := Vp_nonneg f
  calc 2 * Vp f * etaN A B f ρ N ≤ 2 * Vp f * (Vp f * h / (4 * ρ)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = Vp f ^ 2 * h / (2 * ρ) := by field_simp; ring

end CatalanCore.Uniform.Decay.Spline
