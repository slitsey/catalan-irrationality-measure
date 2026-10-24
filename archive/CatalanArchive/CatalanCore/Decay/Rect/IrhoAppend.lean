module

public import CatalanLambda.Decay.KrhoPD
public import CatalanLambda.Decay.ThmNEnergy

@[expose] public section

/-!
# Energy of a concatenated, rescaled measure (P6DECAY, G2)

`I_ρ((σ₁ ⧺ σ₂)/a) = (I(σ₁) + 2 I(σ₁,σ₂) + I(σ₂)) / a²`, the generic expansion behind every hybrid
`I_ok` (the square part, the cross energy and the correction's self energy are bounded separately).
-/

open Finset
open CatalanLambda.Decay (Irho krho krho_comm)

namespace CatalanCore.Decay

theorem Irho_append_div {K1 K2 : ℕ} (ρ a : ℝ) (ha : a ≠ 0) (c1 : Fin K1 → ℂ) (w1 : Fin K1 → ℝ)
    (c2 : Fin K2 → ℂ) (w2 : Fin K2 → ℝ) :
    Irho ρ (Fin.append c1 c2) (fun k => Fin.append w1 w2 k / a)
      = (Irho ρ c1 w1 + 2 * ∑ k, ∑ l, w1 k * w2 l * krho ρ (c1 k) (c2 l) + Irho ρ c2 w2) / a ^ 2 := by
  unfold Irho
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hsw : ∑ i : Fin K2, ∑ j : Fin K1, w2 i * w1 j * krho ρ (c2 i) (c1 j)
      = ∑ j : Fin K1, ∑ i : Fin K2, w1 j * w2 i * krho ρ (c1 j) (c2 i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [krho_comm]; ring
  have e : ∀ x y z : ℝ, x / a * (y / a) * z = (x * y * z) / a ^ 2 := by
    intro x y z; field_simp
  simp_rw [e]
  simp only [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hsw]
  ring

end CatalanCore.Decay
