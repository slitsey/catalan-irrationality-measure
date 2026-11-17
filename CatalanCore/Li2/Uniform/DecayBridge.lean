module

public import CatalanCore.Li2.Uniform.Spec
public import CatalanCore.Li2.Decay.Fields

@[expose] public section

open MeasureTheory Set

namespace CatalanCore.Li2.Uniform

theorem decay_potential_eq (σ : Measure ℂ) (u : ℂ) :
    CatalanCore.Li2.Decay.U σ u = pot σ u := by
  unfold Decay.U Decay.P pot
  rw [integral_neg]

theorem decay_energy_eq (σ : Measure ℂ) :
    CatalanCore.Li2.Decay.I σ = energy σ := by
  simp only [Decay.I, energy, decay_potential_eq]

theorem decay_field_eq (z : ℝ) (hz : 0 < |z| ∧ |z| < 1) (d : DualDatum) (u : ℂ) :
    CatalanCore.Li2.Decay.W z d.σ u = W (signOf z) (Real.log (1 / |z|)) d u := by
  have hk : Decay.kappaRate z = (if signOf z = 1 then 2 * Real.pi else Real.pi) := by
    by_cases h : 0 < z <;> simp [Decay.kappaRate, signOf, h]
  unfold Decay.W Decay.V W
  rw [decay_potential_eq, hk, one_div, Real.log_inv]
  ring

theorem decay_atom_eq (z r : ℝ) (hz : 0 < |z| ∧ |z| < 1) (d : DualDatum) (x : ℝ) :
    CatalanCore.Li2.Decay.A z r d.σ x = A (Real.log (1 / |z|)) r d x := by
  unfold Decay.A Decay.omega A
  rw [decay_potential_eq, one_div, Real.log_inv]
  ring

theorem decay_freeBound_iff (z : ℝ) (hz : 0 < |z| ∧ |z| < 1)
    (F : DualFrame) (d : DualDatum) (θ : ℝ) :
    CatalanCore.Li2.Decay.FreeBound z F d θ ↔
      Admissible F (signOf z) (Real.log (1 / |z|)) d θ := by
  change (∀ u ∈ F.free (signOf z), Decay.W z d.σ u ≤ θ) ↔ _
  simp only [Admissible, decay_field_eq z hz]

theorem decay_dual_eq (z r : ℝ) (hz : 0 < |z| ∧ |z| < 1)
    (F : DualFrame) (d : DualDatum) (θ : ℝ) :
    CatalanCore.Li2.Decay.dualValue z r F d.σ θ =
      dual F (signOf z) (Real.log (1 / |z|)) r d θ := by
  unfold Decay.dualValue dual
  rw [decay_energy_eq]
  simp only [Decay.latPenalty, Decay.atomPenalty, Decay.pos, Decay.lat, lat,
    decay_field_eq z hz, decay_atom_eq z r hz]

end CatalanCore.Li2.Uniform

#print axioms CatalanCore.Li2.Uniform.decay_potential_eq
#print axioms CatalanCore.Li2.Uniform.decay_energy_eq
#print axioms CatalanCore.Li2.Uniform.decay_field_eq
#print axioms CatalanCore.Li2.Uniform.decay_atom_eq
#print axioms CatalanCore.Li2.Uniform.decay_freeBound_iff
#print axioms CatalanCore.Li2.Uniform.decay_dual_eq
