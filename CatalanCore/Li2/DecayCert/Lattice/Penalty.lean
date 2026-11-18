module
public import CatalanCore.Li2.DecayCert.Lattice.Defs
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Penalty.Analytic
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem integralModelQ_value (co : List ℚ) (R : ℚ) :
    (∫ u in (0:ℝ)..(R:ℝ),evalModel (co.map (fun q : ℚ => (q:ℝ))) u)=(integralModelQ co R:ℝ) := by
  simp_rw [evalModel_map_rat]
  rw [intervalIntegral.integral_finsetSum]
  · dsimp only [integralModelQ]
    rw [list_sum_map_range]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_const_mul,integral_pow]
    simp [div_eq_mul_inv] <;> ring
  · intro j hj
    exact (continuous_const.mul (continuous_id.pow j)).intervalIntegrable _ _

theorem penaltyBoundQ_sound (S : ℤ) (w : CellWitness) (R κ : ℚ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0:ℝ) (R:ℝ)))
    (hm : ModelsOn f ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) 0 R w.remainder)
    (hb : ∀ u ∈ Icc (0:ℝ) (R:ℝ),f u ∈ Icc (w.lb:ℝ) (w.ub:ℝ)) :
    (∫ u in (0:ℝ)..(R:ℝ),pos (f u-(κ:ℝ))) ≤ (penaltyBoundQ S w R κ:ℝ) := by
  have hRR : (0:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hfc : ContinuousOn (fun u => f u-(κ:ℝ)) (Icc (0:ℝ) (R:ℝ)) := hf.sub continuous_const.continuousOn
  have hpc : ContinuousOn (fun u => pos (f u-(κ:ℝ))) (Icc (0:ℝ) (R:ℝ)) :=
    fun u hu => Filter.Tendsto.max (hfc u hu) tendsto_const_nhds
  unfold penaltyBoundQ
  split_ifs with hneg hpos
  · have hn : (w.ub:ℝ) ≤ (κ:ℝ) := by exact_mod_cast hneg
    have he := LatticeGate.pos_integral_zero (fun u => f u-(κ:ℝ)) 0 (R:ℝ) hRR
      (fun u hu => sub_nonpos.mpr ((hb u hu).2.trans hn))
    rw [he]
    norm_num
  · have hp : (κ:ℝ) ≤ (w.lb:ℝ) := by exact_mod_cast hpos
    have hc : Continuous (fun u => evalModel ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) u) := by
      unfold evalModel
      fun_prop
    have hi : (∫ u in (0:ℝ)..(R:ℝ),pos (f u-(κ:ℝ))) ≤
        ∫ u in (0:ℝ)..(R:ℝ),evalModel ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) u+
          ((w.remainder:ℝ)-(κ:ℝ)) := by
      apply intervalIntegral.integral_mono_on hRR
        (hpc.intervalIntegrable_of_Icc hRR)
        ((hc.add continuous_const).intervalIntegrable _ _)
      intro u hu
      change max (f u-(κ:ℝ)) 0 ≤ _
      rw [max_eq_left (sub_nonneg.mpr (hp.trans (hb u hu).1))]
      have hh := (abs_le.mp (hm.2.2 u hu)).2
      change f u-(κ:ℝ) ≤ evalModel ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) u+((w.remainder:ℝ)-(κ:ℝ))
      linarith
    have he : (∫ u in (0:ℝ)..(R:ℝ),evalModel ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) u+
          ((w.remainder:ℝ)-(κ:ℝ)))=
        ((integralModelQ (gridCoeffs S w) R+w.remainder*R-κ*R:ℚ):ℝ) := by
      rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),integralModelQ_value]
      simp only [intervalIntegral.integral_const,smul_eq_mul,sub_zero]
      push_cast
      ring
    rw [he] at hi
    exact hi.trans (by exact_mod_cast (le_max_left (integralModelQ (gridCoeffs S w) R+w.remainder*R-κ*R) 0))
  · have hi := LatticeGate.pos_integral_constant (fun u => f u-(κ:ℝ)) 0 (R:ℝ)
      ((w.ub:ℝ)-(κ:ℝ)) hRR hfc (fun u hu => sub_le_sub_right (hb u hu).2 _)
    simpa only [sub_zero,Rat.cast_mul,Rat.cast_max,Rat.cast_sub,Rat.cast_zero] using hi
#print axioms integralModelQ_value
#print axioms penaltyBoundQ_sound
end
end CatalanCore.Li2.DecayCert
