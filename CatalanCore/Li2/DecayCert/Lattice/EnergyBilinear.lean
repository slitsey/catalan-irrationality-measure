module
public import CatalanCore.Li2.DecayCert.Lattice.SelfEnergy
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem datum_energy_two (d : DualDatum) (μ ν : Measure ℂ) (hσ : d.σ=μ+ν) :
    I d.σ=I μ+I ν+2*(∫ u,U μ u ∂ν) := by
  haveI := d.finite
  have hμ : μ ≤ d.σ := by rw [hσ]; exact le_add_of_nonneg_right (show (0:Measure ℂ) ≤ ν from bot_le)
  have hν : ν ≤ d.σ := by rw [hσ]; exact le_add_of_nonneg_left (show (0:Measure ℂ) ≤ μ from bot_le)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_of_le d.σ hμ
  haveI : IsFiniteMeasure ν := isFiniteMeasure_of_le d.σ hν
  have hpair (a b : Measure ℂ) [IsFiniteMeasure a] [IsFiniteMeasure b] (ha : a ≤ d.σ) (hb : b ≤ d.σ) :
      Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (a.prod b) :=
    d.selfIntegrable.mono_measure (Measure.prod_mono ha hb)
  have hi (a b : Measure ℂ) [IsFiniteMeasure a] [IsFiniteMeasure b] (ha : a ≤ d.σ) (hb : b ≤ d.σ) : Integrable (U b) a := by
    change Integrable (fun u => -(∫ y,Real.log ‖u-y‖ ∂b)) a
    exact (hpair a b ha hb).integral_prod_left.neg
  have hU (u : ℂ) : U d.σ u=U μ u+U ν u := by
    have hm := (d.pointLogIntegrable u).mono_measure hμ
    have hn := (d.pointLogIntegrable u).mono_measure hν
    change -(∫ y,Real.log ‖u-y‖ ∂d.σ)= -(∫ y,Real.log ‖u-y‖ ∂μ) + -(∫ y,Real.log ‖u-y‖ ∂ν)
    rw [hσ,integral_add_measure hm hn]
    ring
  have hcross : (∫ u,U ν u ∂μ)=∫ u,U μ u ∂ν := by
    change (∫ u,-(∫ y,Real.log ‖u-y‖ ∂ν) ∂μ)=∫ u,-(∫ y,Real.log ‖u-y‖ ∂μ) ∂ν
    rw [integral_neg,integral_neg]
    congr 1
    rw [integral_integral_swap (hpair μ ν hμ hν)]
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by simp only [norm_sub_rev])
  have hμtotal : Integrable (U μ) d.σ := by
    rw [hσ]
    exact integrable_add_measure.mpr ⟨hi μ μ hμ hμ,hi ν μ hν hμ⟩
  have hνtotal : Integrable (U ν) d.σ := by
    rw [hσ]
    exact integrable_add_measure.mpr ⟨hi μ ν hμ hν,hi ν ν hν hν⟩
  change (∫ u,U d.σ u ∂d.σ)=_
  simp_rw [hU]
  rw [integral_add hμtotal hνtotal,hσ,
    integral_add_measure (hi μ μ hμ hμ) (hi ν μ hν hμ),
    integral_add_measure (hi μ ν hμ hν) (hi ν ν hν hν),hcross]
  change I μ+(∫ u,U μ u ∂ν)+((∫ u,U μ u ∂ν)+I ν)=_
  ring
#print axioms datum_energy_two
end
end CatalanCore.Li2.DecayCert
