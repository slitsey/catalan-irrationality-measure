module
public import CatalanMeasure.Parametric.RealIntegral
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset Set MeasureTheory OAI.InternalCatalan
noncomputable section

def pairedDeterminant (P : Parameters) (N : ℕ) (z : Fin (P.n N) → ℝ×ℝ) : ℝ :=
  Matrix.det (Matrix.of fun r k : Fin (P.n N) =>
    realRowAmplitude P N r.val (z k).1*(filteredColumn P N k.val).eval (z k).2 /
      (1-(z k).1*(z k).2))

theorem integrable_pairedDeterminant (P : Parameters) (N : ℕ) :
    Integrable (pairedDeterminant P N) (Measure.pi (fun _ : Fin (P.n N) =>
      realPlaceMeasure.prod (volume.restrict (Ioo (0:ℝ) 1)))) := by
  classical
  change Integrable (fun z : Fin (P.n N) → ℝ×ℝ =>pairedDeterminant P N z) _
  simp_rw [pairedDeterminant,Matrix.det_apply',Matrix.of_apply]
  apply integrable_finsetSum
  intro σ _
  exact (Integrable.fintype_prod (fun k : Fin (P.n N) =>
    integrable_realPlaceRow P N (σ k).val (filteredColumn P N k.val))).const_mul _

theorem real_det_eq_paired_integral (P : Parameters) (N : ℕ) :
    Matrix.det (Matrix.of fun r k : Fin (P.n N) =>realEntry P N r.val k.val) =
      ∫ z, pairedDeterminant P N z ∂Measure.pi (fun _ : Fin (P.n N) =>
        realPlaceMeasure.prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  classical
  let μ : Measure (ℝ×ℝ) :=realPlaceMeasure.prod (volume.restrict (Ioo (0:ℝ) 1))
  let F : Equiv.Perm (Fin (P.n N)) → (Fin (P.n N) → ℝ×ℝ) → ℝ := fun σ z =>
    ((Equiv.Perm.sign σ:ℤ):ℝ)*∏ k : Fin (P.n N),
      realRowAmplitude P N (σ k).val (z k).1*(filteredColumn P N k.val).eval (z k).2 /
        (1-(z k).1*(z k).2)
  have hF (σ : Equiv.Perm (Fin (P.n N))) :
      Integrable (F σ) (Measure.pi (fun _ : Fin (P.n N) =>μ)) := by
    exact (Integrable.fintype_prod (μ :=fun _ : Fin (P.n N) =>μ)
      (f :=fun k : Fin (P.n N) =>fun p : ℝ×ℝ =>
        realRowAmplitude P N (σ k).val p.1*(filteredColumn P N k.val).eval p.2/(1-p.1*p.2))
      (fun k =>integrable_realPlaceRow P N (σ k).val (filteredColumn P N k.val))).const_mul _
  have hsplit :=integral_finsetSum (μ :=Measure.pi (fun _ : Fin (P.n N) =>μ))
    (f :=F) univ (fun σ _ =>hF σ)
  simp_rw [pairedDeterminant,Matrix.det_apply',Matrix.of_apply]
  change _ = ∫ z,∑ σ : Equiv.Perm (Fin (P.n N)),F σ z
    ∂Measure.pi (fun _ : Fin (P.n N) =>μ)
  rw [hsplit]
  apply sum_congr rfl
  intro σ _
  dsimp only [F]
  rw [integral_const_mul,integral_fintype_prod_eq_prod
    (fun k : Fin (P.n N) =>fun p : ℝ×ℝ =>
      realRowAmplitude P N (σ k).val p.1*(filteredColumn P N k.val).eval p.2/(1-p.1*p.2))]
  congr 1
  apply prod_congr rfl
  intro k _
  exact realEntry_eq_realPlace_product P N (σ k).val k.val

theorem aeval_catalan_deltaPoly_eq_paired_integral {P : Parameters}
    (hP : Admissible P) {N : ℕ} (hN : 0<N) :
    aeval catalan (deltaPoly P N) = ∫ z,pairedDeterminant P N z
      ∂Measure.pi (fun _ : Fin (P.n N) =>
        realPlaceMeasure.prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  rw [aeval_catalan_deltaPoly hP hN]
  exact real_det_eq_paired_integral P N

end
end CatalanMeasure.Parametric
