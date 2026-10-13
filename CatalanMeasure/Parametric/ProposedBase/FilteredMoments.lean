module
public import CatalanMeasure.Parametric.ProposedBase.Definitions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open OAI.InternalCatalan Finset
noncomputable section

theorem filteredMoment_den {i k : ℕ} (hi : i<130) (hk : k<96) :
    ((filteredMomentRat i k).den:ZMod 1009) ≠ 0 := by
  unfold filteredMomentRat
  apply (rational_residue_sum _ _ ?_).1
  intro v hv
  change ((filterCoeffRat proposed 1 v * momentRat i (15+k+v)).den:ZMod 1009) ≠ 0
  apply (rational_residue_mul (filterCoeff_den proposed 1 v) ?_).1
  exact momentRat_odd_prime_small_den_ne_zero (by omega) (by omega)
    (by have := mem_range.mp hv; omega)

theorem filteredZeta_den {i k : ℕ} (hi : i<130) (hk : k<96) :
    ((filteredZetaRat i k).den:ZMod 1009) ≠ 0 := by
  unfold filteredZetaRat
  apply (rational_residue_sum _ _ ?_).1
  intro v hv
  change ((filterCoeffRat proposed 1 v * zetaRat i (15+k+v)).den:ZMod 1009) ≠ 0
  apply (rational_residue_mul (filterCoeff_den proposed 1 v) ?_).1
  exact zetaRat_small_den_ne_zero (by omega) (by have := mem_range.mp hv; omega)

theorem filteredMoment_residue {i k : ℕ} (hi : i<130) (hk : k<96) :
    palindromicRatResidue 1009 (filteredMomentRat i k) =
      ∑ v ∈ range 8, ((-1:ZMod 1009)^v*(7:ℕ).choose v) *
        palindromicRatResidue 1009 (momentRat i (15+k+v)) := by
  have hd : ∀ v ∈ range 8, ((momentRat i (15+k+v)).den:ZMod 1009) ≠ 0 := by
    intro v hv
    exact momentRat_odd_prime_small_den_ne_zero (by omega) (by omega)
      (by have := mem_range.mp hv; omega)
  unfold filteredMomentRat
  change palindromicRatResidue 1009
    (∑ v ∈ range 8,filterCoeffRat proposed 1 v * momentRat i (15+k+v)) = _
  rw [palindromicRatResidue_sum _ _ (fun v hv =>
    (rational_residue_mul (filterCoeff_den proposed 1 v) (hd v hv)).1)]
  apply sum_congr rfl
  intro v hv
  change palindromicRatResidue 1009 (filterCoeffRat proposed 1 v * momentRat i (15+k+v)) = _
  rw [palindromicRatResidue_mul (filterCoeff_den proposed 1 v) (hd v hv),filterCoeff_residue]
  rfl

theorem filteredZeta_residue {i k : ℕ} (hi : i<130) (hk : k<96) :
    palindromicRatResidue 1009 (filteredZetaRat i k) =
      ∑ v ∈ range 8, ((-1:ZMod 1009)^v*(7:ℕ).choose v) *
        palindromicRatResidue 1009 (zetaRat i (15+k+v)) := by
  have hd : ∀ v ∈ range 8, ((zetaRat i (15+k+v)).den:ZMod 1009) ≠ 0 := by
    intro v hv
    exact zetaRat_small_den_ne_zero (by omega) (by have := mem_range.mp hv; omega)
  unfold filteredZetaRat
  change palindromicRatResidue 1009
    (∑ v ∈ range 8,filterCoeffRat proposed 1 v * zetaRat i (15+k+v)) = _
  rw [palindromicRatResidue_sum _ _ (fun v hv =>
    (rational_residue_mul (filterCoeff_den proposed 1 v) (hd v hv)).1)]
  apply sum_congr rfl
  intro v hv
  change palindromicRatResidue 1009 (filterCoeffRat proposed 1 v * zetaRat i (15+k+v)) = _
  rw [palindromicRatResidue_mul (filterCoeff_den proposed 1 v) (hd v hv),filterCoeff_residue]
  rfl

theorem filtered_sum_swap (c : ℕ → ZMod 1009) (f : ℕ → ℕ → ZMod 1009) :
    (∑ i ∈ range 130, c i *
      ∑ v ∈ range 8, ((-1:ZMod 1009)^v*(7:ℕ).choose v)*f i v) =
      ∑ v ∈ range 8, ((-1:ZMod 1009)^v*(7:ℕ).choose v)*
        ∑ i ∈ range 130, c i*f i v := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro i _
  ring

/-- Link the prefiltered moment columns to the actual rational-entry contraction. -/
theorem baseFilteredContraction_filtered_forms (r : ℕ) (k : Fin 96) :
    baseFilteredContraction proposed 1009 r k =
      (∑ i ∈ range 130, ((rowP proposed 1 r).coeff i:ZMod 1009)*
        palindromicRatResidue 1009 (filteredMomentRat i k.val)) -
      (3/2:ZMod 1009)*∑ i ∈ range 130, ((rowD proposed 1 r).coeff i:ZMod 1009)*
        palindromicRatResidue 1009 (filteredZetaRat i k.val) := by
  have hm : (∑ i ∈ range 130, ((rowP proposed 1 r).coeff i:ZMod 1009)*
      palindromicRatResidue 1009 (filteredMomentRat i k.val)) =
      ∑ v ∈ range 8, ((-1:ZMod 1009)^v*(7:ℕ).choose v)*
        ∑ i ∈ range 130, ((rowP proposed 1 r).coeff i:ZMod 1009)*
          palindromicRatResidue 1009 (momentRat i (15+k.val+v)) := by
    calc
      _ = ∑ i ∈ range 130, ((rowP proposed 1 r).coeff i:ZMod 1009)*
          ∑ v ∈ range 8, ((-1:ZMod 1009)^v*(7:ℕ).choose v)*
            palindromicRatResidue 1009 (momentRat i (15+k.val+v)) := by
              apply sum_congr rfl
              intro i hi
              rw [filteredMoment_residue (mem_range.mp hi) k.isLt]
      _ = _ := filtered_sum_swap _ _
  have hz : (∑ i ∈ range 130, ((rowD proposed 1 r).coeff i:ZMod 1009)*
      palindromicRatResidue 1009 (filteredZetaRat i k.val)) =
      ∑ v ∈ range 8, ((-1:ZMod 1009)^v*(7:ℕ).choose v)*
        ∑ i ∈ range 130, ((rowD proposed 1 r).coeff i:ZMod 1009)*
          palindromicRatResidue 1009 (zetaRat i (15+k.val+v)) := by
    calc
      _ = ∑ i ∈ range 130, ((rowD proposed 1 r).coeff i:ZMod 1009)*
          ∑ v ∈ range 8, ((-1:ZMod 1009)^v*(7:ℕ).choose v)*
            palindromicRatResidue 1009 (zetaRat i (15+k.val+v)) := by
              apply sum_congr rfl
              intro i hi
              rw [filteredZeta_residue (mem_range.mp hi) k.isLt]
      _ = _ := filtered_sum_swap _ _
  rw [hm,hz]
  simp only [baseFilteredContraction,baseRawContraction,baseFilterWeight]
  change (∑ v ∈ range 8, ((-1:ZMod 1009)^v*(7:ℕ).choose v)*
    ((∑ i ∈ range 130, ((rowP proposed 1 r).coeff i:ZMod 1009)*
      palindromicRatResidue 1009 (momentRat i (15+k.val+v))) -
    (3/2:ZMod 1009)*∑ i ∈ range 130, ((rowD proposed 1 r).coeff i:ZMod 1009)*
      palindromicRatResidue 1009 (zetaRat i (15+k.val+v)))) = _
  simp_rw [mul_sub,sum_sub_distrib,mul_left_comm _ (3/2:ZMod 1009),← mul_sum]

end
end CatalanMeasure.Parametric.ProposedBase
