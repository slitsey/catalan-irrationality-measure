module
public import CatalanMeasure.TwentyMarkedPositiveData
public import CatalanMeasure.TwentyResidualFixed0Certificate
public import CatalanMeasure.Cert.ResidualPositive
@[expose] public section
namespace CatalanMeasure.TwentyMarkedPositive
open CatalanMeasure.Cert TwentyResidualFixed0
set_option maxRecDepth 6000
set_option maxHeartbeats 6000000
theorem hCover : coverFrom A [] 0 cover 1=true := by decide +kernel
theorem hLeft : residualTwoEndOK Pc P (-101/500) 0=true := by decide +kernel
theorem hRight : residualTwoEndOK Pc P (-101/500) 1=true := by decide +kernel
theorem piece0_gap : integerGapOK AZ (cover.getD 0 (0,0,false))=true := by decide +kernel
theorem piece0_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 0 (0,0,false))=true := by decide +kernel
theorem piece1_gap : integerGapOK AZ (cover.getD 1 (0,0,false))=true := by decide +kernel
theorem piece1_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 1 (0,0,false))=true := by decide +kernel
theorem piece2_gap : integerGapOK AZ (cover.getD 2 (0,0,false))=true := by decide +kernel
theorem piece2_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 2 (0,0,false))=true := by decide +kernel
theorem piece3_gap : integerGapOK AZ (cover.getD 3 (0,0,false))=true := by decide +kernel
theorem piece3_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 3 (0,0,false))=true := by decide +kernel
theorem piece4_gap : integerGapOK AZ (cover.getD 4 (0,0,false))=true := by decide +kernel
theorem piece4_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 4 (0,0,false))=true := by decide +kernel
theorem piece5_gap : integerGapOK AZ (cover.getD 5 (0,0,false))=true := by decide +kernel
theorem piece5_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 5 (0,0,false))=true := by decide +kernel
theorem piece6_gap : integerGapOK AZ (cover.getD 6 (0,0,false))=true := by decide +kernel
theorem piece6_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 6 (0,0,false))=true := by decide +kernel
theorem piece7_gap : integerGapOK AZ (cover.getD 7 (0,0,false))=true := by decide +kernel
theorem piece7_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 7 (0,0,false))=true := by decide +kernel
theorem piece8_gap : integerGapOK AZ (cover.getD 8 (0,0,false))=true := by decide +kernel
theorem piece8_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 8 (0,0,false))=true := by decide +kernel
theorem piece9_gap : integerGapOK AZ (cover.getD 9 (0,0,false))=true := by decide +kernel
theorem piece9_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 9 (0,0,false))=true := by decide +kernel
theorem piece10_gap : integerGapOK AZ (cover.getD 10 (0,0,false))=true := by decide +kernel
theorem piece10_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 10 (0,0,false))=true := by decide +kernel
theorem piece11_gap : integerGapOK AZ (cover.getD 11 (0,0,false))=true := by decide +kernel
theorem piece11_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 11 (0,0,false))=true := by decide +kernel
theorem piece12_gap : integerGapOK AZ (cover.getD 12 (0,0,false))=true := by decide +kernel
theorem piece12_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 12 (0,0,false))=true := by decide +kernel
theorem piece13_gap : integerGapOK AZ (cover.getD 13 (0,0,false))=true := by decide +kernel
theorem piece13_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 13 (0,0,false))=true := by decide +kernel
theorem piece14_gap : integerGapOK AZ (cover.getD 14 (0,0,false))=true := by decide +kernel
theorem piece14_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 14 (0,0,false))=true := by decide +kernel
theorem piece15_gap : integerGapOK AZ (cover.getD 15 (0,0,false))=true := by decide +kernel
theorem piece15_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 15 (0,0,false))=true := by decide +kernel
theorem piece16_gap : integerGapOK AZ (cover.getD 16 (0,0,false))=true := by decide +kernel
theorem piece16_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 16 (0,0,false))=true := by decide +kernel
theorem piece17_gap : integerGapOK AZ (cover.getD 17 (0,0,false))=true := by decide +kernel
theorem piece17_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 17 (0,0,false))=true := by decide +kernel
theorem piece18_gap : integerGapOK AZ (cover.getD 18 (0,0,false))=true := by decide +kernel
theorem piece18_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 18 (0,0,false))=true := by decide +kernel
theorem piece19_gap : integerGapOK AZ (cover.getD 19 (0,0,false))=true := by decide +kernel
theorem piece19_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 19 (0,0,false))=true := by decide +kernel
theorem piece20_gap : integerGapOK AZ (cover.getD 20 (0,0,false))=true := by decide +kernel
theorem piece20_bracket : residualPositiveBracketOK Pc P A Q (-101/500)
    (cover.getD 20 (0,0,false))=true := by decide +kernel
theorem hGaps : cover.all (integerGapOK AZ)=true := by
  simp only [cover,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨piece0_gap,piece1_gap,piece2_gap,piece3_gap,piece4_gap,piece5_gap,piece6_gap,piece7_gap,piece8_gap,piece9_gap,piece10_gap,piece11_gap,piece12_gap,piece13_gap,piece14_gap,piece15_gap,piece16_gap,piece17_gap,piece18_gap,piece19_gap,piece20_gap,True.intro⟩
theorem hBrackets : cover.all (residualPositiveBracketOK Pc P A Q (-101/500))=true := by
  simp only [cover,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨piece0_bracket,piece1_bracket,piece2_bracket,piece3_bracket,piece4_bracket,piece5_bracket,piece6_bracket,piece7_bracket,piece8_bracket,piece9_bracket,piece10_bracket,piece11_bracket,piece12_bracket,piece13_bracket,piece14_bracket,piece15_bracket,piece16_bracket,piece17_bracket,piece18_bracket,piece19_bracket,piece20_bracket,True.intro⟩
theorem field_sup : ∀ x ∈ Set.Icc (0:ℝ) 1,
    residualTwoField Pc P x≤-(101/500:ℝ) := by
  simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,neg_div] using
    residual_positive_sup_of_checks TwentyResidualFixed0.hTail TwentyResidualFixed0.hAQ hCover
    (integerGaps_spec TwentyResidualFixed0.hScale TwentyResidualFixed0.hIntA hGaps)
    hBrackets hLeft hRight
end CatalanMeasure.TwentyMarkedPositive
