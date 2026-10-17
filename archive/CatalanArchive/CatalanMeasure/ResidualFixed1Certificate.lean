module
public import CatalanArchive.CatalanMeasure.ResidualFixed1Data
@[expose] public section
namespace CatalanMeasure.ResidualFixed1
open CatalanMeasure.Cert
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
theorem hTail : tailsInDisk P=true := by decide +kernel
theorem hAQ : fracSum (residualTwoFracs Pc P)=(A,Q) := by decide +kernel
theorem hIntA : A=lpSmul scale (AZ.map (fun z:ℤ =>(z:ℚ))) := by decide +kernel
theorem hScale : scale≠0 := by decide +kernel
theorem hCover : coverFrom A [] (-1) cover 0=true := by decide +kernel
theorem hLeft : residualTwoEndOK Pc P (-1/8) (-1)=true := by decide +kernel
theorem hRight : residualTwoEndOK Pc P (-1/8) 0=true := by decide +kernel
theorem piece0_gap : integerGapOK AZ (cover.getD 0 (0,0,false))=true := by decide +kernel
theorem piece0_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 0 (0,0,false))=true := by decide +kernel
theorem piece1_gap : integerGapOK AZ (cover.getD 1 (0,0,false))=true := by decide +kernel
theorem piece1_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 1 (0,0,false))=true := by decide +kernel
theorem piece2_gap : integerGapOK AZ (cover.getD 2 (0,0,false))=true := by decide +kernel
theorem piece2_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 2 (0,0,false))=true := by decide +kernel
theorem piece3_gap : integerGapOK AZ (cover.getD 3 (0,0,false))=true := by decide +kernel
theorem piece3_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 3 (0,0,false))=true := by decide +kernel
theorem piece4_gap : integerGapOK AZ (cover.getD 4 (0,0,false))=true := by decide +kernel
theorem piece4_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 4 (0,0,false))=true := by decide +kernel
theorem piece5_gap : integerGapOK AZ (cover.getD 5 (0,0,false))=true := by decide +kernel
theorem piece5_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 5 (0,0,false))=true := by decide +kernel
theorem piece6_gap : integerGapOK AZ (cover.getD 6 (0,0,false))=true := by decide +kernel
theorem piece6_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 6 (0,0,false))=true := by decide +kernel
theorem piece7_gap : integerGapOK AZ (cover.getD 7 (0,0,false))=true := by decide +kernel
theorem piece7_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 7 (0,0,false))=true := by decide +kernel
theorem piece8_gap : integerGapOK AZ (cover.getD 8 (0,0,false))=true := by decide +kernel
theorem piece8_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 8 (0,0,false))=true := by decide +kernel
theorem piece9_gap : integerGapOK AZ (cover.getD 9 (0,0,false))=true := by decide +kernel
theorem piece9_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 9 (0,0,false))=true := by decide +kernel
theorem piece10_gap : integerGapOK AZ (cover.getD 10 (0,0,false))=true := by decide +kernel
theorem piece10_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 10 (0,0,false))=true := by decide +kernel
theorem piece11_gap : integerGapOK AZ (cover.getD 11 (0,0,false))=true := by decide +kernel
theorem piece11_bracket : residualTwoBracketOK Pc P A Q (-1/8)
    (cover.getD 11 (0,0,false))=true := by decide +kernel
theorem hGaps : cover.all (integerGapOK AZ)=true := by
  simp only [cover,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨piece0_gap,piece1_gap,piece2_gap,piece3_gap,piece4_gap,piece5_gap,piece6_gap,piece7_gap,piece8_gap,piece9_gap,piece10_gap,piece11_gap,True.intro⟩
theorem hBrackets : cover.all (residualTwoBracketOK Pc P A Q (-1/8))=true := by
  simp only [cover,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨piece0_bracket,piece1_bracket,piece2_bracket,piece3_bracket,piece4_bracket,piece5_bracket,piece6_bracket,piece7_bracket,piece8_bracket,piece9_bracket,piece10_bracket,piece11_bracket,True.intro⟩
theorem field_sup : ∀ x ∈ Set.Icc (-1:ℝ) 0,
    residualTwoField Pc P x≤-(1/8:ℝ) := by
  simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,neg_div] using
    residualTwo_sup_of_checks hTail hAQ hCover
    (integerGaps_spec hScale hIntA hGaps) hBrackets hLeft hRight
end CatalanMeasure.ResidualFixed1
