module
public import CatalanArchive.CatalanMeasure.StrongTrial.Norms
public import CatalanArchive.CatalanMeasure.StrongTrial.RootCoverage
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX0
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX1
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX2
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX3
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX4
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX5
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX6
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX7
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX8
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX9
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX10
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX11
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX12
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX13
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX14
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX15
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX16
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX17
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX18
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX19
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX20
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX21
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX22
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX23
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX24
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX25
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX26
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX27
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX28
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX29
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesX30
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY0
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY1
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY2
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY3
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY4
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY5
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY6
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY7
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY8
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY9
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY10
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY11
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY12
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY13
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY14
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY15
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY16
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesY17
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG00
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG02
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG03
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG04
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG05
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG06
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG07
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG08
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG010
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesRG00
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG10
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG11
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG13
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG14
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG15
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG16
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG17
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG19
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG111
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG113
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG115
public import CatalanArchive.CatalanMeasure.StrongTrial.GapsRG117
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesRG10
public import CatalanArchive.CatalanMeasure.StrongTrial.ValuesRG11
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem hGapsX : NoRootGaps AX planX := by
  exact rootBudgetGapsX
theorem hBracketsX : planX.all (shiftedRowBracketOK R Pc Vc P V AX QX MX)=true := by
  simp only [planX,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨(by decide +kernel),bracketX_1,(by decide +kernel),bracketX_3,(by decide +kernel),bracketX_5,(by decide +kernel),bracketX_7,(by decide +kernel),bracketX_9,(by decide +kernel),bracketX_11,(by decide +kernel),bracketX_13,(by decide +kernel),bracketX_15,(by decide +kernel),bracketX_17,(by decide +kernel),bracketX_19,(by decide +kernel),bracketX_21,(by decide +kernel),bracketX_23,(by decide +kernel),bracketX_25,(by decide +kernel),bracketX_27,(by decide +kernel),bracketX_29,(by decide +kernel),bracketX_31,(by decide +kernel),bracketX_33,(by decide +kernel),bracketX_35,(by decide +kernel),bracketX_37,(by decide +kernel),bracketX_39,(by decide +kernel),bracketX_41,(by decide +kernel),bracketX_43,(by decide +kernel),bracketX_45,(by decide +kernel),bracketX_47,(by decide +kernel),bracketX_49,(by decide +kernel),bracketX_51,(by decide +kernel),bracketX_53,(by decide +kernel),bracketX_55,(by decide +kernel),bracketX_57,(by decide +kernel),bracketX_59,(by decide +kernel),bracketX_61,(by decide +kernel),bracketX_63,(by decide +kernel),bracketX_65,(by decide +kernel),bracketX_67,(by decide +kernel),bracketX_69,(by decide +kernel),bracketX_71,(by decide +kernel),bracketX_73,(by decide +kernel),bracketX_75,(by decide +kernel),bracketX_77,(by decide +kernel),bracketX_79,(by decide +kernel),bracketX_81,(by decide +kernel),bracketX_83,(by decide +kernel),bracketX_85,(by decide +kernel),bracketX_87,(by decide +kernel),bracketX_89,(by decide +kernel),bracketX_91,(by decide +kernel),bracketX_93,(by decide +kernel),bracketX_95,(by decide +kernel),bracketX_97,(by decide +kernel),bracketX_99,(by decide +kernel),bracketX_101,(by decide +kernel),bracketX_103,(by decide +kernel),bracketX_105,(by decide +kernel),bracketX_107,(by decide +kernel),bracketX_109,(by decide +kernel),bracketX_111,(by decide +kernel),bracketX_113,(by decide +kernel),bracketX_115,(by decide +kernel),bracketX_117,(by decide +kernel),bracketX_119,(by decide +kernel),bracketX_121,(by decide +kernel),bracketX_123,(by decide +kernel),bracketX_125,(by decide +kernel),bracketX_127,(by decide +kernel),bracketX_129,(by decide +kernel),bracketX_131,(by decide +kernel),bracketX_133,(by decide +kernel),bracketX_135,(by decide +kernel),bracketX_137,(by decide +kernel),bracketX_139,(by decide +kernel),bracketX_141,(by decide +kernel),bracketX_143,(by decide +kernel),bracketX_145,(by decide +kernel),bracketX_147,(by decide +kernel),bracketX_149,(by decide +kernel),bracketX_151,(by decide +kernel),bracketX_153,(by decide +kernel),bracketX_155,(by decide +kernel),bracketX_157,(by decide +kernel),bracketX_159,(by decide +kernel),bracketX_161,(by decide +kernel),(by decide +kernel),bracketX_164,(by decide +kernel),bracketX_166,(by decide +kernel),bracketX_168,(by decide +kernel),bracketX_170,(by decide +kernel),bracketX_172,(by decide +kernel),bracketX_174,(by decide +kernel),bracketX_176,(by decide +kernel),bracketX_178,(by decide +kernel),bracketX_180,(by decide +kernel),bracketX_182,(by decide +kernel),bracketX_184,(by decide +kernel),bracketX_186,(by decide +kernel),bracketX_188,(by decide +kernel),bracketX_190,(by decide +kernel),bracketX_192,(by decide +kernel),bracketX_194,(by decide +kernel),bracketX_196,(by decide +kernel),bracketX_198,(by decide +kernel),bracketX_200,(by decide +kernel),bracketX_202,(by decide +kernel),bracketX_204,(by decide +kernel),bracketX_206,(by decide +kernel),bracketX_208,(by decide +kernel),bracketX_210,(by decide +kernel),bracketX_212,(by decide +kernel),bracketX_214,(by decide +kernel),bracketX_216,(by decide +kernel),bracketX_218,(by decide +kernel),bracketX_220,(by decide +kernel),bracketX_222,(by decide +kernel),bracketX_224,(by decide +kernel),bracketX_226,(by decide +kernel),bracketX_228,(by decide +kernel),bracketX_230,(by decide +kernel),bracketX_232,(by decide +kernel),bracketX_234,(by decide +kernel),bracketX_236,(by decide +kernel),bracketX_238,(by decide +kernel),bracketX_240,(by decide +kernel),bracketX_242,(by decide +kernel),bracketX_244,(by decide +kernel),bracketX_246,(by decide +kernel),bracketX_248,(by decide +kernel),bracketX_250,(by decide +kernel),bracketX_252,(by decide +kernel),bracketX_254,(by decide +kernel),bracketX_256,(by decide +kernel),bracketX_258,(by decide +kernel),bracketX_260,(by decide +kernel),bracketX_262,(by decide +kernel),bracketX_264,(by decide +kernel),bracketX_266,(by decide +kernel),bracketX_268,(by decide +kernel),bracketX_270,(by decide +kernel),bracketX_272,(by decide +kernel),bracketX_274,(by decide +kernel),bracketX_276,(by decide +kernel),bracketX_278,(by decide +kernel),bracketX_280,(by decide +kernel),bracketX_282,(by decide +kernel),bracketX_284,(by decide +kernel),bracketX_286,(by decide +kernel),bracketX_288,(by decide +kernel),bracketX_290,(by decide +kernel),bracketX_292,(by decide +kernel),bracketX_294,(by decide +kernel),bracketX_296,(by decide +kernel),bracketX_298,(by decide +kernel),bracketX_300,(by decide +kernel),bracketX_302,(by decide +kernel),bracketX_304,(by decide +kernel),bracketX_306,(by decide +kernel),bracketX_308,(by decide +kernel),True.intro⟩
theorem hGapsY : NoRootGaps AY planY := by
  exact rootBudgetGapsY
theorem hBracketsY : planY.all (shiftedColumnBracketOK C Vc V AY QY MY)=true := by
  simp only [planY,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨(by decide +kernel),bracketY_1,(by decide +kernel),bracketY_3,(by decide +kernel),bracketY_5,(by decide +kernel),bracketY_7,(by decide +kernel),bracketY_9,(by decide +kernel),bracketY_11,(by decide +kernel),bracketY_13,(by decide +kernel),bracketY_15,(by decide +kernel),bracketY_17,(by decide +kernel),bracketY_19,(by decide +kernel),bracketY_21,(by decide +kernel),bracketY_23,(by decide +kernel),bracketY_25,(by decide +kernel),bracketY_27,(by decide +kernel),bracketY_29,(by decide +kernel),bracketY_31,(by decide +kernel),bracketY_33,(by decide +kernel),bracketY_35,(by decide +kernel),bracketY_37,(by decide +kernel),bracketY_39,(by decide +kernel),bracketY_41,(by decide +kernel),bracketY_43,(by decide +kernel),bracketY_45,(by decide +kernel),bracketY_47,(by decide +kernel),bracketY_49,(by decide +kernel),bracketY_51,(by decide +kernel),bracketY_53,(by decide +kernel),bracketY_55,(by decide +kernel),bracketY_57,(by decide +kernel),bracketY_59,(by decide +kernel),bracketY_61,(by decide +kernel),bracketY_63,(by decide +kernel),bracketY_65,(by decide +kernel),bracketY_67,(by decide +kernel),bracketY_69,(by decide +kernel),bracketY_71,(by decide +kernel),bracketY_73,(by decide +kernel),bracketY_75,(by decide +kernel),bracketY_77,(by decide +kernel),bracketY_79,(by decide +kernel),bracketY_81,(by decide +kernel),bracketY_83,(by decide +kernel),bracketY_85,(by decide +kernel),bracketY_87,(by decide +kernel),bracketY_89,(by decide +kernel),bracketY_91,(by decide +kernel),bracketY_93,(by decide +kernel),bracketY_95,(by decide +kernel),bracketY_97,(by decide +kernel),bracketY_99,(by decide +kernel),bracketY_101,(by decide +kernel),bracketY_103,(by decide +kernel),bracketY_105,(by decide +kernel),bracketY_107,(by decide +kernel),bracketY_109,(by decide +kernel),bracketY_111,(by decide +kernel),bracketY_113,(by decide +kernel),bracketY_115,(by decide +kernel),bracketY_117,(by decide +kernel),bracketY_119,(by decide +kernel),bracketY_121,(by decide +kernel),bracketY_123,(by decide +kernel),bracketY_125,(by decide +kernel),bracketY_127,(by decide +kernel),bracketY_129,(by decide +kernel),bracketY_131,(by decide +kernel),bracketY_133,(by decide +kernel),bracketY_135,(by decide +kernel),bracketY_137,(by decide +kernel),bracketY_139,(by decide +kernel),bracketY_141,(by decide +kernel),bracketY_143,(by decide +kernel),bracketY_145,(by decide +kernel),bracketY_147,(by decide +kernel),bracketY_149,(by decide +kernel),bracketY_151,(by decide +kernel),bracketY_153,(by decide +kernel),bracketY_155,(by decide +kernel),bracketY_157,(by decide +kernel),bracketY_159,(by decide +kernel),bracketY_161,(by decide +kernel),bracketY_163,(by decide +kernel),bracketY_165,(by decide +kernel),bracketY_167,(by decide +kernel),bracketY_169,(by decide +kernel),bracketY_171,(by decide +kernel),bracketY_173,(by decide +kernel),True.intro⟩
theorem hGapsRG0 : NoRootGaps AR planRG0 := by
  simp only [planRG0,noRootGaps_cons,noRootGaps_nil]
  exact ⟨gapRG0_0,(by intro h; cases h),gapRG0_2,gapRG0_3,gapRG0_4,gapRG0_5,gapRG0_6,gapRG0_7,gapRG0_8,(by intro h; cases h),gapRG0_10,True.intro⟩
theorem hBracketsRG0 : planRG0.all (markedResidualClosedBracketOK Pc P AR QR gapResidualM)=true := by
  simp only [planRG0,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨(by decide +kernel),bracketRG0_1,(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),bracketRG0_9,(by decide +kernel),True.intro⟩
theorem hGapsRG1 : NoRootGaps AR planRG1 := by
  simp only [planRG1,noRootGaps_cons,noRootGaps_nil]
  exact ⟨gapRG1_0,gapRG1_1,(by intro h; cases h),gapRG1_3,gapRG1_4,gapRG1_5,gapRG1_6,gapRG1_7,(by intro h; cases h),gapRG1_9,(by intro h; cases h),gapRG1_11,(by intro h; cases h),gapRG1_13,(by intro h; cases h),gapRG1_15,(by intro h; cases h),gapRG1_17,True.intro⟩
theorem hBracketsRG1 : planRG1.all (markedResidualClosedBracketOK Pc P AR QR gapResidualM)=true := by
  simp only [planRG1,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨(by decide +kernel),(by decide +kernel),bracketRG1_2,(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),bracketRG1_8,(by decide +kernel),bracketRG1_10,(by decide +kernel),bracketRG1_12,(by decide +kernel),bracketRG1_14,(by decide +kernel),bracketRG1_16,(by decide +kernel),True.intro⟩

theorem row_sup : ∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
    shiftedRowField R Pc Vc P V x ≤ (MX:ℝ) :=
  shiftedRowCheck_spec (by norm_num [R]) (by norm_num [R]) hAQX hchainX
    hGapsX hBracketsX hendX

theorem column_sup : ∀ s ∈ Ioo (0:ℝ) 1,
    shiftedColumnField C Vc V s ≤ (MY:ℝ) :=
  shiftedColumnCheck_spec (by norm_num [C]) (by norm_num [C]) hAQY hchainY
    hGapsY hBracketsY

theorem residual_negative_gap : ∀ x ∈ Icc (-1:ℝ) (-residualGap),
    markedResidualField Pc P x ≤ (gapResidualM:ℝ) := by
  have he : -(residualGap:ℚ)=(-401/2500:ℚ) := by norm_num [residualGap]
  have hh := markedResidual_closed_sup_of_checks (a := -1) (b := -residualGap)
    (by norm_num) (by norm_num [residualGap])
    (by norm_num [residualGap]) tailsP hAQR hcoverRG0 hGapsRG0 hBracketsRG0
    hendRGLeft (by rw [he]; exact hendRGLeftGap)
  convert hh using 1 <;> norm_num [residualGap]

theorem residual_positive_gap : ∀ x ∈ Icc (residualGap:ℝ) 1,
    markedResidualField Pc P x ≤ (gapResidualM:ℝ) := by
  have hh := markedResidual_closed_sup_of_checks (a := residualGap) (b := 1)
    (by norm_num [residualGap])
    (by norm_num [residualGap]) (by norm_num) tailsP hAQR hcoverRG1 hGapsRG1 hBracketsRG1
    hendRGRightGap hendRGRight
  convert hh using 1 <;> norm_num [residualGap]

theorem residual_gap_sup : ∀ x ∈ Icc (-1:ℝ) 1,
    (residualGap:ℝ)≤|x| → markedResidualField Pc P x ≤ (gapResidualM:ℝ) := by
  intro x hx hg
  rcases (le_abs.mp hg) with hn | hp
  · exact residual_positive_gap x ⟨hn,hx.2⟩
  · exact residual_negative_gap x ⟨hx.1,by linarith only [hp]⟩

end CatalanMeasure.StrongTrial
