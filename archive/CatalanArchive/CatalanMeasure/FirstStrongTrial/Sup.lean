module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Norms
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX0
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX2
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX3
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX4
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX5
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX6
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX7
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX8
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX9
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX11
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX13
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX15
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX17
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX19
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX21
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX23
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX24
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX26
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX28
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX30
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX32
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX34
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX36
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX38
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX40
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX42
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX44
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX46
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX48
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsX50
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesX0
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesX1
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesX2
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesX3
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesX4
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY0
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY2
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY4
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY6
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY8
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY10
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY12
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY14
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY16
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY18
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY20
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY22
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY24
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY26
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY28
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY30
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY32
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY34
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY36
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY38
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY40
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY42
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY44
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.GapsY46
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesY0
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesY1
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesY2
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesY3
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.ValuesY4
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem hGapsX : NoRootGaps AX planX := by
  simp only [planX,noRootGaps_cons,noRootGaps_nil]
  exact ⟨gapX_0,(by intro h; cases h),gapX_2,gapX_3,gapX_4,gapX_5,gapX_6,gapX_7,gapX_8,gapX_9,(by intro h; cases h),gapX_11,(by intro h; cases h),gapX_13,(by intro h; cases h),gapX_15,(by intro h; cases h),gapX_17,(by intro h; cases h),gapX_19,(by intro h; cases h),gapX_21,(by intro h; cases h),gapX_23,gapX_24,(by intro h; cases h),gapX_26,(by intro h; cases h),gapX_28,(by intro h; cases h),gapX_30,(by intro h; cases h),gapX_32,(by intro h; cases h),gapX_34,(by intro h; cases h),gapX_36,(by intro h; cases h),gapX_38,(by intro h; cases h),gapX_40,(by intro h; cases h),gapX_42,(by intro h; cases h),gapX_44,(by intro h; cases h),gapX_46,(by intro h; cases h),gapX_48,(by intro h; cases h),gapX_50,True.intro⟩
theorem hBracketsX : planX.all (shiftedRowBracketOK R Pc Vc P V AX QX MX)=true := by
  simp only [planX,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨(by decide +kernel),bracketX_1,(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),bracketX_10,(by decide +kernel),bracketX_12,(by decide +kernel),bracketX_14,(by decide +kernel),bracketX_16,(by decide +kernel),bracketX_18,(by decide +kernel),bracketX_20,(by decide +kernel),bracketX_22,(by decide +kernel),(by decide +kernel),bracketX_25,(by decide +kernel),bracketX_27,(by decide +kernel),bracketX_29,(by decide +kernel),bracketX_31,(by decide +kernel),bracketX_33,(by decide +kernel),bracketX_35,(by decide +kernel),bracketX_37,(by decide +kernel),bracketX_39,(by decide +kernel),bracketX_41,(by decide +kernel),bracketX_43,(by decide +kernel),bracketX_45,(by decide +kernel),bracketX_47,(by decide +kernel),bracketX_49,(by decide +kernel),True.intro⟩
theorem hGapsY : NoRootGaps AY planY := by
  simp only [planY,noRootGaps_cons,noRootGaps_nil]
  exact ⟨gapY_0,(by intro h; cases h),gapY_2,(by intro h; cases h),gapY_4,(by intro h; cases h),gapY_6,(by intro h; cases h),gapY_8,(by intro h; cases h),gapY_10,(by intro h; cases h),gapY_12,(by intro h; cases h),gapY_14,(by intro h; cases h),gapY_16,(by intro h; cases h),gapY_18,(by intro h; cases h),gapY_20,(by intro h; cases h),gapY_22,(by intro h; cases h),gapY_24,(by intro h; cases h),gapY_26,(by intro h; cases h),gapY_28,(by intro h; cases h),gapY_30,(by intro h; cases h),gapY_32,(by intro h; cases h),gapY_34,(by intro h; cases h),gapY_36,(by intro h; cases h),gapY_38,(by intro h; cases h),gapY_40,(by intro h; cases h),gapY_42,(by intro h; cases h),gapY_44,(by intro h; cases h),gapY_46,True.intro⟩
theorem hBracketsY : planY.all (shiftedColumnBracketOK C Vc V AY QY MY)=true := by
  simp only [planY,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨(by decide +kernel),bracketY_1,(by decide +kernel),bracketY_3,(by decide +kernel),bracketY_5,(by decide +kernel),bracketY_7,(by decide +kernel),bracketY_9,(by decide +kernel),bracketY_11,(by decide +kernel),bracketY_13,(by decide +kernel),bracketY_15,(by decide +kernel),bracketY_17,(by decide +kernel),bracketY_19,(by decide +kernel),bracketY_21,(by decide +kernel),bracketY_23,(by decide +kernel),bracketY_25,(by decide +kernel),bracketY_27,(by decide +kernel),bracketY_29,(by decide +kernel),bracketY_31,(by decide +kernel),bracketY_33,(by decide +kernel),bracketY_35,(by decide +kernel),bracketY_37,(by decide +kernel),bracketY_39,(by decide +kernel),bracketY_41,(by decide +kernel),bracketY_43,(by decide +kernel),bracketY_45,(by decide +kernel),True.intro⟩

theorem row_sup : ∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
    shiftedRowField R Pc Vc P V x ≤ (MX:ℝ) :=
  shiftedRowCheck_spec (by norm_num [R]) (by norm_num [R]) hAQX hchainX
    hGapsX hBracketsX hendX

theorem column_sup : ∀ s ∈ Ioo (0:ℝ) 1,
    shiftedColumnField C Vc V s ≤ (MY:ℝ) :=
  shiftedColumnCheck_spec (by norm_num [C]) (by norm_num [C]) hAQY hchainY
    hGapsY hBracketsY

end CatalanMeasure.FirstStrongTrial
