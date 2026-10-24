module
public import CatalanArchive.CatalanMeasure.StrongTrial.RootData
public import CatalanArchive.CatalanMeasure.StrongTrial.RootCoarseX0
public import CatalanArchive.CatalanMeasure.StrongTrial.RootCoarseX1
public import CatalanArchive.CatalanMeasure.StrongTrial.RootCoarseX2
public import CatalanArchive.CatalanMeasure.StrongTrial.RootCoarseX3
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX0
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX1
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX2
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX3
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX4
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX5
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX6
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX7
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX8
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX9
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX10
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX11
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX12
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX13
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX14
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX15
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX16
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX17
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX18
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsX19
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY0
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY1
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY2
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY3
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY4
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY5
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY6
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY7
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY8
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY9
public import CatalanArchive.CatalanMeasure.StrongTrial.RootSignsY10
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignsX0 : rootBracketsX0.all (RootBracket.signCheck AZX)=true := by
  simp only [rootBracketsX0,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨rootSignX0,rootSignX1,rootSignX2,rootSignX3,rootSignX4,rootSignX5,rootSignX6,rootSignX7,rootSignX8,rootSignX9,rootSignX10,rootSignX11,rootSignX12,rootSignX13,rootSignX14,rootSignX15,rootSignX16,rootSignX17,rootSignX18,rootSignX19,rootSignX20,rootSignX21,rootSignX22,rootSignX23,rootSignX24,rootSignX25,rootSignX26,rootSignX27,rootSignX28,rootSignX29,rootSignX30,rootSignX31,rootSignX32,rootSignX33,rootSignX34,rootSignX35,rootSignX36,rootSignX37,rootSignX38,rootSignX39,rootSignX40,rootSignX41,rootSignX42,rootSignX43,rootSignX44,rootSignX45,rootSignX46,rootSignX47,rootSignX48,rootSignX49,rootSignX50,rootSignX51,rootSignX52,rootSignX53,rootSignX54,rootSignX55,rootSignX56,rootSignX57,rootSignX58,True.intro⟩
theorem rootCoverageX0 : ∀ x ∈ Ioo ((-1 : ℚ) : ℝ) ((-1 / 2 : ℚ) : ℝ), ipEval AZX x=0 →
    ∃ q ∈ planX, q.2.2=true ∧ x ∈ Icc (q.1:ℝ) q.2.1 := by
  have hb : RootBudget (ipEval AZX) (-1 : ℚ) (-1 / 2 : ℚ) rootBracketsX0.length := rootBudgetX0
  have hh := root_coverage_rat_brackets rootCellX0 hb rootInsideX0 rootDisjointX0
    rootAlignedX0 (fun i => (List.all_eq_true.mp rootSignsX0) _ (List.get_mem _ _))
  intro x hx hz
  obtain ⟨i,hi⟩ := hh x hx hz
  exact ⟨((rootCellX0 i).lo,(rootCellX0 i).hi,true),rootMemberX0 i,rfl,hi⟩
theorem rootSignsX1 : rootBracketsX1.all (RootBracket.signCheck AZX)=true := by
  simp only [rootBracketsX1,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨rootSignX59,rootSignX60,rootSignX61,rootSignX62,rootSignX63,rootSignX64,rootSignX65,rootSignX66,rootSignX67,rootSignX68,rootSignX69,rootSignX70,rootSignX71,rootSignX72,rootSignX73,rootSignX74,rootSignX75,rootSignX76,rootSignX77,rootSignX78,rootSignX79,rootSignX80,True.intro⟩
theorem rootCoverageX1 : ∀ x ∈ Ioo ((-1 / 2 : ℚ) : ℝ) ((0 : ℚ) : ℝ), ipEval AZX x=0 →
    ∃ q ∈ planX, q.2.2=true ∧ x ∈ Icc (q.1:ℝ) q.2.1 := by
  have hb : RootBudget (ipEval AZX) (-1 / 2 : ℚ) (0 : ℚ) rootBracketsX1.length := rootBudgetX1
  have hh := root_coverage_rat_brackets rootCellX1 hb rootInsideX1 rootDisjointX1
    rootAlignedX1 (fun i => (List.all_eq_true.mp rootSignsX1) _ (List.get_mem _ _))
  intro x hx hz
  obtain ⟨i,hi⟩ := hh x hx hz
  exact ⟨((rootCellX1 i).lo,(rootCellX1 i).hi,true),rootMemberX1 i,rfl,hi⟩
theorem rootSignsX2 : rootBracketsX2.all (RootBracket.signCheck AZX)=true := by
  simp only [rootBracketsX2,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨rootSignX81,rootSignX82,rootSignX83,rootSignX84,rootSignX85,rootSignX86,rootSignX87,rootSignX88,rootSignX89,rootSignX90,rootSignX91,rootSignX92,rootSignX93,rootSignX94,rootSignX95,rootSignX96,rootSignX97,rootSignX98,rootSignX99,rootSignX100,rootSignX101,rootSignX102,rootSignX103,True.intro⟩
theorem rootCoverageX2 : ∀ x ∈ Ioo ((0 : ℚ) : ℝ) ((1 / 2 : ℚ) : ℝ), ipEval AZX x=0 →
    ∃ q ∈ planX, q.2.2=true ∧ x ∈ Icc (q.1:ℝ) q.2.1 := by
  have hb : RootBudget (ipEval AZX) (0 : ℚ) (1 / 2 : ℚ) rootBracketsX2.length := rootBudgetX2
  have hh := root_coverage_rat_brackets rootCellX2 hb rootInsideX2 rootDisjointX2
    rootAlignedX2 (fun i => (List.all_eq_true.mp rootSignsX2) _ (List.get_mem _ _))
  intro x hx hz
  obtain ⟨i,hi⟩ := hh x hx hz
  exact ⟨((rootCellX2 i).lo,(rootCellX2 i).hi,true),rootMemberX2 i,rfl,hi⟩
theorem rootSignsX3 : rootBracketsX3.all (RootBracket.signCheck AZX)=true := by
  simp only [rootBracketsX3,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨rootSignX104,rootSignX105,rootSignX106,rootSignX107,rootSignX108,rootSignX109,rootSignX110,rootSignX111,rootSignX112,rootSignX113,rootSignX114,rootSignX115,rootSignX116,rootSignX117,rootSignX118,rootSignX119,rootSignX120,rootSignX121,rootSignX122,rootSignX123,rootSignX124,rootSignX125,rootSignX126,rootSignX127,rootSignX128,rootSignX129,rootSignX130,rootSignX131,rootSignX132,rootSignX133,rootSignX134,rootSignX135,rootSignX136,rootSignX137,rootSignX138,rootSignX139,rootSignX140,rootSignX141,rootSignX142,rootSignX143,rootSignX144,rootSignX145,rootSignX146,rootSignX147,rootSignX148,rootSignX149,rootSignX150,rootSignX151,rootSignX152,rootSignX153,True.intro⟩
theorem rootCoverageX3 : ∀ x ∈ Ioo ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ), ipEval AZX x=0 →
    ∃ q ∈ planX, q.2.2=true ∧ x ∈ Icc (q.1:ℝ) q.2.1 := by
  have hb : RootBudget (ipEval AZX) (1 / 2 : ℚ) (1 : ℚ) rootBracketsX3.length := rootBudgetX3
  have hh := root_coverage_rat_brackets rootCellX3 hb rootInsideX3 rootDisjointX3
    rootAlignedX3 (fun i => (List.all_eq_true.mp rootSignsX3) _ (List.get_mem _ _))
  intro x hx hz
  obtain ⟨i,hi⟩ := hh x hx hz
  exact ⟨((rootCellX3 i).lo,(rootCellX3 i).hi,true),rootMemberX3 i,rfl,hi⟩
theorem rootSignsY : rootBracketsY.all (RootBracket.signCheck AZY)=true := by
  simp only [rootBracketsY,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨rootSignY0,rootSignY1,rootSignY2,rootSignY3,rootSignY4,rootSignY5,rootSignY6,rootSignY7,rootSignY8,rootSignY9,rootSignY10,rootSignY11,rootSignY12,rootSignY13,rootSignY14,rootSignY15,rootSignY16,rootSignY17,rootSignY18,rootSignY19,rootSignY20,rootSignY21,rootSignY22,rootSignY23,rootSignY24,rootSignY25,rootSignY26,rootSignY27,rootSignY28,rootSignY29,rootSignY30,rootSignY31,rootSignY32,rootSignY33,rootSignY34,rootSignY35,rootSignY36,rootSignY37,rootSignY38,rootSignY39,rootSignY40,rootSignY41,rootSignY42,rootSignY43,rootSignY44,rootSignY45,rootSignY46,rootSignY47,rootSignY48,rootSignY49,rootSignY50,rootSignY51,rootSignY52,rootSignY53,rootSignY54,rootSignY55,rootSignY56,rootSignY57,rootSignY58,rootSignY59,rootSignY60,rootSignY61,rootSignY62,rootSignY63,rootSignY64,rootSignY65,rootSignY66,rootSignY67,rootSignY68,rootSignY69,rootSignY70,rootSignY71,rootSignY72,rootSignY73,rootSignY74,rootSignY75,rootSignY76,rootSignY77,rootSignY78,rootSignY79,rootSignY80,rootSignY81,rootSignY82,rootSignY83,rootSignY84,rootSignY85,rootSignY86,True.intro⟩
theorem rootCoverageY : ∀ x ∈ Ioo ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ), ipEval AZY x=0 →
    ∃ q ∈ planY, q.2.2=true ∧ x ∈ Icc (q.1:ℝ) q.2.1 := by
  have hb : RootBudget (ipEval AZY) (0 : ℚ) (1 : ℚ) rootBracketsY.length := by
    convert coarseBudgetY using 1 <;> norm_num [rootBracketsY]
  have hh := root_coverage_rat_brackets rootCellY hb rootInsideY rootDisjointY
    rootAlignedY (fun i => (List.all_eq_true.mp rootSignsY) _ (List.get_mem _ _))
  intro x hx hz
  obtain ⟨i,hi⟩ := hh x hx hz
  exact ⟨((rootCellY i).lo,(rootCellY i).hi,true),rootMemberY i,rfl,hi⟩
theorem rootCoverageX : ∀ x ∈ Ioo (-1:ℝ) 1, x≠0 → ipEval AZX x=0 →
    ∃ q ∈ planX, q.2.2=true ∧ x ∈ Icc (q.1:ℝ) q.2.1 := by
  intro x hx hx0 hz
  by_cases hn : x<0
  · rcases lt_trichotomy x (-(1/2:ℝ)) with h|h|h
    · exact rootCoverageX0 x (by norm_num; exact ⟨hx.1,h⟩) hz
    · exact False.elim (rootMinusHalf_nonzero (h ▸ hz))
    · exact rootCoverageX1 x (by norm_num; exact ⟨h,hn⟩) hz
  · have hp : 0<x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx0)
    rcases lt_trichotomy x (1/2:ℝ) with h|h|h
    · exact rootCoverageX2 x (by norm_num; exact ⟨hp,h⟩) hz
    · exact False.elim (rootPlusHalf_nonzero (h ▸ hz))
    · exact rootCoverageX3 x (by norm_num; exact ⟨h,hx.2⟩) hz

theorem rootBudgetGapsX : NoRootGaps AX planX :=
  noRootGaps_of_root_coverage hScaleX hIntX rootDomainX rootSeparatedX (by
    intro x hx hn hz
    exact rootCoverageX x (by norm_num at hx; exact hx) (hn rfl) hz)

theorem rootBudgetGapsY : NoRootGaps AY planY :=
  noRootGaps_of_root_coverage hScaleY hIntY rootDomainY rootSeparatedY (by
    intro x hx _ hz
    exact rootCoverageY x hx hz)

end CatalanMeasure.StrongTrial
#print axioms CatalanMeasure.StrongTrial.rootBudgetGapsX
#print axioms CatalanMeasure.StrongTrial.rootBudgetGapsY
