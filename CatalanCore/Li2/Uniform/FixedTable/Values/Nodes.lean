module
public import CatalanCore.Li2.Uniform.FixedTable.LogCriterion
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Set
namespace CatalanCore.Li2.Uniform.FixedData
def magnitude0 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [2]).headD 0:ℚ)
def node0 : Node := ⟨magnitude0,.lattice⟩
theorem node0_checked : 0<node0.magnitude ∧ node0.magnitude<1 ∧ (node0.frame=.lattice ↔ 0<24) := by decide +kernel
def magnitude1 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [3]).headD 0:ℚ)
def node1 : Node := ⟨magnitude1,.lattice⟩
theorem node1_checked : 0<node1.magnitude ∧ node1.magnitude<1 ∧ (node1.frame=.lattice ↔ 1<24) := by decide +kernel
def magnitude2 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [4]).headD 0:ℚ)
def node2 : Node := ⟨magnitude2,.lattice⟩
theorem node2_checked : 0<node2.magnitude ∧ node2.magnitude<1 ∧ (node2.frame=.lattice ↔ 2<24) := by decide +kernel
def magnitude3 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [5]).headD 0:ℚ)
def node3 : Node := ⟨magnitude3,.lattice⟩
theorem node3_checked : 0<node3.magnitude ∧ node3.magnitude<1 ∧ (node3.frame=.lattice ↔ 3<24) := by decide +kernel
def magnitude4 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [6]).headD 0:ℚ)
def node4 : Node := ⟨magnitude4,.lattice⟩
theorem node4_checked : 0<node4.magnitude ∧ node4.magnitude<1 ∧ (node4.frame=.lattice ↔ 4<24) := by decide +kernel
def magnitude5 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [8]).headD 0:ℚ)
def node5 : Node := ⟨magnitude5,.lattice⟩
theorem node5_checked : 0<node5.magnitude ∧ node5.magnitude<1 ∧ (node5.frame=.lattice ↔ 5<24) := by decide +kernel
def magnitude6 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [15]).headD 0:ℚ)
def node6 : Node := ⟨magnitude6,.lattice⟩
theorem node6_checked : 0<node6.magnitude ∧ node6.magnitude<1 ∧ (node6.frame=.lattice ↔ 6<24) := by decide +kernel
def magnitude7 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [17]).headD 0:ℚ)
def node7 : Node := ⟨magnitude7,.lattice⟩
theorem node7_checked : 0<node7.magnitude ∧ node7.magnitude<1 ∧ (node7.frame=.lattice ↔ 7<24) := by decide +kernel
def magnitude8 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [13]).headD 0:ℚ)
def node8 : Node := ⟨magnitude8,.lattice⟩
theorem node8_checked : 0<node8.magnitude ∧ node8.magnitude<1 ∧ (node8.frame=.lattice ↔ 8<24) := by decide +kernel
def magnitude9 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [19]).headD 0:ℚ)
def node9 : Node := ⟨magnitude9,.lattice⟩
theorem node9_checked : 0<node9.magnitude ∧ node9.magnitude<1 ∧ (node9.frame=.lattice ↔ 9<24) := by decide +kernel
def magnitude10 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [23]).headD 0:ℚ)
def node10 : Node := ⟨magnitude10,.lattice⟩
theorem node10_checked : 0<node10.magnitude ∧ node10.magnitude<1 ∧ (node10.frame=.lattice ↔ 10<24) := by decide +kernel
def magnitude11 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [25]).headD 0:ℚ)
def node11 : Node := ⟨magnitude11,.lattice⟩
theorem node11_checked : 0<node11.magnitude ∧ node11.magnitude<1 ∧ (node11.frame=.lattice ↔ 11<24) := by decide +kernel
def magnitude12 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [33]).headD 0:ℚ)
def node12 : Node := ⟨magnitude12,.lattice⟩
theorem node12_checked : 0<node12.magnitude ∧ node12.magnitude<1 ∧ (node12.frame=.lattice ↔ 12<24) := by decide +kernel
def magnitude13 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [37]).headD 0:ℚ)
def node13 : Node := ⟨magnitude13,.lattice⟩
theorem node13_checked : 0<node13.magnitude ∧ node13.magnitude<1 ∧ (node13.frame=.lattice ↔ 13<24) := by decide +kernel
def magnitude14 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [39]).headD 0:ℚ)
def node14 : Node := ⟨magnitude14,.lattice⟩
theorem node14_checked : 0<node14.magnitude ∧ node14.magnitude<1 ∧ (node14.frame=.lattice ↔ 14<24) := by decide +kernel
def magnitude15 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [10]).headD 0:ℚ)
def node15 : Node := ⟨magnitude15,.lattice⟩
theorem node15_checked : 0<node15.magnitude ∧ node15.magnitude<1 ∧ (node15.frame=.lattice ↔ 15<24) := by decide +kernel
def magnitude16 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [148]).headD 0:ℚ)
def node16 : Node := ⟨magnitude16,.lattice⟩
theorem node16_checked : 0<node16.magnitude ∧ node16.magnitude<1 ∧ (node16.frame=.lattice ↔ 16<24) := by decide +kernel
def magnitude17 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [14]).headD 0:ℚ)
def node17 : Node := ⟨magnitude17,.lattice⟩
theorem node17_checked : 0<node17.magnitude ∧ node17.magnitude<1 ∧ (node17.frame=.lattice ↔ 17<24) := by decide +kernel
def magnitude18 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [20]).headD 0:ℚ)
def node18 : Node := ⟨magnitude18,.lattice⟩
theorem node18_checked : 0<node18.magnitude ∧ node18.magnitude<1 ∧ (node18.frame=.lattice ↔ 18<24) := by decide +kernel
def magnitude19 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [26]).headD 0:ℚ)
def node19 : Node := ⟨magnitude19,.lattice⟩
theorem node19_checked : 0<node19.magnitude ∧ node19.magnitude<1 ∧ (node19.frame=.lattice ↔ 19<24) := by decide +kernel
def magnitude20 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [33]).headD 0:ℚ)
def node20 : Node := ⟨magnitude20,.lattice⟩
theorem node20_checked : 0<node20.magnitude ∧ node20.magnitude<1 ∧ (node20.frame=.lattice ↔ 20<24) := by decide +kernel
def magnitude21 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [403]).headD 0:ℚ)
def node21 : Node := ⟨magnitude21,.lattice⟩
theorem node21_checked : 0<node21.magnitude ∧ node21.magnitude<1 ∧ (node21.frame=.lattice ↔ 21<24) := by decide +kernel
def magnitude22 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [55]).headD 0:ℚ)
def node22 : Node := ⟨magnitude22,.lattice⟩
theorem node22_checked : 0<node22.magnitude ∧ node22.magnitude<1 ∧ (node22.frame=.lattice ↔ 22<24) := by decide +kernel
def magnitude23 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [90]).headD 0:ℚ)
def node23 : Node := ⟨magnitude23,.lattice⟩
theorem node23_checked : 0<node23.magnitude ∧ node23.magnitude<1 ∧ (node23.frame=.lattice ↔ 23<24) := by decide +kernel
def magnitude24 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [2]).headD 0:ℚ)
def node24 : Node := ⟨magnitude24,.G2⟩
theorem node24_checked : 0<node24.magnitude ∧ node24.magnitude<1 ∧ (node24.frame=.lattice ↔ 24<24) := by decide +kernel
def magnitude25 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [3]).headD 0:ℚ)
def node25 : Node := ⟨magnitude25,.G3⟩
theorem node25_checked : 0<node25.magnitude ∧ node25.magnitude<1 ∧ (node25.frame=.lattice ↔ 25<24) := by decide +kernel
def magnitude26 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [4]).headD 0:ℚ)
def node26 : Node := ⟨magnitude26,.G4⟩
theorem node26_checked : 0<node26.magnitude ∧ node26.magnitude<1 ∧ (node26.frame=.lattice ↔ 26<24) := by decide +kernel
def magnitude27 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [13]).headD 0:ℚ)
def node27 : Node := ⟨magnitude27,.G15⟩
theorem node27_checked : 0<node27.magnitude ∧ node27.magnitude<1 ∧ (node27.frame=.lattice ↔ 27<24) := by decide +kernel
def magnitude28 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [20]).headD 0:ℚ)
def node28 : Node := ⟨magnitude28,.G15⟩
theorem node28_checked : 0<node28.magnitude ∧ node28.magnitude<1 ∧ (node28.frame=.lattice ↔ 28<24) := by decide +kernel
def magnitude29 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [33]).headD 0:ℚ)
def node29 : Node := ⟨magnitude29,.G15⟩
theorem node29_checked : 0<node29.magnitude ∧ node29.magnitude<1 ∧ (node29.frame=.lattice ↔ 29<24) := by decide +kernel
def magnitude30 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [6]).headD 0:ℚ)
def node30 : Node := ⟨magnitude30,.G15⟩
theorem node30_checked : 0<node30.magnitude ∧ node30.magnitude<1 ∧ (node30.frame=.lattice ↔ 30<24) := by decide +kernel
def magnitude31 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [11]).headD 0:ℚ)
def node31 : Node := ⟨magnitude31,.G15⟩
theorem node31_checked : 0<node31.magnitude ∧ node31.magnitude<1 ∧ (node31.frame=.lattice ↔ 31<24) := by decide +kernel
def magnitude32 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [15]).headD 0:ℚ)
def node32 : Node := ⟨magnitude32,.G15⟩
theorem node32_checked : 0<node32.magnitude ∧ node32.magnitude<1 ∧ (node32.frame=.lattice ↔ 32<24) := by decide +kernel
def magnitude33 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [25]).headD 0:ℚ)
def node33 : Node := ⟨magnitude33,.G15⟩
theorem node33_checked : 0<node33.magnitude ∧ node33.magnitude<1 ∧ (node33.frame=.lattice ↔ 33<24) := by decide +kernel
def magnitude34 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [41]).headD 0:ℚ)
def node34 : Node := ⟨magnitude34,.G15⟩
theorem node34_checked : 0<node34.magnitude ∧ node34.magnitude<1 ∧ (node34.frame=.lattice ↔ 34<24) := by decide +kernel
def magnitude35 : ℚ := ((raw_ints% [2]).headD 0:ℚ)/((raw_ints% [65]).headD 0:ℚ)
def node35 : Node := ⟨magnitude35,.G15⟩
theorem node35_checked : 0<node35.magnitude ∧ node35.magnitude<1 ∧ (node35.frame=.lattice ↔ 35<24) := by decide +kernel
def magnitude36 : ℚ := ((raw_ints% [1]).headD 0:ℚ)/((raw_ints% [5]).headD 0:ℚ)
def node36 : Node := ⟨magnitude36,.G4⟩
theorem node36_checked : 0<node36.magnitude ∧ node36.magnitude<1 ∧ (node36.frame=.lattice ↔ 36<24) := by decide +kernel
def nodeValues : List Node := [node0,node1,node2,node3,node4,node5,node6,node7,node8,node9,node10,node11,node12,node13,node14,node15,node16,node17,node18,node19,node20,node21,node22,node23,node24,node25,node26,node27,node28,node29,node30,node31,node32,node33,node34,node35,node36]
theorem nodeValues_length : nodeValues.length=37 := by rfl
def fixedNodes (i : Fin 37) : Node := nodeValues[i.val]'(by rw [nodeValues_length]; exact i.isLt)
theorem fixedNodes_positive (i : Fin 37) : 0<(fixedNodes i).magnitude := by
  fin_cases i
  · exact node0_checked.1
  · exact node1_checked.1
  · exact node2_checked.1
  · exact node3_checked.1
  · exact node4_checked.1
  · exact node5_checked.1
  · exact node6_checked.1
  · exact node7_checked.1
  · exact node8_checked.1
  · exact node9_checked.1
  · exact node10_checked.1
  · exact node11_checked.1
  · exact node12_checked.1
  · exact node13_checked.1
  · exact node14_checked.1
  · exact node15_checked.1
  · exact node16_checked.1
  · exact node17_checked.1
  · exact node18_checked.1
  · exact node19_checked.1
  · exact node20_checked.1
  · exact node21_checked.1
  · exact node22_checked.1
  · exact node23_checked.1
  · exact node24_checked.1
  · exact node25_checked.1
  · exact node26_checked.1
  · exact node27_checked.1
  · exact node28_checked.1
  · exact node29_checked.1
  · exact node30_checked.1
  · exact node31_checked.1
  · exact node32_checked.1
  · exact node33_checked.1
  · exact node34_checked.1
  · exact node35_checked.1
  · exact node36_checked.1
theorem fixedNodes_lt_one (i : Fin 37) : (fixedNodes i).magnitude<1 := by
  fin_cases i
  · exact node0_checked.2.1
  · exact node1_checked.2.1
  · exact node2_checked.2.1
  · exact node3_checked.2.1
  · exact node4_checked.2.1
  · exact node5_checked.2.1
  · exact node6_checked.2.1
  · exact node7_checked.2.1
  · exact node8_checked.2.1
  · exact node9_checked.2.1
  · exact node10_checked.2.1
  · exact node11_checked.2.1
  · exact node12_checked.2.1
  · exact node13_checked.2.1
  · exact node14_checked.2.1
  · exact node15_checked.2.1
  · exact node16_checked.2.1
  · exact node17_checked.2.1
  · exact node18_checked.2.1
  · exact node19_checked.2.1
  · exact node20_checked.2.1
  · exact node21_checked.2.1
  · exact node22_checked.2.1
  · exact node23_checked.2.1
  · exact node24_checked.2.1
  · exact node25_checked.2.1
  · exact node26_checked.2.1
  · exact node27_checked.2.1
  · exact node28_checked.2.1
  · exact node29_checked.2.1
  · exact node30_checked.2.1
  · exact node31_checked.2.1
  · exact node32_checked.2.1
  · exact node33_checked.2.1
  · exact node34_checked.2.1
  · exact node35_checked.2.1
  · exact node36_checked.2.1
theorem fixedNodes_lattice_iff (i : Fin 37) : ((fixedNodes i).frame=.lattice ↔ i.val<24) := by
  fin_cases i
  · exact node0_checked.2.2
  · exact node1_checked.2.2
  · exact node2_checked.2.2
  · exact node3_checked.2.2
  · exact node4_checked.2.2
  · exact node5_checked.2.2
  · exact node6_checked.2.2
  · exact node7_checked.2.2
  · exact node8_checked.2.2
  · exact node9_checked.2.2
  · exact node10_checked.2.2
  · exact node11_checked.2.2
  · exact node12_checked.2.2
  · exact node13_checked.2.2
  · exact node14_checked.2.2
  · exact node15_checked.2.2
  · exact node16_checked.2.2
  · exact node17_checked.2.2
  · exact node18_checked.2.2
  · exact node19_checked.2.2
  · exact node20_checked.2.2
  · exact node21_checked.2.2
  · exact node22_checked.2.2
  · exact node23_checked.2.2
  · exact node24_checked.2.2
  · exact node25_checked.2.2
  · exact node26_checked.2.2
  · exact node27_checked.2.2
  · exact node28_checked.2.2
  · exact node29_checked.2.2
  · exact node30_checked.2.2
  · exact node31_checked.2.2
  · exact node32_checked.2.2
  · exact node33_checked.2.2
  · exact node34_checked.2.2
  · exact node35_checked.2.2
  · exact node36_checked.2.2
theorem node0_gap (j : Fin 37) : node0.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node0.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node1_gap (j : Fin 37) : node1.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node1.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node2_gap (j : Fin 37) : node2.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node2.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node3_gap (j : Fin 37) : node3.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node3.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node4_gap (j : Fin 37) : node4.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node4.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node5_gap (j : Fin 37) : node5.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node5.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node6_gap (j : Fin 37) : node6.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node6.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node7_gap (j : Fin 37) : node7.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node7.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node8_gap (j : Fin 37) : node8.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node8.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node9_gap (j : Fin 37) : node9.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node9.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node10_gap (j : Fin 37) : node10.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node10.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node11_gap (j : Fin 37) : node11.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node11.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node12_gap (j : Fin 37) : node12.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node12.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node13_gap (j : Fin 37) : node13.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node13.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node14_gap (j : Fin 37) : node14.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node14.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node15_gap (j : Fin 37) : node15.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node15.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node16_gap (j : Fin 37) : node16.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node16.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node17_gap (j : Fin 37) : node17.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node17.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node18_gap (j : Fin 37) : node18.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node18.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node19_gap (j : Fin 37) : node19.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node19.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node20_gap (j : Fin 37) : node20.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node20.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node21_gap (j : Fin 37) : node21.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node21.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node22_gap (j : Fin 37) : node22.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node22.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node23_gap (j : Fin 37) : node23.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node23.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node24_gap (j : Fin 37) : node24.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node24.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node25_gap (j : Fin 37) : node25.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node25.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node26_gap (j : Fin 37) : node26.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node26.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node27_gap (j : Fin 37) : node27.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node27.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node28_gap (j : Fin 37) : node28.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node28.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node29_gap (j : Fin 37) : node29.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node29.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node30_gap (j : Fin 37) : node30.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node30.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node31_gap (j : Fin 37) : node31.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node31.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node32_gap (j : Fin 37) : node32.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node32.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node33_gap (j : Fin 37) : node33.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node33.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node34_gap (j : Fin 37) : node34.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node34.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node35_gap (j : Fin 37) : node35.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node35.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem node36_gap (j : Fin 37) : node36.magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤node36.magnitude/(fixedNodes j).magnitude := by
  fin_cases j <;> decide +kernel
theorem fixedNodes_gap (i j : Fin 37) : (fixedNodes i).magnitude/(fixedNodes j).magnitude≤logGapLow ∨ logGapHigh≤(fixedNodes i).magnitude/(fixedNodes j).magnitude := by
  fin_cases i
  · exact node0_gap j
  · exact node1_gap j
  · exact node2_gap j
  · exact node3_gap j
  · exact node4_gap j
  · exact node5_gap j
  · exact node6_gap j
  · exact node7_gap j
  · exact node8_gap j
  · exact node9_gap j
  · exact node10_gap j
  · exact node11_gap j
  · exact node12_gap j
  · exact node13_gap j
  · exact node14_gap j
  · exact node15_gap j
  · exact node16_gap j
  · exact node17_gap j
  · exact node18_gap j
  · exact node19_gap j
  · exact node20_gap j
  · exact node21_gap j
  · exact node22_gap j
  · exact node23_gap j
  · exact node24_gap j
  · exact node25_gap j
  · exact node26_gap j
  · exact node27_gap j
  · exact node28_gap j
  · exact node29_gap j
  · exact node30_gap j
  · exact node31_gap j
  · exact node32_gap j
  · exact node33_gap j
  · exact node34_gap j
  · exact node35_gap j
  · exact node36_gap j
#print axioms fixedNodes_positive
#print axioms fixedNodes_gap
end CatalanCore.Li2.Uniform.FixedData
